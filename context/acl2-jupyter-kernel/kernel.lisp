;;;; ACL2 Jupyter Kernel - Kernel Class
;;;;
;;;; Architecture:
;;;;
;;;;   Shell thread (Jupyter): owns *kernel*, IOPub socket, protocol.
;;;;   Main thread (ACL2):     owns 128MB stack, ACL2 state, output channels.
;;;;
;;;; evaluate-code runs on the shell thread.  It dispatches ACL2 work
;;;; to the main thread via in-main-thread, which blocks until done.
;;;;
;;;; The main thread lives inside a PERSISTENT LP context set up once
;;;; by start.  This means *ld-level* stays at 1, the unwind-protect
;;;; stack persists, and command history accumulates across cells --
;;;; just like a normal ACL2 session.
;;;;
;;;; ALL user code is evaluated through ACL2's trans-eval, giving us:
;;;;   - Structured (stobjs-out . replaced-val) results   (not stdout)
;;;;   - ACL2's own reader (via read-object on a channel)
;;;;   - Full event processing, command landmarks, world updates
;;;;
;;;; No sbcl-restart, no LD, no set-raw-mode-on!.  We set up LP
;;;; scaffolding directly and call trans-eval ourselves.
;;;;
;;;; Proof/event output streams to Jupyter stdout via ACL2 channels.
;;;; Per-form result values are sent as Jupyter execute_result messages.
;;;;
;;;; in-main-thread forwards *standard-output* (Jupyter's IOPub stream)
;;;; and *kernel* to the main thread so both CL output and Jupyter calls
;;;; work there.

(in-package #:acl2-jupyter)

;;; ---------------------------------------------------------------------------
;;; Main Thread Dispatch
;;; ---------------------------------------------------------------------------

(defvar *initial-world-baseline* nil
  "World baseline set by start, picked up by the kernel instance.
   NIL means full-world mode (first cell gets entire world).
   A world value means diff-only mode.")

(defvar *main-thread-lock* (bordeaux-threads:make-lock "acl2-jupyter-main-thread-lock"))
(defvar *main-thread-work* nil)
(defvar *main-thread-ready* (bt-semaphore:make-semaphore))
(defvar *kernel-shutdown* nil)

(defun main-thread-loop ()
  "Block the main thread, executing work dispatched from the Shell thread."
  (loop until *kernel-shutdown* do
        (bt-semaphore:wait-on-semaphore *main-thread-ready*)
        (unless *kernel-shutdown*
          (let ((work *main-thread-work*))
            (setq *main-thread-work* nil)
            (when work (funcall work))))))

(defmacro in-main-thread (&body forms)
  "Execute FORMS on the main thread.  Blocks until done.
   Forwards all Jupyter shell-thread specials (*kernel*, *stdout*, *stderr*,
   *stdin*, *message*, *thread-id*, *html-output*, *markdown-output*)
   so that Jupyter protocol calls (execute-result, stream output, etc.)
   work correctly on the main thread."
  ;; Modeled directly on Bridge's in-main-thread-aux.
  ;; Assumes caller holds *main-thread-lock*.
  (let ((done     (gensym "DONE"))
        (retvals  (gensym "RETVALS"))
        (errval   (gensym "ERRVAL"))
        (finished (gensym "FINISHED"))
        (saved-stdout  (gensym "SAVED-STDOUT"))
        (saved-stderr  (gensym "SAVED-STDERR"))
        (saved-stdin   (gensym "SAVED-STDIN"))
        (saved-kernel  (gensym "SAVED-KERNEL"))
        (saved-message (gensym "SAVED-MESSAGE"))
        (saved-thread  (gensym "SAVED-THREAD"))
        (saved-html    (gensym "SAVED-HTML"))
        (saved-md      (gensym "SAVED-MD"))
        (work          (gensym "WORK")))
    `(bordeaux-threads:with-lock-held (*main-thread-lock*)
       (let* ((,done     (bt-semaphore:make-semaphore))
              (,retvals  nil)
              (,finished nil)
              (,errval   nil)
              ;; Capture all Jupyter shell-thread specials
              (,saved-stdout  jupyter::*stdout*)
              (,saved-stderr  jupyter::*stderr*)
              (,saved-stdin   jupyter::*stdin*)
              (,saved-kernel  jupyter:*kernel*)
              (,saved-message jupyter::*message*)
              (,saved-thread  jupyter:*thread-id*)
              (,saved-html    jupyter:*html-output*)
              (,saved-md      jupyter:*markdown-output*)
              (,work
               (lambda ()
                 ;; Rebind ALL Jupyter specials on the main thread
                 (let ((jupyter::*stdout*          ,saved-stdout)
                       (jupyter::*stderr*          ,saved-stderr)
                       (jupyter::*stdin*           ,saved-stdin)
                       (jupyter:*kernel*          ,saved-kernel)
                       (jupyter::*message*        ,saved-message)
                       (jupyter:*thread-id*       ,saved-thread)
                       (jupyter:*html-output*     ,saved-html)
                       (jupyter:*markdown-output* ,saved-md)
                       ;; Rebuild CL streams same as run-shell does
                       (*standard-input*  (make-synonym-stream 'jupyter::*stdin*))
                       (*standard-output* (make-synonym-stream 'jupyter::*stdout*))
                       (*error-output*    (make-synonym-stream 'jupyter::*stderr*))
                       (*trace-output*    (make-synonym-stream 'jupyter::*stdout*)))
                   (let ((*debug-io*    (make-two-way-stream *standard-input* *standard-output*))
                         (*query-io*    (make-two-way-stream *standard-input* *standard-output*))
                         (*terminal-io* (make-two-way-stream *standard-input* *standard-output*)))
                     ;; Same block/unwind-protect/handler-case structure as
                     ;; Bridge's in-main-thread-aux: THROWs get past
                     ;; handler-case but not past unwind-protect.
                     (block main-thread-work
                       (unwind-protect
                           (handler-case
                             (progn
                               (setq ,retvals (multiple-value-list (progn ,@forms)))
                               (setq ,finished t))
                             (error (condition)
                               (setq ,errval condition)
                               (setq ,finished t)))
                         ;; Non-local exit (ACL2 throw) -- same as Bridge:
                         ;; set errval so caller sees the error.
                         (unless ,finished
                           (setq ,errval
                                 (make-condition
                                  'simple-error
                                  :format-control "Unexpected non-local exit.")))
                         (return-from main-thread-work nil)))
                     ;; Signal AFTER the block -- same position as Bridge.
                     ;; This runs whether we exited normally or via
                     ;; return-from (non-local exit / error).
                     (bt-semaphore:signal-semaphore ,done))))))
         (setq *main-thread-work* ,work)
         (bt-semaphore:signal-semaphore *main-thread-ready*)
         (bt-semaphore:wait-on-semaphore ,done)
         (when ,errval (error ,errval))
         (values-list ,retvals)))))

;;; ---------------------------------------------------------------------------
;;; ACL2 Output Routing (same macros as Bridge)
;;; ---------------------------------------------------------------------------

(defmacro with-acl2-channels-bound (channel &body forms)
  "Bind ACL2 state globals (proofs-co, standard-co, trace-co) to CHANNEL."
  `(progv
       (list (global-symbol 'acl2::proofs-co)
             (global-symbol 'acl2::standard-co)
             (global-symbol 'acl2::trace-co))
       (list ,channel ,channel ,channel)
     (progn ,@forms)))

(defmacro with-acl2-output-to (stream &body forms)
  "Redirect all ACL2 output channels AND CL streams to STREAM."
  (let ((channel (gensym "CHANNEL")))
    `(let* ((,channel (gensym "ACL2-JUPYTER-OUT")))
       (setf (get ,channel *open-output-channel-type-key*) :character)
       (setf (get ,channel *open-output-channel-key*) ,stream)
       (unwind-protect
           (let ((*standard-output* ,stream)
                 (*trace-output*    ,stream)
                 (*debug-io*        (make-two-way-stream *standard-input* ,stream))
                 (*error-output*    ,stream)
                 (*standard-co*     ,channel))
             (with-acl2-channels-bound ,channel ,@forms))
         (setf (get ,channel *open-output-channel-key*) nil)
         (setf (get ,channel *open-output-channel-type-key*) nil)))))

;;; ---------------------------------------------------------------------------
;;; Kernel Class
;;; ---------------------------------------------------------------------------

(defclass kernel (jupyter:kernel)
  ((cell-events     :initform #() :accessor cell-events)
   (cell-package    :initform "ACL2" :accessor cell-package)
   (world-baseline  :initform *initial-world-baseline*
                    :accessor world-baseline
                    :documentation "Previous world state for event diff.
   Set from *initial-world-baseline* when the kernel is instantiated.
   NIL = full-world mode (first cell gets entire world).
   A world = diff-only (first cell gets only its own additions)."))
  (:default-initargs
    :name "acl2"
    :package (find-package "ACL2")
    :version "0.1.0"
    :banner (format nil "ACL2 Jupyter Kernel v0.1.0~%~A"
                    (f-get-global 'acl2::acl2-version
                                  *the-live-state*))
    :language-name "acl2"
    :language-version (f-get-global 'acl2::acl2-version
                                    *the-live-state*)
    :mime-type "text/x-common-lisp"
    :file-extension ".lisp"
    :pygments-lexer "common-lisp"
    :codemirror-mode "text/x-common-lisp"
    :help-links '(("ACL2 Documentation" . "https://www.cs.utexas.edu/~moore/acl2/")
                  ("ACL2 Manual" . "https://www.cs.utexas.edu/~moore/acl2/current/manual/")
                  ("ACL2 Community Books" . "https://www.cs.utexas.edu/~moore/acl2/current/combined-manual/"))))


;;; ---------------------------------------------------------------------------
;;; ACL2 Channel from String Stream
;;; ---------------------------------------------------------------------------
;;; Create a temporary ACL2 :object input channel backed by a CL string
;;; stream.  This lets ACL2's own reader (read-object) handle all reader
;;; macros, package prefixes, keyword commands, etc.

(defun make-string-input-channel (string)
  "Create an ACL2 :object input channel reading from STRING.
   Returns the channel symbol.  Caller must call close-string-input-channel
   when done."
  (let ((channel (gensym "JUPYTER-INPUT")))
    (setf (get channel *open-input-channel-type-key*) :object)
    (setf (get channel *open-input-channel-key*)
          (make-string-input-stream string))
    channel))

(defun close-string-input-channel (channel)
  "Close a channel created by make-string-input-channel."
  (let ((stream (get channel *open-input-channel-key*)))
    (when stream (close stream)))
  (setf (get channel *open-input-channel-key*) nil)
  (setf (get channel *open-input-channel-type-key*) nil))


;;; ---------------------------------------------------------------------------
;;; Keyword Command Expansion
;;; ---------------------------------------------------------------------------
;;; ACL2's LD supports keyword commands:
;;;   :pe foo  =>  (ACL2::PE 'FOO)
;;;   :ubt bar =>  (ACL2::UBT 'BAR)
;;;
;;; We replicate the logic from ld-read-keyword-command (ld.lisp:820):
;;; intern keyword name in "ACL2", look up arity, read N more forms,
;;; quote them, build (SYM 'arg1 'arg2 ...).
;;;
;;; :q exits the kernel process (Jupyter client handles restart).

(defun keyword-command-arity (sym state)
  "Return the number of arguments for keyword command SYM, or NIL if
   SYM is not a known function/macro."
  (let ((wrld (w state)))
    (cond ((function-symbolp sym wrld)
           (length (formals sym wrld)))
          ((getpropc sym 'acl2::macro-body nil wrld)
           (macro-minimal-arity sym nil wrld))
          (t nil))))

(defun expand-keyword-command (key channel state)
  "Expand keyword KEY into a full form, reading additional arguments
   from CHANNEL.  Returns the expanded form ready for trans-eval.
   Signals an error for unrecognized keywords."
  (cond
    ((eq key :q)
     ;; Exit immediately.  :abort t avoids deadlock with the Jupyter
     ;; shell thread (which is blocked waiting on in-main-thread).
     (sb-ext:exit :code 0 :abort t))
    (t
     (let* ((sym (intern (symbol-name key) "ACL2"))
            (len (keyword-command-arity sym state)))
       (cond
         (len
          (let ((args (loop repeat len
                            collect (multiple-value-bind (eofp obj state)
                                        (acl2::read-object channel state)
                                      (when eofp
                                        (error "Unfinished keyword command ~S"
                                               key))
                                      (list 'quote obj)))))
            (cons sym args)))
         (t
          (error "Unrecognized keyword command ~S" key)))))))


;;; ---------------------------------------------------------------------------
;;; Read-Eval-Print Loop (runs inside persistent LP context from start)
;;; ---------------------------------------------------------------------------
;;; trans-eval returns (mv erp (stobjs-out . replaced-val) state).
;;;   - erp non-nil means error (already printed to channels)
;;;   - stobjs-out = (NIL NIL STATE) for error triples (most events)
;;;   - For error triples: replaced-val = (erp-flag val state-symbol)
;;;     We display val via execute_result unless it's :invisible.
;;;   - For non-triples: replaced-val is the value(s) directly.

(defun jupyter-read-eval-print-loop (channel state)
  "Read forms from CHANNEL, evaluate each via trans-eval, send results
   to Jupyter.  Runs inside the persistent LP context set up by start.
   catch 'local-top-level is per-cell so a throw aborts the rest of
   the cell but not the kernel."
  (let ((*readtable* acl2::*acl2-readtable*))
    (catch 'acl2::local-top-level
      (loop
        ;; Clean up any pending acl2-unwind-protect forms from previous
        ;; command, same as ld-loop does at the top of each iteration.
        (acl2::acl2-unwind acl2::*ld-level* t)
        (multiple-value-bind (eofp raw-form state)
            (acl2::read-object channel state)
          (when eofp (return))
          ;; Keyword commands:  :pe foo => (ACL2::PE 'FOO)
          ;; String commands:   "ACL2S" => (IN-PACKAGE "ACL2S")
          (let ((form (cond
                        ((keywordp raw-form)
                         (expand-keyword-command
                          raw-form channel state))
                        ((stringp raw-form)
                         (list 'acl2::in-package raw-form))
                        (t raw-form))))
            ;; Save world state before eval -- needed for command landmarks.
            ;; This mirrors ld-fn0 which saves old-wrld and
            ;; old-default-defun-mode before calling trans-eval.
            (let* ((old-wrld (w state))
                   (old-default-defun-mode (default-defun-mode old-wrld)))
              (initialize-accumulated-warnings)
              (f-put-global 'acl2::last-make-event-expansion nil state)
              ;; Evaluate via trans-eval -- full ACL2 event processing
              (multiple-value-bind (erp trans-ans state)
                  (acl2::trans-eval-default-warning
                   form 'acl2-jupyter state t)
                (cond
                  (erp nil)
                  (t
                   ;; Add command landmark if the world was extended.
                   ;; This is what makes :pbt, :pe, :ubt etc. work.
                   (multiple-value-bind (lm-erp lm-val state)
                       (maybe-add-command-landmark
                        old-wrld old-default-defun-mode
                        form trans-ans state)
                     (declare (ignore lm-erp lm-val))
                     (let* ((stobjs-out  (car trans-ans))
                            (replaced-val (cdr trans-ans)))
                       (cond
                         ((equal stobjs-out acl2::*error-triple-sig*)
                          (let ((erp-flag (car replaced-val))
                                (val      (cadr replaced-val)))
                            (unless (or erp-flag (eq val :invisible))
                              (jupyter:execute-result
                               (jupyter:text
                                (let ((*package* (find-package
                                                  (acl2::current-package
                                                   *the-live-state*)))
                                      (*print-case* :downcase)
                                      (*print-pretty* t))
                                  (prin1-to-string val)))))))
                         (t
                          (unless (and (= (length stobjs-out) 1)
                                      (eq (car stobjs-out) 'acl2::state))
                            (jupyter:execute-result
                             (jupyter:text
                              (let ((*package* (find-package
                                                (acl2::current-package
                                                 *the-live-state*)))
                                    (*print-case* :downcase)
                                    (*print-pretty* t))
                                (prin1-to-string replaced-val)))))))))))))))))))


;;; ---------------------------------------------------------------------------
;;; evaluate-code -- dispatches to main thread
;;; ---------------------------------------------------------------------------

(defmethod jupyter:evaluate-code ((k kernel) code &optional source-path breakpoints)
  (declare (ignore source-path breakpoints))
  ;; Reset per-cell metadata
  (setf (cell-events k) #()
        (cell-package k) "ACL2")
  (let ((trimmed (string-trim '(#\Space #\Tab #\Newline #\Return) code)))
    (when (plusp (length trimmed))
      (multiple-value-bind (ename evalue traceback)
          (handler-case
              (in-main-thread
                ;; ---- Everything below runs on the main thread ----
                ;; with-suppression unlocks COMMON-LISP package (on SBCL)
                ;; so that pkg-witness can intern into it during undo etc.
                ;; This mirrors lp which wraps ld-fn in with-suppression.
                (acl2::with-suppression
                 (with-acl2-output-to *standard-output*
                     (let ((channel (make-string-input-channel trimmed)))
                       (unwind-protect
                           (jupyter-read-eval-print-loop channel *the-live-state*)
                         (close-string-input-channel channel)))
                   ;; After eval: capture events + package.
                   ;; Diff post-world against world-baseline.  The baseline
                   ;; is set in start: NIL for full-world mode (first cell
                   ;; gets the entire world) or (w state) for diff-only.
                   ;; After each cell, baseline advances to post-world.
                   (let* ((post-wrld (w *the-live-state*))
                          (baseline (world-baseline k))
                          (scan (if baseline
                                    (ldiff post-wrld baseline)
                                    post-wrld))
                          (events
                            (let ((*package* (find-package "ACL2"))
                                  (*print-case* :upcase))
                              (loop for triple in scan
                                    when (and (eq (car triple)
                                                  'acl2::event-landmark)
                                              (eq (cadr triple)
                                                  'acl2::global-value))
                                    collect (prin1-to-string
                                             (cddr triple))))))
                     (setf (cell-events k)
                           (coerce events 'vector)
                           (cell-package k)
                           (acl2::current-package *the-live-state*)
                           (world-baseline k) post-wrld)
                     (values)))))
            (error (c)
              (values (symbol-name (type-of c))
                      (format nil "~A" c)
                      (list (format nil "~A" c)))))
        ;; Back on shell thread.  Send metadata as display_data with a
        ;; vendor MIME type so it gets persisted in .ipynb cell outputs.
        (unless ename
          (jupyter::send-display-data
           (jupyter::kernel-iopub k)
           (list :object-plist
                 "application/vnd.acl2.events+json"
                 (list :object-alist
                       (cons "events" (cell-events k))
                       (cons "package" (cell-package k))))))
        ;; Return error triple to CL-Jupyter, or no values for success.
        (when ename
          (values ename evalue traceback))))))

(defmethod jupyter:code-is-complete ((k kernel) code)
  (let ((*package* (find-package "ACL2"))
        (*readtable* (copy-readtable nil)))
    (handler-case
        (with-input-from-string (stream code)
          (loop
            (loop for ch = (peek-char nil stream nil nil)
                  while (and ch (member ch '(#\Space #\Tab #\Newline #\Return)))
                  do (read-char stream))
            (let ((ch (peek-char nil stream nil nil)))
              (when (null ch) (return "complete"))
              (cond
                ((char= ch #\;) (read-line stream nil ""))
                (t (let ((form (read stream nil stream)))
                     (when (eq form stream) (return "complete"))))))))
      (end-of-file () "incomplete")
      (error () "invalid"))))


;;; ---------------------------------------------------------------------------
;;; Kernel Startup
;;; ---------------------------------------------------------------------------
;;; Set up a PERSISTENT LP context (like ld-fn0 does) and then block
;;; the main thread in the work loop.  The LP context lives for the
;;; entire kernel lifetime -- *ld-level* stays at 1, command history
;;; accumulates, and : commands work across cells.
;;;
;;; No sbcl-restart, no LD, no set-raw-mode-on!.  We're called
;;; directly from sbcl --eval.

(defun start (&optional connection-file)
  "Start the ACL2 Jupyter kernel."
  ;; Image initialization (idempotent -- same as sbcl-restart calls)
  (acl2::acl2-default-restart)
  ;; LP first-entry initialization (normally done by lp on first call).
  ;; We need these for include-book (:dir :system) to work.
  (let ((state *the-live-state*))
    (when (not acl2::*lp-ever-entered-p*)
      (f-put-global 'acl2::saved-output-reversed nil state)
      (acl2::push-current-acl2-world 'acl2::saved-output-reversed state)
      (acl2::set-initial-cbd)
      (acl2::establish-project-dir-alist
       (acl2::getenv$-raw "ACL2_SYSTEM_BOOKS") 'acl2-jupyter state)
      (acl2::setup-standard-io)
      (setq acl2::*lp-ever-entered-p* t))
    (f-put-global 'acl2::acl2-raw-mode-p nil state)
    (f-put-global 'acl2::ld-error-action :continue state)
    (sb-ext:disable-debugger)
    ;; Suppress slow alist/array warnings for interactive use
    (eval '(acl2::set-slow-alist-action nil))
    (f-put-global 'acl2::slow-array-action nil state)
    (setq *kernel-shutdown* nil)
    ;; Set world-baseline for first-cell event capture.
    ;; ACL2_JUPYTER_FULL_WORLD=1 → baseline = NIL (first cell gets entire world).
    ;; Otherwise baseline = current world (first cell gets only its own diff).
    (setq *initial-world-baseline*
          (if (equal (uiop:getenv "ACL2_JUPYTER_FULL_WORLD") "1")
              nil
              (w state)))
    (let ((conn (or connection-file
                    (first (uiop:command-line-arguments)))))
      (unless conn
        (error "No connection file provided"))
      ;; Set up persistent LP context -- mirroring ld-fn0's raw code.
      ;; This stays active for the lifetime of the kernel.
      (acl2::acl2-unwind acl2::*ld-level* nil)
      (push nil acl2::*acl2-unwind-protect-stack*)
      (let ((acl2::*ld-level* 1))
        (f-put-global 'acl2::ld-level 1 state)
        (unwind-protect
            (progn
              ;; Start Jupyter in a thread (like Bridge starts its listener)
              (bordeaux-threads:make-thread
               (lambda ()
                 (unwind-protect
                     (jupyter:run-kernel 'kernel conn)
                   (setq *kernel-shutdown* t)
                   (bt-semaphore:signal-semaphore *main-thread-ready*)))
               :name "jupyter-kernel")
              ;; Block main thread in work loop -- inside LP context
              (main-thread-loop))
          ;; Cleanup LP context on exit
          (f-put-global 'acl2::ld-level 0 state)
          (acl2::acl2-unwind 0 nil))))))

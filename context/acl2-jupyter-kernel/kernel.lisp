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

(defvar *initial-bootstrap-p* nil
  "When T, the kernel is running in boot-strap mode.
   Set by start-boot-strap.  Causes evaluate-code to use the
   simplified bootstrap-read-eval-print-loop instead of the
   normal interactive REPL loop.")

(defvar *initial-event-forms-p* nil
  "When T, each cell's display_data includes a 'forms' array of the
   original ACL2 event forms (the code as submitted), enabling the
   .ipynb to serve as a self-contained book.  Set from
   ACL2_JUPYTER_EVENT_FORMS env var in start.")

(defvar *initial-deep-events-p* nil
  "When NIL (default), only top-level events (depth=0) are included
   in the events/forms arrays, and absolute event numbers are stripped.
   Sub-events from include-book etc. can be found by following the
   include-book landmark to the referenced .ipynb.
   When T, all events (including embedded sub-events) are included
   with their full event-tuple structure including absolute numbers.
   Set from ACL2_JUPYTER_DEEP_EVENTS env var in start.")

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
   (cell-forms      :initform nil  :accessor cell-forms)
   (cell-package    :initform "ACL2" :accessor cell-package)
   (world-baseline  :initform *initial-world-baseline*
                    :accessor world-baseline
                    :documentation "Previous world state for event diff.
   Set from *initial-world-baseline* when the kernel is instantiated.
   NIL = full-world mode (first cell gets entire world).
   A world = diff-only (first cell gets only its own additions).")
   (event-forms-p   :initform *initial-event-forms-p*
                    :accessor event-forms-p
                    :documentation "When T, include original event forms
   in display_data so .ipynb can serve as a self-contained book.")
   (deep-events-p   :initform *initial-deep-events-p*
                    :accessor deep-events-p
                    :documentation "When NIL, only top-level events
   (depth=0) are included and event numbers are stripped.  When T,
   all events including embedded sub-events with full tuples.")
   (bootstrap-p     :initform *initial-bootstrap-p*
                    :accessor bootstrap-p
                    :documentation "When T, kernel is in boot-strap mode.
   Uses simplified REPL loop: no keyword commands, no string-as-in-package,
   no command landmarks."))
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
;;; Result Display Helpers
;;; ---------------------------------------------------------------------------

(defun format-acl2-value (val)
  "Pretty-print VAL in the current ACL2 package, downcased."
  (let ((*package* (find-package (acl2::current-package *the-live-state*)))
        (*print-case* :downcase)
        (*print-pretty* t))
    (prin1-to-string val)))

(defun display-trans-eval-result (trans-ans)
  "Send the result of a trans-eval call to Jupyter as execute_result.
   TRANS-ANS is (stobjs-out . replaced-val).
   Error-triple results are displayed unless erp or :invisible.
   Non-triple results are displayed unless state-only.
   No-op when no kernel is active (e.g. in test harness)."
  (when jupyter:*kernel*
    (let ((stobjs-out   (car trans-ans))
          (replaced-val (cdr trans-ans)))
      (cond
        ((equal stobjs-out acl2::*error-triple-sig*)
         (let ((erp-flag (car replaced-val))
               (val      (cadr replaced-val)))
           (unless (or erp-flag (eq val :invisible))
             (jupyter:execute-result
              (jupyter:text (format-acl2-value val))))))
        (t
         (unless (and (= (length stobjs-out) 1)
                      (eq (car stobjs-out) 'acl2::state))
           (jupyter:execute-result
            (jupyter:text (format-acl2-value replaced-val)))))))))


;;; ---------------------------------------------------------------------------
;;; Boot-strap Read-Eval-Print Loop
;;; ---------------------------------------------------------------------------
;;; Simplified REPL for boot-strap mode.  No keyword commands, no
;;; string-as-in-package, no command landmarks.  Just:
;;;   read form → trans-eval → display result
;;;
;;; During boot-strap, the primordial world has no command landmark
;;; infrastructure (next-absolute-command-number → (1+ NIL) → crash),
;;; and interactive features like :pe, :pbt are not needed.

(defun bootstrap-read-eval-print-loop (channel state)
  "Read forms from CHANNEL, evaluate each via trans-eval.
   Simplified for boot-strap mode: no keyword expansion, no command
   landmarks.  Output routing is handled by the caller."
  (let ((*readtable* acl2::*acl2-readtable*))
    (catch 'acl2::local-top-level
      (loop
        (acl2::acl2-unwind acl2::*ld-level* t)
        (multiple-value-bind (eofp raw-form state)
            (acl2::read-object channel state)
          (when eofp (return))
          (let ((form raw-form))
            (initialize-accumulated-warnings)
            (acl2::initialize-timers state)
            (f-put-global 'acl2::last-make-event-expansion nil state)
            (multiple-value-bind (erp trans-ans state)
                (acl2::trans-eval-default-warning
                 form 'acl2-jupyter state t)
              (unless erp
                (display-trans-eval-result trans-ans)))))))))


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
              (acl2::initialize-timers state)
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
;;; Cell Metadata Capture
;;; ---------------------------------------------------------------------------

(defun extract-event-tuples (scan deep-p)
  "Extract event-landmark tuples from world SCAN (an ldiff).
   When DEEP-P is NIL, keep only depth=0 (top-level) tuples."
  (let ((all (loop for triple in scan
                   when (and (eq (car triple) 'acl2::event-landmark)
                             (eq (cadr triple) 'acl2::global-value))
                   collect (cddr triple))))
    (if deep-p
        all
        (remove-if-not
         (lambda (et)
           (let ((inner (if (eq (car et) 'acl2::local) (cdr et) et)))
             (integerp (car inner))))
         all))))

(defun format-event-tuples (event-tuples deep-p)
  "Format EVENT-TUPLES as printable strings.
   DEEP-P T: full tuples with event numbers.
   DEEP-P NIL: strip event number, unwrap LOCAL wrapper."
  (let ((*package* (find-package "ACL2"))
        (*print-case* :upcase))
    (if deep-p
        (mapcar #'prin1-to-string event-tuples)
        (mapcar (lambda (et)
                  (let ((inner (if (eq (car et) 'acl2::local) (cdr et) et)))
                    (prin1-to-string (cdr inner))))
                event-tuples))))

(defun format-event-forms (event-tuples)
  "Format the original source forms from EVENT-TUPLES as printable strings."
  (let ((*package* (find-package "ACL2"))
        (*print-case* :downcase))
    (mapcar (lambda (et)
              (prin1-to-string (acl2::access-event-tuple-form et)))
            event-tuples)))

(defun collect-cell-events (k)
  "Diff post-world against world-baseline in kernel K.
   Updates cell-events, cell-forms, cell-package, and world-baseline."
  (let* ((post-wrld (w *the-live-state*))
         (baseline  (world-baseline k))
         (scan      (if baseline (ldiff post-wrld baseline) post-wrld))
         (tuples    (extract-event-tuples scan (deep-events-p k)))
         (events    (format-event-tuples tuples (deep-events-p k)))
         (forms     (when (event-forms-p k) (format-event-forms tuples))))
    (setf (cell-events k)   (coerce events 'vector)
          (cell-forms k)    (when forms (coerce forms 'vector))
          (cell-package k)  (acl2::current-package *the-live-state*)
          (world-baseline k) post-wrld)))

(defun send-cell-metadata (k)
  "Send cell metadata as display_data with vendor MIME type."
  (let ((alist (list (cons "events" (cell-events k))
                     (cons "package" (cell-package k)))))
    (when (plusp (length (cell-forms k)))
      (push (cons "forms" (cell-forms k)) (cdr (last alist))))
    (jupyter::send-display-data
     (jupyter::kernel-iopub k)
     (list :object-plist
           "application/vnd.acl2.events+json"
           (cons :object-alist alist)))))


;;; ---------------------------------------------------------------------------
;;; evaluate-code -- dispatches to main thread
;;; ---------------------------------------------------------------------------

(defvar *bootstrap-pass2-directive* ":bootstrap-enter-pass-2"
  "Sentinel string sent by build_boot_strap.py to trigger pass-2 transition.
   Matched literally in eval-cell before dispatching to the REPL.")

(defun bootstrap-enter-pass-2 (state)
  "Transition from pass 1 to pass 2 during bootstrap.
   Replicates the effects of ACL2's enter-boot-strap-pass-2 without calling
   ld-fn (which would fail due to missing command landmarks in our bootstrap
   world that bypasses ld).  Mirrors initialize-acl2's inter-pass logic:
     1. Set boot-strap-pass-2 = t in the world
     2. Initialize memoization tables
     3. Switch default-defun-mode to :logic
     4. Change ld-skip-proofsp from initialize-acl2 to include-book"
  (format t "~&;; [boot-strap] Transitioning to pass 2 ...~%")
  ;; Debug: check *1* functions  
  (handler-case
      (with-open-file (dbg "/tmp/bootstrap-pass2-debug.log"
                           :direction :output :if-exists :supersede)
        (let ((test-fns '(acl2::in-package-fn acl2::defconst-fn acl2::defmacro-fn
                          acl2::legal-variablep acl2::defun-fn
                          acl2::defuns-fn acl2::encapsulate-fn)))
          (dolist (fn test-fns)
            (let ((*1*sym (acl2::*1*-symbol fn)))
              (format dbg "*1* ~a [~a] => ~a~%" fn *1*sym
                      (if (fboundp *1*sym) "DEFINED" "MISSING")))))
        ;; Count total *1* symbols
        (let ((total 0) (defined 0))
          (do-symbols (sym (find-package "ACL2_*1*_ACL2"))
            (incf total)
            (when (fboundp sym) (incf defined)))
          (format dbg "~%Total *1* symbols: ~a, Defined: ~a~%" total defined)))
    (error (c) (format t "~&;; [boot-strap] Debug error: ~a~%" c)))
  ;; Same as enter-boot-strap-pass-2 minus the ld-fn call:
  (push nil acl2::*acl2-unwind-protect-stack*)
  (acl2::set-w 'acl2::extension
               (acl2::global-set 'acl2::boot-strap-pass-2 t (w state))
               state)
  (acl2::acl2-unwind acl2::*ld-level* nil)
  ;; Initialize memoization (needed for memoize calls in boot-strap-pass-2-b)
  (acl2::memoize-init)
  ;; Switch to :logic default-defun-mode (equivalent to ld of (logic))
  (f-put-global 'acl2::default-defun-mode :logic state)
  ;; Change ld-skip-proofsp for pass 2
  (f-put-global 'acl2::ld-skip-proofsp 'acl2::include-book state)
  (format t "~&;; [boot-strap] Pass 2 ready (default-defun-mode = :logic, ld-skip-proofsp = include-book).~%"))

(defun eval-cell (k trimmed)
  "Evaluate TRIMMED code string through the appropriate REPL loop.
   Captures cell metadata (events, forms, package) into kernel K.
   Runs on the main thread inside with-suppression.
   Returns (values) on success so evaluate-code sees no ename."
  ;; Bootstrap pass-2 transition directive (sent by build_boot_strap.py)
  (when (and (bootstrap-p k)
             (string= trimmed *bootstrap-pass2-directive*))
    (bootstrap-enter-pass-2 *the-live-state*)
    (collect-cell-events k)
    (return-from eval-cell (values)))
  (acl2::with-suppression
      (with-acl2-output-to *standard-output*
        (let ((channel (make-string-input-channel trimmed)))
          (unwind-protect
              (if (bootstrap-p k)
                  (bootstrap-read-eval-print-loop channel *the-live-state*)
                  (jupyter-read-eval-print-loop channel *the-live-state*))
            (close-string-input-channel channel))))
      (collect-cell-events k)
      (values)))

(defmethod jupyter:evaluate-code ((k kernel) code &optional source-path breakpoints)
  (declare (ignore source-path breakpoints))
  (setf (cell-events k) #()
        (cell-forms k)  nil
        (cell-package k) "ACL2")
  (let ((trimmed (string-trim '(#\Space #\Tab #\Newline #\Return) code)))
    (when (plusp (length trimmed))
      (multiple-value-bind (ename evalue traceback)
          (handler-case
              (in-main-thread (eval-cell k trimmed))
            (error (c)
              (values (symbol-name (type-of c))
                      (format nil "~A" c)
                      (list (format nil "~A" c)))))
        (unless ename (send-cell-metadata k))
        (when ename (values ename evalue traceback))))))

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

;;; ---------------------------------------------------------------------------
;;; Kernel Launch Helpers
;;; ---------------------------------------------------------------------------

(defun prepare-kernel-state (state)
  "Common state setup for both normal and boot-strap kernel modes."
  (f-put-global 'acl2::acl2-raw-mode-p nil state)
  (f-put-global 'acl2::ld-error-action :continue state)
  (sb-ext:disable-debugger)
  (eval '(acl2::set-slow-alist-action nil))
  (f-put-global 'acl2::slow-array-action nil state)
  (setq *kernel-shutdown* nil))

(defun run-kernel-with-lp-context (conn thread-name state)
  "Set up persistent LP context and run the Jupyter kernel.
   CONN is the connection file path.  Blocks until shutdown."
  (acl2::acl2-unwind acl2::*ld-level* nil)
  (push nil acl2::*acl2-unwind-protect-stack*)
  (let ((acl2::*ld-level* 1))
    (f-put-global 'acl2::ld-level 1 state)
    (unwind-protect
        (progn
          (bordeaux-threads:make-thread
           (lambda ()
             (unwind-protect
                 (jupyter:run-kernel 'kernel conn)
               (setq *kernel-shutdown* t)
               (bt-semaphore:signal-semaphore *main-thread-ready*)))
           :name thread-name)
          (main-thread-loop))
      (f-put-global 'acl2::ld-level 0 state)
      (acl2::acl2-unwind 0 nil))))

(defun start (&optional connection-file
              &key full-world event-forms deep-events)
  "Start the ACL2 Jupyter kernel.
   CONNECTION-FILE: Jupyter connection file path (or from argv).
   FULL-WORLD: when T, first cell gets entire world (not just diff).
   EVENT-FORMS: when T, include original event forms in metadata.
   DEEP-EVENTS: when T, include embedded sub-events with full tuples."
  (acl2::acl2-default-restart)
  ;; LP first-entry initialization (normally done by lp on first call).
  (let ((state *the-live-state*))
    (when (not acl2::*lp-ever-entered-p*)
      (f-put-global 'acl2::saved-output-reversed nil state)
      (acl2::push-current-acl2-world 'acl2::saved-output-reversed state)
      (acl2::set-initial-cbd)
      (acl2::establish-project-dir-alist
       (acl2::getenv$-raw "ACL2_SYSTEM_BOOKS") 'acl2-jupyter state)
      (acl2::setup-standard-io)
      (setq acl2::*lp-ever-entered-p* t))
    (prepare-kernel-state state)
    (setq *initial-world-baseline*
          (if full-world nil (w state)))
    (setq *initial-bootstrap-p* nil)
    (setq *initial-event-forms-p* (and event-forms t))
    (setq *initial-deep-events-p* (and deep-events t))
    (let ((conn (or connection-file
                    (first (uiop:command-line-arguments)))))
      (unless conn (error "No connection file provided"))
      (run-kernel-with-lp-context conn "jupyter-kernel" state))))


;;; ---------------------------------------------------------------------------
;;; Boot-Strap Kernel Startup
;;; ---------------------------------------------------------------------------
;;; Like start, but replicates the boot-strap process from initialize-acl2:
;;;   1. load-acl2  (raw CL compilation artefacts)
;;;   2. enter-boot-strap-mode  (primordial world, :acl2-loop-only feature)
;;;   3. Set ld-skip-proofsp = initialize-acl2  (pass 1)
;;;
;;; This is launched from init.lisp (NOT saved_acl2.core) since the boot-strap
;;; builds the world from scratch.
;;;
;;; A SINGLE kernel handles both passes.  It starts in pass 1 mode.
;;; The Python build script sends the :bootstrap-enter-pass-2 directive
;;; between passes, which triggers bootstrap-enter-pass-2 to switch to
;;; pass 2 (ld-skip-proofsp = include-book, default-defun-mode = :logic).
;;;
;;; The Python build script (build_boot_strap.py) drives execution by
;;; opening each .ipynb and executing cells one at a time against this
;;; kernel, collecting the per-cell display_data (events + forms).

(defun start-boot-strap (&optional connection-file)
  "Start an ACL2 Jupyter kernel in boot-strap mode.
   Always starts in pass 1: enter-boot-strap-mode, ld-skip-proofsp = initialize-acl2.
   The build script sends :bootstrap-enter-pass-2 to transition to pass 2.

   Prerequisite: load-acl2 must have been called before the kernel package
   is loaded.  The boot-strap kernel.json argv handles this by including
     --eval \"(acl2::load-acl2 :load-acl2-proclaims acl2::*do-proclaims*)\"
   before quickloading the kernel."
  (format t "~&;; [boot-strap] Entering boot-strap mode (pass 1) ...~%")
  (push :acl2-loop-only *features*)
  (let ((state *the-live-state*))
    (acl2::set-initial-cbd)
    (makunbound 'acl2::*copy-of-common-lisp-symbols-from-main-lisp-package*)
    (acl2::enter-boot-strap-mode nil (acl2::get-os))
    (f-put-global 'acl2::ld-skip-proofsp 'acl2::initialize-acl2 state)
    (format t "~&;; [boot-strap] Kernel ready (pass 1).~%")
    (setq acl2::*lp-ever-entered-p* t)
    (prepare-kernel-state state)
    (setq *initial-world-baseline* (w state))
    (setq *initial-bootstrap-p* t)
    (setq *initial-event-forms-p* t)
    (setq *initial-deep-events-p* nil)
    (let ((conn (or connection-file
                    (first (uiop:command-line-arguments)))))
      (unless conn (error "No connection file provided"))
      (run-kernel-with-lp-context conn "jupyter-kernel-bootstrap" state))))


;;; ---------------------------------------------------------------------------
;;; Boot-Strap Pass-2-Only Kernel Startup
;;; ---------------------------------------------------------------------------
;;; Like start-boot-strap, but runs pass 1 internally via ACL2's own ld-fn
;;; (which correctly handles *1* function compilation, command landmarks,
;;; and all event processing).  The kernel starts already in pass 2 state,
;;; so the build script only needs to execute pass-2 notebooks.
;;;
;;; This avoids the *1* function errors and PROGN!-FN problems that occur
;;; when our simplified bootstrap REPL handles pass 1, while still giving
;;; us a proper pass-2 world for capturing notebook execution metadata.

(defun start-boot-strap-pass2 (&optional connection-file)
  "Start an ACL2 Jupyter kernel in pass-2-only mode.
   Runs pass 1 internally via ACL2's ld-fn, then transitions to pass 2.
   Only pass-2 notebooks need execution by the build script.

   Prerequisite: same as start-boot-strap (load-acl2 must have been called)."
  (format t "~&;; [boot-strap-pass2] Entering boot-strap mode ...~%")
  (push :acl2-loop-only *features*)
  (let ((state *the-live-state*))
    (acl2::set-initial-cbd)
    (makunbound 'acl2::*copy-of-common-lisp-symbols-from-main-lisp-package*)
    (acl2::enter-boot-strap-mode nil (acl2::get-os))
    ;; --- Pass 1 via ld-fn (mirrors initialize-acl2) ---
    ;; Each non-raw, non-pass-2 file is processed with
    ;; ld-skip-proofsp = initialize-acl2, exactly as in initialize-acl2.
    (format t "~&;; [boot-strap-pass2] Running pass 1 via ld-fn ...~%")
    (force-output)
    (dolist (fl acl2::*acl2-files*)
      (when (not (or (equal fl "boot-strap-pass-2-a")
                     (equal fl "boot-strap-pass-2-b")
                     (acl2::raw-source-name-p fl)))
        (format t "~&;; [pass 1] ~a~%" fl)
        (force-output)
        (let ((fname (concatenate 'string fl "." acl2::*lisp-extension*)))
          (multiple-value-bind (er val st)
              (acl2::ld-fn
               (acl2::ld-alist-raw fname
                                   'acl2::initialize-acl2
                                   :error)
               state nil)
            (declare (ignore val st))
            (when er
              (error "[boot-strap-pass2] Pass 1 error on ~a" fl))))))
    ;; --- Transition to pass 2 ---
    ;; enter-boot-strap-pass-2 sets boot-strap-pass-2 = t, initializes
    ;; memoization, and switches default-defun-mode to :logic.
    (format t "~&;; [boot-strap-pass2] Transitioning to pass 2 ...~%")
    (acl2::enter-boot-strap-pass-2)
    ;; Set ld-skip-proofsp for our REPL (enter-boot-strap-pass-2 sets
    ;; it per-ld-call, but our trans-eval reads the global value).
    (f-put-global 'acl2::ld-skip-proofsp 'acl2::include-book state)
    (format t "~&;; [boot-strap-pass2] Kernel ready (pass 2).~%")
    (setq acl2::*lp-ever-entered-p* t)
    (prepare-kernel-state state)
    (setq *initial-world-baseline* (w state))
    (setq *initial-bootstrap-p* t)
    (setq *initial-event-forms-p* t)
    (setq *initial-deep-events-p* nil)
    (let ((conn (or connection-file
                    (first (uiop:command-line-arguments)))))
      (unless conn (error "No connection file provided"))
      (run-kernel-with-lp-context conn "jupyter-kernel-bootstrap-pass2" state))))

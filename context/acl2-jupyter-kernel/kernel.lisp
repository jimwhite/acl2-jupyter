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
;;;; ALL user code is evaluated through ACL2's trans-eval inside LP
;;;; scaffolding copied from ld-fn0.  This gives us:
;;;;   - *ld-level* > 0, catch tags, acl2-unwind-protect  (LP context)
;;;;   - Structured (stobjs-out . replaced-val) results   (not stdout)
;;;;   - ACL2's own reader (via read-object on a channel)
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
                         ;; Non-local exit (ACL2 throw) — same as Bridge:
                         ;; set errval so caller sees the error.
                         (unless ,finished
                           (setq ,errval
                                 (make-condition
                                  'simple-error
                                  :format-control "Unexpected non-local exit.")))
                         (return-from main-thread-work nil)))
                     ;; Signal AFTER the block — same position as Bridge.
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
  ()
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
;;; LP Scaffolding + trans-eval  —  our own read-eval-print loop
;;; ---------------------------------------------------------------------------
;;; We copy the essential LP setup from ld-fn0 (raw code in ld.lisp):
;;;   1. ACL2-UNWIND / push unwind-protect stack
;;;   2. Increment *LD-LEVEL* (both CL special and state global)
;;;   3. CATCH 'LOCAL-TOP-LEVEL
;;;   4. trans-eval for each form — returns structured results
;;;   5. Cleanup: restore *LD-LEVEL*, pop unwind stack
;;;
;;; trans-eval returns (mv erp (stobjs-out . replaced-val) state).
;;;   - erp non-nil means error (already printed to channels)
;;;   - stobjs-out = (NIL NIL STATE) for error triples (most events)
;;;   - For error triples: replaced-val = (erp-flag val state-symbol)
;;;     We display val via execute_result unless it's :invisible.
;;;   - For non-triples: replaced-val is the value(s) directly.

(defun jupyter-read-eval-print-loop (channel state)
  "Read forms from CHANNEL, evaluate each via trans-eval inside LP context,
   and send structured results to Jupyter.  Proof/event output streams to
   stdout via the already-bound ACL2 output channels."
  (let* ((old-ld-level (f-get-global 'acl2::ld-level state))
         (new-ld-level (1+ old-ld-level)))
    ;; Set up LP context — mirroring ld-fn0's raw code
    (acl2::acl2-unwind acl2::*ld-level* nil)
    (push nil acl2::*acl2-unwind-protect-stack*)
    (let ((acl2::*ld-level* new-ld-level)
          (*readtable* acl2::*acl2-readtable*))
      (f-put-global 'acl2::ld-level new-ld-level state)
      (unwind-protect
          (catch 'acl2::local-top-level
            (loop
              (multiple-value-bind (eofp form state)
                  (acl2::read-object channel state)
                (when eofp (return))
                ;; Evaluate via trans-eval — full ACL2 event processing
                (multiple-value-bind (erp trans-ans state)
                    (acl2::trans-eval-default-warning
                     form 'acl2-jupyter state t)
                  (cond
                    (erp
                     ;; Error already printed to ACL2 channels (stdout).
                     ;; Revert world on error, same as ld-read-eval-print.
                     nil)
                    (t
                     ;; Extract result for Jupyter execute_result
                     (let* ((stobjs-out (car trans-ans))
                            (replaced-val (cdr trans-ans)))
                       (cond
                         ;; Error triple: (mv erp val state)
                         ;; stobjs-out = (NIL NIL STATE)
                         ((equal stobjs-out acl2::*error-triple-sig*)
                          (let ((erp-flag (car replaced-val))
                                (val (cadr replaced-val)))
                            (cond
                              (erp-flag
                               ;; Non-nil erp means the form signaled error
                               nil)
                              ((eq val :invisible)
                               nil)
                              ((eq val :q)
                               ;; User typed :q — ignore, don't exit kernel
                               nil)
                              (t
                               (jupyter:execute-result
                                (jupyter:text
                                 (let ((*package* (find-package
                                                   (acl2::current-package
                                                    *the-live-state*)))
                                       (*print-case* :downcase)
                                       (*print-pretty* t))
                                   (prin1-to-string val))))))))
                         ;; Non-error-triple: display result directly
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
                                (prin1-to-string replaced-val))))))))))))))
        ;; Cleanup — restore ld-level, pop unwind stack
        (f-put-global 'acl2::ld-level old-ld-level state)
        (acl2::acl2-unwind (1- acl2::*ld-level*) nil)))))


;;; ---------------------------------------------------------------------------
;;; evaluate-code — dispatches to main thread
;;; ---------------------------------------------------------------------------

(defmethod jupyter:evaluate-code ((k kernel) code &optional source-path breakpoints)
  (declare (ignore source-path breakpoints))
  (let ((trimmed (string-trim '(#\Space #\Tab #\Newline #\Return) code)))
    (when (plusp (length trimmed))
      (handler-case
          (in-main-thread
            ;; ---- Everything below runs on the main thread ----
            (with-acl2-output-to *standard-output*
              (let ((channel (make-string-input-channel trimmed)))
                (unwind-protect
                    (jupyter-read-eval-print-loop channel *the-live-state*)
                  (close-string-input-channel channel)))))
        (error (c)
          (values (symbol-name (type-of c))
                  (format nil "~A" c)
                  (list (format nil "~A" c))))))))

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
;;; Same pattern as Bridge's start-fn:
;;;   1. Start listener/kernel in a spawned thread
;;;   2. Block main thread in main-thread-loop

(defun start (&optional connection-file)
  "Start the ACL2 Jupyter kernel."
  ;; Turn off raw mode — we needed it only for LP to call this function.
  (f-put-global 'acl2::acl2-raw-mode-p nil *the-live-state*)
  (sb-ext:disable-debugger)
  ;; Suppress slow alist/array warnings for interactive use (same as acl2_jupyter)
  (eval '(acl2::set-slow-alist-action nil))
  (f-put-global 'acl2::slow-array-action nil *the-live-state*)
  (setq *kernel-shutdown* nil)
  (let ((conn (or connection-file
                  (first (uiop:command-line-arguments)))))
    (unless conn
      (error "No connection file provided"))
    ;; Start Jupyter in a thread (like Bridge starts its listener thread)
    (bordeaux-threads:make-thread
     (lambda ()
       (unwind-protect
           (jupyter:run-kernel 'kernel conn)
         (setq *kernel-shutdown* t)
         (bt-semaphore:signal-semaphore *main-thread-ready*)))
     :name "jupyter-kernel")
    ;; Block main thread in work loop (like Bridge's start-fn)
    (main-thread-loop)))

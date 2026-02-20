;;;; ACL2 Jupyter Kernel - Kernel Class
;;;;
;;;; Architecture:
;;;;
;;;;   Shell thread (Jupyter): owns *kernel*, IOPub socket, protocol.
;;;;   Main thread (ACL2):     owns 64MB stack, ACL2 state, output channels.
;;;;
;;;; evaluate-code runs on the shell thread.  It dispatches ACL2 work
;;;; (output routing + eval) to the main thread via in-main-thread,
;;;; which returns results.  Jupyter protocol calls (execute-result)
;;;; stay on the shell thread where *kernel* is bound.
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
                     (block main-thread-work
                       (unwind-protect
                           (handler-case
                             (progn
                               (setq ,retvals (multiple-value-list (progn ,@forms)))
                               (setq ,finished t))
                             (error (condition)
                               (setq ,errval condition)
                               (setq ,finished t)))
                         ;; ACL2 throws (e.g. include-book) bypass handler-case.
                         ;; Side effects already happened.  Treat as success
                         ;; with nil result — same as Bridge, which lets the
                         ;; uncaught throw become a caught condition at a
                         ;; higher level.
                         (unless ,finished
                           (setq ,finished t))
                         (return-from main-thread-work nil))))
                   (bt-semaphore:signal-semaphore ,done)))))
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
;;; REPL Variables
;;; ---------------------------------------------------------------------------

(defvar *acl2-last-form* nil)
(defvar *acl2-results* nil)

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
;;; ACL2 Form Evaluation
;;; ---------------------------------------------------------------------------
;;; Same pattern as Bridge's worker-do-work:
;;;   (eval `(let ((state *the-live-state*)) (declare (ignorable state)) ,cmd))
;;; Plus catch for raw-ev-fncall to handle ACL2 throws gracefully.

(defun acl2-eval (form)
  "Evaluate a single ACL2 form with STATE bound to *the-live-state*.
   Catches raw-ev-fncall throws so they become CL errors."
  (let ((threw t))
    (let ((result
            (multiple-value-list
             (catch 'acl2::raw-ev-fncall
               (prog1
                   (eval
                    `(let ((state *the-live-state*))
                       (declare (ignorable state))
                       ,form))
                 (setq threw nil))))))
      (when threw
        (let ((msg (ignore-errors
                     (format nil "~A"
                             (if (and (consp (car result))
                                      (consp (cdar result)))
                                 (cadar result)
                                 (car result))))))
          (error "ACL2 error: ~A" (or msg "unknown error"))))
      result)))

(defun read-acl2-forms (code)
  "Read all forms from a string of ACL2 code."
  (let ((forms nil)
        (*package* (find-package "ACL2"))
        (*readtable* (copy-readtable nil)))
    (with-input-from-string (stream code)
      (loop
        (loop for ch = (peek-char nil stream nil nil)
              while (and ch (member ch '(#\Space #\Tab #\Newline #\Return)))
              do (read-char stream))
        (let ((ch (peek-char nil stream nil nil)))
          (when (null ch) (return))
          (cond
            ((char= ch #\:)
             (read-line stream nil ""))
            ((char= ch #\;)
             (read-line stream nil ""))
            (t
             (handler-case
                 (let ((form (read stream nil stream)))
                   (unless (eq form stream)
                     (push form forms)))
               (error (c)
                 (let ((rest (read-line stream nil "")))
                   (push `(acl2::er acl2::soft 'acl2-jupyter
                                    "Read error: ~@0 near: ~@1"
                                    ,(format nil "~A" c)
                                    ,rest)
                         forms)))))))))
    (nreverse forms)))

;;; ---------------------------------------------------------------------------
;;; evaluate-code — ALL work dispatched to main thread
;;; ---------------------------------------------------------------------------
;;; This is the key architectural alignment with Bridge.  Bridge's worker
;;; thread does: output routing → eval → result handling, all on ONE thread.
;;; We do the same on the main thread.  The Jupyter shell thread only
;;; dispatches and waits.

(defmethod jupyter:evaluate-code ((k kernel) code &optional source-path breakpoints)
  (declare (ignore source-path breakpoints))
  (let ((forms (let ((*package* (find-package "ACL2")))
                 (read-acl2-forms code))))
    (handler-case
        (in-main-thread
          ;; ---- Everything below runs on the main thread ----
          (with-acl2-output-to *standard-output*
            (let ((*package* (find-package "ACL2")))
              (dolist (form forms)
                (setf *acl2-last-form* form)
                (let ((results (acl2-eval form)))
                  (setf *acl2-results* results)
                  (dolist (result results)
                    (unless (eq result *the-live-state*)
                      (jupyter:execute-result
                       (jupyter:text
                        (let ((*package* (find-package "ACL2"))
                              (*print-case* :downcase)
                              (*print-pretty* t))
                          (prin1-to-string result)))))))))))
      (error (c)
        (values (symbol-name (type-of c))
                (format nil "~A" c)
                (list (format nil "~A" c)))))))

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
                ((char= ch #\:) (read-line stream nil ""))
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

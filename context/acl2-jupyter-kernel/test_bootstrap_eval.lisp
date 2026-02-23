;;;; Test harness for the bootstrap REPL loop.
;;;;
;;;; Exercises bootstrap-read-eval-print-loop directly in a
;;;; primordial world — same code path as the bootstrap kernel,
;;;; without Jupyter wire protocol.
;;;;
;;;; Run via start-kernel-bootstrap.sh's startup sequence, minus the
;;;; kernel launch:
;;;;
;;;;   cd /home/acl2 && \
;;;;   sbcl --tls-limit 16384 --dynamic-space-size 32000 \
;;;;        --control-stack-size 64 --disable-ldb \
;;;;        --end-runtime-options \
;;;;        --no-userinit --disable-debugger \
;;;;        --load init.lisp \
;;;;        --eval '(acl2::load-acl2 :load-acl2-proclaims acl2::*do-proclaims*)' \
;;;;        --load "$HOME/quicklisp/setup.lisp" \
;;;;        --eval '(ql:quickload :acl2-jupyter-kernel :silent t)' \
;;;;        --load context/acl2-jupyter-kernel/test_bootstrap_eval.lisp

;;; -----------------------------------------------------------------------
;;; Boot-strap mode setup (mirrors start-boot-strap, kernel.lisp)
;;; -----------------------------------------------------------------------

(in-package "ACL2")

(format t "~&;; [test] Entering boot-strap mode ...~%")
(push :acl2-loop-only *features*)
(let ((state *the-live-state*))
  (set-initial-cbd)
  (makunbound '*copy-of-common-lisp-symbols-from-main-lisp-package*)
  (enter-boot-strap-mode nil (get-os))
  (f-put-global 'ld-skip-proofsp 'initialize-acl2 state)
  (f-put-global 'acl2-raw-mode-p nil state)
  (f-put-global 'ld-error-action :continue state)
  (eval '(set-slow-alist-action nil))
  (f-put-global 'slow-array-action nil state)
  (setq *lp-ever-entered-p* t)
  ;; Push an LP frame so acl2-unwind has something to work with
  (acl2-unwind *ld-level* nil)
  (push nil *acl2-unwind-protect-stack*)
  (setq *ld-level* 1)
  (f-put-global 'ld-level 1 state))
(format t "~&;; [test] Boot-strap mode ready.~%")

;;; -----------------------------------------------------------------------
;;; Test infrastructure
;;; -----------------------------------------------------------------------

(in-package "ACL2-JUPYTER")

(defvar *test-pass* 0)
(defvar *test-fail* 0)

(defun test-check (name condition)
  (if condition
      (progn (format t "  PASS: ~A~%" name) (incf *test-pass*))
      (progn (format t "  FAIL: ~A~%" name) (incf *test-fail*))))

(defun bootstrap-eval-string (source)
  "Evaluate SOURCE string through bootstrap-read-eval-print-loop.
   Returns the captured output as a string.
   Binds jupyter:*kernel* to suppress execute-result calls that
   need a running kernel (we have none in this test harness)."
  (let ((output (make-string-output-stream))
        (jupyter:*kernel* nil))
    (handler-case
        (with-acl2-output-to output
          (let ((channel (make-string-input-channel source)))
            (unwind-protect
                (bootstrap-read-eval-print-loop channel *the-live-state*)
              (close-string-input-channel channel))))
      ;; Catch execute-result errors from missing kernel
      (serious-condition (c)
        (let ((msg (format nil "~A" c)))
          (unless (search "KERNEL-IOPUB" msg)
            (format output "~&ERROR: ~A~%" c)))))
    (get-output-stream-string output)))

(defun bootstrap-eval-string-full (source)
  "Like bootstrap-eval-string but also returns the post-world.
   Returns (values output-string post-world error-p)."
  (let ((output (make-string-output-stream))
        (jupyter:*kernel* nil)
        (error-p nil))
    (handler-bind
        ((serious-condition
           (lambda (c)
             (let ((msg (format nil "~A" c)))
               (when (search "KERNEL-IOPUB" msg)
                 ;; Suppress execute-result errors from missing kernel
                 (return-from bootstrap-eval-string-full
                   (values (get-output-stream-string output)
                           (w *the-live-state*)
                           nil)))
               (setq error-p t)
               (format output "~&ERROR: ~A~%" c)
               (format output "~&BACKTRACE:~%")
               (sb-debug:print-backtrace :stream output :count 20)
               nil))))
      (handler-case
          (with-acl2-output-to output
            (let ((channel (make-string-input-channel source)))
              (unwind-protect
                  (bootstrap-read-eval-print-loop channel *the-live-state*)
                (close-string-input-channel channel))))
        (serious-condition (c)
          (declare (ignore c)))))
    (values (get-output-stream-string output)
            (w *the-live-state*)
            error-p)))


;;; =====================================================================
;;; Tests — exercise the same forms that axioms.ipynb cells contain
;;; =====================================================================

(format t "~%=== Bootstrap Eval Tests ===~%")

;;; --- Sanity: is the function defined? ---
(format t "~%--- Sanity: fboundp ---~%")
(test-check "bootstrap-read-eval-print-loop is fboundp"
            (fboundp 'bootstrap-read-eval-print-loop))
(test-check "make-string-input-channel is fboundp"
            (fboundp 'make-string-input-channel))
(test-check "close-string-input-channel is fboundp"
            (fboundp 'close-string-input-channel))
(test-check "with-acl2-output-to is bound (macro)"
            (macro-function 'with-acl2-output-to))

;;; --- Cell 0: (in-package "ACL2") ---
(format t "~%--- Cell 0: in-package ---~%")
(let ((out (bootstrap-eval-string "(in-package \"ACL2\")")))
  (test-check "in-package completes without error"
              (not (search "ERROR:" out)))
  (format t "    output: ~S~%" out))

;;; --- Read sanity: a simple value expression ---
(format t "~%--- Sanity: value expression ---~%")
(let ((out (bootstrap-eval-string "42")))
  (test-check "42 evaluates cleanly"
              (not (search "ERROR:" out)))
  (format t "    output: ~S~%" out))

;;; --- Cell 1: *common-lisp-symbols-from-main-lisp-package* ---
;;; This is the defconst that triggered TYPE-ERROR: NIL is not NUMBER.
(format t "~%--- Cell 1: defconst *common-lisp-symbols-from-main-lisp-package* ---~%")
(multiple-value-bind (out wrld error-p)
    ;; Read the actual cell 1 source from axioms.ipynb
    (let* ((nb-path (merge-pathnames "axioms.ipynb"
                                     (truename "/home/acl2/")))
           ;; Quick and dirty: slurp the notebook as text, then use
           ;; the Python-side test for actual content.  For the Lisp
           ;; test, use a representative defconst instead.
           (form-str
             "(acl2::defconst acl2::*common-lisp-symbols-from-main-lisp-package*
               '(& * + - / 1+ 1- < <= = > >= abort abs acons aref
                 atom car cdr char char-code char-downcase char-equal
                 char-upcase char< char<= char> char>= characterp
                 code-char coerce compile complex conjugate cons
                 consp count defconstant defmacro defparameter defun
                 denominator digit-char-p endp eq eql equal error
                 evenp expt float floatp floor identity if ignore
                 imagpart integerp intern keywordp last length listp
                 logand logandc1 logandc2 logbitp logcount logeqv
                 logior lognand lognor lognot logorc1 logorc2 logtest
                 logxor max member min minusp mod not null numberp
                 numerator oddp open or otherwise pairlis peek-char
                 plusp position progn quote random random-state-p
                 rationalp read-char realpart rem remove return-from
                 reverse round search second set-difference signum
                 string string-append string-downcase string-equal
                 string-upcase string< string<= string> string>=
                 stringp subseq substitute symbol-name symbol-package-name
                 symbolp t the values zerop))"))
      (declare (ignore nb-path))
      (bootstrap-eval-string-full form-str))
  (test-check "defconst completes without TYPE-ERROR"
              (not error-p))
  (when error-p
    (format t "    OUTPUT+BACKTRACE:~%~A~%" out))
  (test-check "defconst does not produce ERROR"
              (not (search "ERROR:" out)))
  ;; Verify the constant is defined
  (let ((val (and (not error-p)
                  (boundp 'acl2::*common-lisp-symbols-from-main-lisp-package*)
                  (symbol-value 'acl2::*common-lisp-symbols-from-main-lisp-package*))))
    (test-check "constant is bound" (not (null val)))
    (test-check "constant is a list" (listp val))
    (when val
      (format t "    constant length: ~D~%" (length val)))))

;;; --- Cell 3: #+acl2-loop-only (defconst nil 'nil) ---
(format t "~%--- Cell 3: defconst nil ---~%")
(multiple-value-bind (out wrld error-p)
    (bootstrap-eval-string-full
      "#+acl2-loop-only
       (defconst nil 'nil)")
  (test-check "defconst nil no error" (not error-p))
  (when error-p
    (format t "    OUTPUT+BACKTRACE:~%~A~%" out))
  (format t "    output: ~S~%" out))

;;; --- Cell 4: #+acl2-loop-only (defconst t 't) ---
(format t "~%--- Cell 4: defconst t ---~%")
(multiple-value-bind (out wrld error-p)
    (bootstrap-eval-string-full
      "#+acl2-loop-only
       (defconst t 't)")
  (test-check "defconst t no error" (not error-p))
  (when error-p
    (format t "    OUTPUT+BACKTRACE:~%~A~%" out))
  (format t "    output: ~S~%" out))

;;; --- Cell 2: defconst *common-lisp-specials-and-constants* ---
(format t "~%--- Cell 2: defconst *common-lisp-specials-and-constants* (abbreviated) ---~%")
(multiple-value-bind (out wrld error-p)
    (bootstrap-eval-string-full
      "(defconst *common-lisp-specials-and-constants*
         '(t nil &allow-other-keys &aux &body &key &optional &rest &whole
           *features* *package* *print-base* *print-case* *print-circle*
           *print-escape* *print-length* *print-level* *print-lines*
           *print-pretty* *print-radix* *print-readably* *print-right-margin*
           *read-base* *readtable* *terminal-io*
           array-dimension-limit boole-1 boole-2 boole-and
           call-arguments-limit char-code-limit
           double-float-epsilon double-float-negative-epsilon
           internal-time-units-per-second lambda-list-keywords
           lambda-parameters-limit least-negative-normalized-double-float
           least-positive-normalized-double-float
           most-negative-fixnum most-negative-long-float
           most-positive-fixnum most-positive-long-float
           multiple-values-limit pi))")
  (test-check "specials-and-constants no error" (not error-p))
  (when error-p
    (format t "    OUTPUT+BACKTRACE:~%~A~%" out))
  (format t "    output: ~S~%" out))

;;; --- Multiple forms in one cell ---
(format t "~%--- Multiple forms in one cell ---~%")
(multiple-value-bind (out wrld error-p)
    (bootstrap-eval-string-full
      "(in-package \"ACL2\")
       #+acl2-loop-only
       (defconst *test-multi-form* '(a b c))")
  (test-check "multi-form no error" (not error-p))
  (when error-p
    (format t "    OUTPUT+BACKTRACE:~%~A~%" out))
  (format t "    output: ~S~%" out))

;;; --- World grows after defconst ---
(format t "~%--- World growth ---~%")
(let ((before (w *the-live-state*))
      (const-name (format nil "*TEST-GROWTH-~A*" (get-universal-time))))
  (multiple-value-bind (out after error-p)
      (bootstrap-eval-string-full
        (format nil "#+acl2-loop-only~%(acl2::defconst acl2::~A 12345)" const-name))
    (test-check "world-growth no error" (not error-p))
    (when error-p
      (format t "    OUTPUT+BACKTRACE:~%~A~%" out))
    (test-check "world grew" (not (eq before after)))
    (when (not (eq before after))
      (let ((diff (ldiff after before)))
        (format t "    world grew by ~D triples~%" (length diff))
        ;; Check that event-landmark is among the new triples
        (let ((has-event (find 'acl2::event-landmark diff
                               :key #'car)))
          (test-check "world has event-landmark" (not (null has-event))))))))


;;; =====================================================================
(format t "~%=== Summary: ~D passed, ~D failed ===~%" *test-pass* *test-fail*)
(sb-ext:exit :code (if (zerop *test-fail*) 0 1))

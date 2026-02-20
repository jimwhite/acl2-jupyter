;;;; Test harness that exercises the kernel's eval pattern directly.
;;;; Run via the same sbcl invocation as start-kernel.sh:
;;;;   sbcl --core saved_acl2.core --load quicklisp/setup.lisp \
;;;;        --eval '(ql:quickload :acl2-jupyter-kernel :silent t)' \
;;;;        --eval '(acl2::sbcl-restart)' < test_kernel_eval.lisp
;;;;
;;;; This uses the kernel's acl2-eval + with-acl2-output-to,
;;;; same as evaluate-code does minus the Jupyter wire protocol.
;;;; Compare results to test_bridge_eval.lisp — must match.

(set-raw-mode-on!)

(in-package "ACL2")

(defvar *test-pass* 0)
(defvar *test-fail* 0)

(defun test-check (name condition)
  (if condition
      (progn (format t "  PASS: ~a~%" name) (incf *test-pass*))
      (progn (format t "  FAIL: ~a~%" name) (incf *test-fail*))))

;;; ---------------------------------------------------------------------------
;;; Kernel-style eval with output capture
;;; ---------------------------------------------------------------------------
(defun kernel-eval-with-output (form)
  "Eval with the kernel's with-acl2-output-to + acl2-eval, returning
   (values result-list output-string)."
  (let ((out (make-string-output-stream)))
    (let ((results
           (acl2-jupyter-kernel::with-acl2-output-to out
             (handler-case
                 (acl2-jupyter-kernel::acl2-eval form)
               (serious-condition (c)
                 (list :error (format nil "~A" c)))))))
      (values results (get-output-stream-string out)))))

;;; ===========================================================================
;;; Tests — identical to test_bridge_eval.lisp
;;; ===========================================================================
(format t "~%=== Kernel Eval Tests ===~%")

;;; --- Arithmetic ---
(format t "~%--- Arithmetic ---~%")
(multiple-value-bind (results output) (kernel-eval-with-output '(+ 1 2))
  (test-check "(+ 1 2) = 3" (equal results '(3))))

(multiple-value-bind (results output) (kernel-eval-with-output '(* 6 7))
  (test-check "(* 6 7) = 42" (equal results '(42))))

(multiple-value-bind (results output) (kernel-eval-with-output '(expt 2 10))
  (test-check "(expt 2 10) = 1024" (equal results '(1024))))

;;; --- Lists ---
(format t "~%--- Lists ---~%")
(multiple-value-bind (results output) (kernel-eval-with-output '(car '(a b c)))
  (test-check "(car '(a b c)) = A" (equal results '(A))))

(multiple-value-bind (results output) (kernel-eval-with-output '(cons 'x '(y z)))
  (test-check "(cons 'x '(y z)) = (X Y Z)" (equal results '((X Y Z)))))

;;; --- defun ---
(format t "~%--- defun ---~%")
(multiple-value-bind (results output) (kernel-eval-with-output '(defun test-double-k (x) (* 2 x)))
  (test-check "defun returns something" (not (null results)))
  (format t "    defun results: ~S~%" results)
  (format t "    defun output: ~S~%" output))

;;; --- call defun ---
(multiple-value-bind (results output) (kernel-eval-with-output '(test-double-k 21))
  (test-check "(test-double-k 21) = 42" (equal results '(42))))

;;; --- defthm ---
(format t "~%--- defthm ---~%")
(multiple-value-bind (results output)
    (kernel-eval-with-output '(defthm test-double-k-is-plus
                                (equal (test-double-k x) (+ x x))))
  (test-check "defthm returns something" (not (null results)))
  (format t "    defthm results: ~S~%" results)
  (format t "    defthm output length: ~D~%" (length output)))

;;; --- defconst ---
(format t "~%--- defconst ---~%")
(multiple-value-bind (results output) (kernel-eval-with-output '(defconst *test-val-k* 99))
  (test-check "defconst returns something" (not (null results)))
  (format t "    defconst results: ~S~%" results))

(multiple-value-bind (results output) (kernel-eval-with-output '*test-val-k*)
  (test-check "*test-val-k* = 99" (equal results '(99))))

;;; --- CW output ---
(format t "~%--- CW Output ---~%")
(multiple-value-bind (results output) (kernel-eval-with-output '(cw "hello from acl2~%"))
  (test-check "cw output captured" (search "hello from acl2" output))
  (format t "    cw results: ~S~%" results)
  (format t "    cw output: ~S~%" output))

(multiple-value-bind (results output) (kernel-eval-with-output '(cw "Sum is ~x0~%" (+ 3 4)))
  (test-check "cw format output has 7" (search "7" output))
  (format t "    cw format results: ~S~%" results)
  (format t "    cw format output: ~S~%" output))

;;; --- Error handling ---
(format t "~%--- Error Handling ---~%")
(multiple-value-bind (results output) (kernel-eval-with-output '(no-such-function-xyz 1 2))
  (test-check "undefined function returns error" (and (consp results) (eq (car results) :error)))
  (format t "    error results: ~S~%" results))

;;; --- After error, still works ---
(multiple-value-bind (results output) (kernel-eval-with-output '(+ 10 20))
  (test-check "(+ 10 20) = 30 after error" (equal results '(30))))

;;; --- include-book ---
(format t "~%--- include-book ---~%")
(multiple-value-bind (results output)
    (kernel-eval-with-output '(include-book "std/lists/append" :dir :system))
  (test-check "include-book doesn't error" (not (and (consp results) (eq (car results) :error))))
  (format t "    include-book results: ~S~%" results)
  (format t "    include-book output length: ~D~%" (length output)))

;;; --- After include-book, still works ---
(multiple-value-bind (results output) (kernel-eval-with-output '(+ 100 200))
  (test-check "(+ 100 200) = 300 after include-book" (equal results '(300))))

;;; ===========================================================================
(format t "~%=== Summary: ~D passed, ~D failed ===~%" *test-pass* *test-fail*)
(quit)

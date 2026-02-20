;;;; Test harness that exercises the Bridge's eval pattern directly.
;;;; Run via: saved_acl2 < test_bridge_eval.lisp
;;;;
;;;; This tests the exact same eval + output-routing that Bridge's
;;;; worker-do-work uses, without any networking.
;;;; If these pass, the same logic will work in the Jupyter kernel.

(include-book "centaur/bridge/top" :dir :system)
(set-raw-mode-on!)

(in-package "ACL2")

(defvar *test-pass* 0)
(defvar *test-fail* 0)

(defun test-check (name condition)
  (if condition
      (progn (format t "  PASS: ~a~%" name) (incf *test-pass*))
      (progn (format t "  FAIL: ~a~%" name) (incf *test-fail*))))

;;; ---------------------------------------------------------------------------
;;; Bridge-style eval: exactly what worker-do-work does
;;; ---------------------------------------------------------------------------
(defun bridge-eval (form)
  "Eval a form the way Bridge's worker-do-work does it."
  (handler-case
      (multiple-value-list
       (eval
        `(let ((state *the-live-state*))
           (declare (ignorable state))
           ,form)))
    (error (condition)
      (list :error (format nil "~A" condition)))))

;;; ---------------------------------------------------------------------------
;;; Bridge-style eval with output capture (with-output-to)
;;; ---------------------------------------------------------------------------
(defun bridge-eval-with-output (form)
  "Eval with Bridge's with-output-to, returning (values result-list output-string)."
  (let ((out (make-string-output-stream)))
    (let ((results (bridge::with-output-to out (bridge-eval form))))
      (values results (get-output-stream-string out)))))

;;; ===========================================================================
;;; Tests
;;; ===========================================================================
(format t "~%=== Bridge Eval Tests ===~%")

;;; --- Arithmetic ---
(format t "~%--- Arithmetic ---~%")
(multiple-value-bind (results output) (bridge-eval-with-output '(+ 1 2))
  (test-check "(+ 1 2) = 3" (equal results '(3))))

(multiple-value-bind (results output) (bridge-eval-with-output '(* 6 7))
  (test-check "(* 6 7) = 42" (equal results '(42))))

(multiple-value-bind (results output) (bridge-eval-with-output '(expt 2 10))
  (test-check "(expt 2 10) = 1024" (equal results '(1024))))

;;; --- Lists ---
(format t "~%--- Lists ---~%")
(multiple-value-bind (results output) (bridge-eval-with-output '(car '(a b c)))
  (test-check "(car '(a b c)) = A" (equal results '(A))))

(multiple-value-bind (results output) (bridge-eval-with-output '(cons 'x '(y z)))
  (test-check "(cons 'x '(y z)) = (X Y Z)" (equal results '((X Y Z)))))

;;; --- defun ---
(format t "~%--- defun ---~%")
(multiple-value-bind (results output) (bridge-eval-with-output '(defun test-double (x) (* 2 x)))
  (test-check "defun returns something" (not (null results)))
  (format t "    defun results: ~S~%" results)
  (format t "    defun output: ~S~%" output))

;;; --- call defun ---
(multiple-value-bind (results output) (bridge-eval-with-output '(test-double 21))
  (test-check "(test-double 21) = 42" (equal results '(42))))

;;; --- defthm ---
(format t "~%--- defthm ---~%")
(multiple-value-bind (results output)
    (bridge-eval-with-output '(defthm test-double-is-plus
                                (equal (test-double x) (+ x x))))
  (test-check "defthm returns something" (not (null results)))
  (format t "    defthm results: ~S~%" results)
  (format t "    defthm output length: ~D~%" (length output)))

;;; --- defconst ---
(format t "~%--- defconst ---~%")
(multiple-value-bind (results output) (bridge-eval-with-output '(defconst *test-val* 99))
  (test-check "defconst returns something" (not (null results)))
  (format t "    defconst results: ~S~%" results))

(multiple-value-bind (results output) (bridge-eval-with-output '*test-val*)
  (test-check "*test-val* = 99" (equal results '(99))))

;;; --- CW output ---
(format t "~%--- CW Output ---~%")
(multiple-value-bind (results output) (bridge-eval-with-output '(cw "hello from acl2~%"))
  (test-check "cw output captured" (search "hello from acl2" output))
  (format t "    cw results: ~S~%" results)
  (format t "    cw output: ~S~%" output))

(multiple-value-bind (results output) (bridge-eval-with-output '(cw "Sum is ~x0~%" (+ 3 4)))
  (test-check "cw format output has 7" (search "7" output))
  (format t "    cw format results: ~S~%" results)
  (format t "    cw format output: ~S~%" output))

;;; --- Error handling ---
(format t "~%--- Error Handling ---~%")
(multiple-value-bind (results output) (bridge-eval-with-output '(no-such-function-xyz 1 2))
  (test-check "undefined function returns error" (and (consp results) (eq (car results) :error)))
  (format t "    error results: ~S~%" results))

;;; --- After error, still works ---
(multiple-value-bind (results output) (bridge-eval-with-output '(+ 10 20))
  (test-check "(+ 10 20) = 30 after error" (equal results '(30))))

;;; --- include-book ---
(format t "~%--- include-book ---~%")
(multiple-value-bind (results output)
    (bridge-eval-with-output '(include-book "std/lists/append" :dir :system))
  (test-check "include-book doesn't error" (not (and (consp results) (eq (car results) :error))))
  (format t "    include-book results: ~S~%" results)
  (format t "    include-book output length: ~D~%" (length output)))

;;; --- After include-book, still works ---
(multiple-value-bind (results output) (bridge-eval-with-output '(+ 100 200))
  (test-check "(+ 100 200) = 300 after include-book" (equal results '(300))))

;;; ===========================================================================
(format t "~%=== Summary: ~D passed, ~D failed ===~%" *test-pass* *test-fail*)
(quit)

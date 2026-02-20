;;; Test include-book in a spawned thread.
;;;
;;; This isolates the thread-safety of include-book from any
;;; Jupyter kernel machinery.
;;;
;;; Usage (pipe to our kernel image which has bordeaux-threads loaded):
;;;   /usr/local/bin/sbcl --control-stack-size 64 \
;;;     --core saved_acl2_jupyter.core \
;;;     --eval '(acl2::sbcl-restart)' \
;;;     < test-include-book-thread.lisp
;;;
;;; Expected: "THREAD-INCLUDE-BOOK: SUCCESS" printed.

;; Exit LP and enter raw mode
(set-raw-mode-on!)

;; Now evaluate our test forms in raw Lisp from within LD

(format t "~%=== Testing include-book in a spawned thread ===~%")
(format t "Current *default-pathname-defaults*: ~A~%" *default-pathname-defaults*)
(format t "project-dir-alist: ~A~%"
        (acl2::f-get-global 'acl2::project-dir-alist acl2::*the-live-state*))
(format t "CBD: ~A~%"
        (acl2::f-get-global 'acl2::connected-book-directory acl2::*the-live-state*))

;; Test 1: include-book in the main thread (raw Lisp, outside LP)
(format t "~%--- Test 1: include-book in main thread (outside LP) ---~%")
(handler-case
    (progn
      (eval '(let ((acl2::state acl2::*the-live-state*))
               (declare (ignorable acl2::state))
               (include-book "std/lists/append" :dir :system)))
      (format t "MAIN-THREAD: SUCCESS~%"))
  (error (c)
    (format t "MAIN-THREAD: ERROR: ~A~%" c))
  (serious-condition (c)
    (format t "MAIN-THREAD: SERIOUS-CONDITION: ~A~%" c)))

;; Test 2: include-book in a spawned thread (like the bridge worker)
(format t "~%--- Test 2: include-book in spawned thread ---~%")
(let ((result nil)
      (done nil))
  (bordeaux-threads:make-thread
   (lambda ()
     (handler-case
         (let ((acl2::*default-hs* (acl2::hl-hspace-init)))
           (eval '(let ((acl2::state acl2::*the-live-state*))
                    (declare (ignorable acl2::state))
                    (include-book "std/lists/append" :dir :system)))
           (setf result :success))
       (error (c)
         (setf result (format nil "ERROR: ~A" c)))
       (serious-condition (c)
         (setf result (format nil "SERIOUS: ~A" c))))
     (setf done t))
   :name "include-book-test")
  ;; Wait for the thread
  (loop until done do (sleep 0.1))
  (format t "THREAD-WITH-HS: ~A~%" result))

;; Test 3: include-book in a spawned thread WITHOUT *default-hs*
(format t "~%--- Test 3: include-book in spawned thread (no *default-hs*) ---~%")
(let ((result nil)
      (done nil))
  (bordeaux-threads:make-thread
   (lambda ()
     (handler-case
         (progn
           (eval '(let ((acl2::state acl2::*the-live-state*))
                    (declare (ignorable acl2::state))
                    (include-book "std/lists/append" :dir :system)))
           (setf result :success))
       (error (c)
         (setf result (format nil "ERROR: ~A" c)))
       (serious-condition (c)
         (setf result (format nil "SERIOUS: ~A" c))))
     (setf done t))
   :name "include-book-test-no-hs")
  ;; Wait for the thread
  (loop until done do (sleep 0.1))
  (format t "THREAD-NO-HS: ~A~%" result))

(format t "~%=== All tests complete ===~%")
(sb-ext:exit :code 0)

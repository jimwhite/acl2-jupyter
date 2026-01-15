; ACL2 Jupyter Kernel - Tests
; Copyright (C) 2026
;
; License: MIT
;
; Tests are defthm forms proven during certification.
; Raw Lisp functions are tested via progn! at load time.

(in-package "ACL2-KERNEL")
(include-book "top")

;;;============================================================================
;;; Tests for connection.lisp
;;;============================================================================

;; Test build-tcp-endpoint produces correct format
(defthm test-build-tcp-endpoint-format
  (equal (build-tcp-endpoint "127.0.0.1" 12345)
         "tcp://127.0.0.1:12345"))

(defthm test-build-tcp-endpoint-localhost
  (equal (build-tcp-endpoint "localhost" 8888)
         "tcp://localhost:8888"))

;; Test build-ipc-endpoint produces correct format  
(defthm test-build-ipc-endpoint-format
  (equal (build-ipc-endpoint "/tmp/kernel.sock")
         "ipc:///tmp/kernel.sock"))

;;;============================================================================
;;; Tests for message.lisp
;;;============================================================================

;; Test string-to-bytes
(defthm test-string-to-bytes-abc
  (equal (string-to-bytes "ABC")
         '(65 66 67)))

(defthm test-string-to-bytes-empty
  (equal (string-to-bytes "")
         nil))

;; Test bytes-to-hex-string
(defthm test-bytes-to-hex-string-basic
  (equal (bytes-to-hex-string '(0 15 255))
         "000fff"))

(defthm test-bytes-to-hex-string-abcd
  (equal (bytes-to-hex-string '(171 205))
         "abcd"))

;; Test make-header returns alist
(defthm test-make-header-is-alist
  (alistp (make-header "id1" "execute_request" "user" "sess" "2026-01-01T00:00:00.000Z")))

;; Test kernel-info-content structure
(defthm test-kernel-info-content-is-alist
  (alistp (kernel-info-content)))

(defthm test-kernel-info-content-status-ok
  (equal (cdr (assoc-equal "status" (kernel-info-content)))
         "ok"))

;; Test execute-reply-ok structure
(defthm test-execute-reply-ok-is-alist
  (alistp (execute-reply-ok 1)))

(defthm test-execute-reply-ok-status
  (equal (cdr (assoc-equal "status" (execute-reply-ok 1)))
         "ok"))

(defthm test-execute-reply-ok-count
  (equal (cdr (assoc-equal "execution_count" (execute-reply-ok 5)))
         5))

;;;============================================================================
;;; Tests for kernel.lisp  
;;;============================================================================

;; Test make-kernel-state
(defthm test-make-kernel-state-is-alist
  (alistp (make-kernel-state "sess-123" "key-456" nil)))

(defthm test-kernel-state-session-accessor
  (equal (kernel-state-session (make-kernel-state "sess-123" "key" nil))
         "sess-123"))

(defthm test-kernel-state-initial-execution-count
  (equal (kernel-state-execution-count (make-kernel-state "sess" "key" nil))
         0))

;; Test increment-execution-count
(defthm test-increment-execution-count
  (equal (kernel-state-execution-count 
          (increment-execution-count (make-kernel-state "s" "k" nil)))
         1))

;; Test message type predicates
(defthm test-shell-message-type-execute
  (shell-message-type-p "execute_request"))

(defthm test-shell-message-type-kernel-info
  (shell-message-type-p "kernel_info_request"))

(defthm test-shell-message-type-unknown
  (not (shell-message-type-p "unknown_request")))

(defthm test-control-message-type-shutdown
  (control-message-type-p "shutdown_request"))

(defthm test-control-message-type-interrupt
  (control-message-type-p "interrupt_request"))

;; Test execute-request accessors
(defthm test-execute-request-code
  (equal (execute-request-code '(("code" . "(+ 1 2)")))
         "(+ 1 2)"))

(defthm test-execute-request-code-missing
  (equal (execute-request-code '(("other" . "x")))
         ""))

(defthm test-execute-request-silent-true
  (execute-request-silent-p '(("silent" . t))))

(defthm test-execute-request-silent-false
  (not (execute-request-silent-p '(("silent" . nil)))))

;; Test reply construction
(defthm test-make-execute-reply-ok-status
  (equal (cdr (assoc-equal "status" (make-execute-reply-ok 1)))
         "ok"))

(defthm test-make-execute-reply-ok-count
  (equal (cdr (assoc-equal "execution_count" (make-execute-reply-ok 5)))
         5))

(defthm test-make-execute-reply-error-status
  (equal (cdr (assoc-equal "status" (make-execute-reply-error 1 "E" "msg" nil)))
         "error"))

;; Test reply-message-type mapping
(defthm test-reply-message-type-kernel-info
  (equal (reply-message-type "kernel_info_request")
         "kernel_info_reply"))

(defthm test-reply-message-type-execute
  (equal (reply-message-type "execute_request")
         "execute_reply"))

(defthm test-reply-message-type-shutdown
  (equal (reply-message-type "shutdown_request")
         "shutdown_reply"))

;;;============================================================================
;;; Tests for Raw Lisp Functions (run at load time)
;;;============================================================================

;; Need ttag for progn! with raw mode
(defttag :acl2-kernel-tests)

;; These tests run in raw Lisp mode during book loading
(progn!
 (set-raw-mode t)
 
 ;; Test HMAC with empty key returns empty string
 (assert (equal (hmac-sign-raw "" "test data") ""))
 
 ;; Test HMAC with nil key returns empty string  
 (assert (equal (hmac-sign-raw nil "test data") ""))
 
 ;; Test HMAC produces correct output
 ;; Verified: printf 'test message' | openssl dgst -sha256 -hmac 'secret-key'
 (assert (equal (hmac-sign-raw "secret-key" "test message")
                "9a0eb7d4647a82cf2785df52d1e605fb531beb1f270c8215c8ffb3ff31a993b4"))
 
 ;; Test HMAC with multiple message parts (concatenated)
 ;; Verified: printf 'helloworld' | openssl dgst -sha256 -hmac 'key'
 (assert (equal (hmac-sign-raw "key" "hello" "world")
                "90ad356894b519def4f954aab2a2c14d7cc64ab70a0f7ba0b8c31d3f2f1fb251"))
 
 ;; Test UUID generation
 (assert (stringp (make-uuid)))
 (assert (eql (length (make-uuid)) 36))
 (assert (not (equal (make-uuid) (make-uuid))))
 
 ;; Test ISO8601 formatting
 (assert (stringp (iso8601-now)))
 (assert (eql (length (iso8601-now)) 27))
 
 ;; Test JSON encoding with hash-table
 (let ((ht (make-hash-table :test #'equal)))
   (setf (gethash "key" ht) "value")
   (assert (stringp (json-encode ht))))
 
 ;; Test connection file parser
 (let ((test-file "/tmp/acl2-kernel-test-conn.json"))
   (with-open-file (out test-file :direction :output :if-exists :supersede)
     (format out "{\"transport\":\"tcp\",\"ip\":\"127.0.0.1\",\"shell_port\":12345,\"key\":\"test-key\"}"))
   (let ((conn (parse-connection-file test-file)))
     (assert (equal (gethash "transport" conn) "tcp"))
     (assert (equal (gethash "ip" conn) "127.0.0.1"))
     (assert (equal (gethash "shell_port" conn) 12345))
     (assert (equal (gethash "key" conn) "test-key")))
   (delete-file test-file))
 
 (format t "~%; All raw Lisp tests passed.~%"))

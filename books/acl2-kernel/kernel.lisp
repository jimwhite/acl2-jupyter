; ACL2 Jupyter Kernel - Kernel Logic
; Copyright (C) 2026
;
; License: MIT
;
; This book defines:
; - Kernel state representation
; - Message dispatch logic
; - Request handlers (pure logic portions)
;
; Raw Lisp runtime (ZeroMQ, threading, I/O) is in kernel-raw.lsp

(in-package "ACL2-KERNEL")

(include-book "connection")
(include-book "message")
(include-book "std/util/define" :dir :system)
(include-book "std/alists/put-assoc-equal" :dir :system)
(local (include-book "std/testing/assert-bang" :dir :system))

;;;============================================================================
;;; Kernel State
;;;============================================================================

;; Kernel state is an alist with the following keys:
;; - session: string (UUID for this kernel session)
;; - execution-count: natp (incremented per execute_request)
;; - username: string (from connection file or default)
;; - hmac-key: string (HMAC signing key from connection file)
;; - connection: alist (parsed connection file)

(define make-kernel-state ((session stringp)
                           (hmac-key stringp)
                           (connection alistp))
  :returns (state alistp)
  :short "Create initial kernel state"
  (list (cons 'session session)
        (cons 'execution-count 0)
        (cons 'username "acl2-kernel")
        (cons 'hmac-key hmac-key)
        (cons 'connection connection)))

(define kernel-state-session ((kstate alistp))
  :returns (session stringp :hyp :guard)
  :short "Get session ID from kernel state"
  (let ((pair (assoc 'session kstate)))
    (if (and pair (stringp (cdr pair)))
        (cdr pair)
      "")))

(define kernel-state-execution-count ((kstate alistp))
  :returns (count natp :hyp :guard)
  :short "Get execution count from kernel state"
  (let ((pair (assoc 'execution-count kstate)))
    (if (and pair (natp (cdr pair)))
        (cdr pair)
      0)))

(define kernel-state-username ((kstate alistp))
  :returns (username stringp :hyp :guard)
  :short "Get username from kernel state"
  (let ((pair (assoc 'username kstate)))
    (if (and pair (stringp (cdr pair)))
        (cdr pair)
      "acl2-kernel")))

(define kernel-state-hmac-key ((kstate alistp))
  :returns (key stringp :hyp :guard)
  :short "Get HMAC key from kernel state"
  (let ((pair (assoc 'hmac-key kstate)))
    (if (and pair (stringp (cdr pair)))
        (cdr pair)
      "")))

(define increment-execution-count ((kstate alistp))
  :returns (new-state alistp :hyp :guard
                      :hints (("Goal" :in-theory (enable put-assoc-equal))))
  :short "Increment execution count in kernel state"
  (let ((count (kernel-state-execution-count kstate)))
    (put-assoc 'execution-count (+ 1 count) kstate)))

;;;============================================================================
;;; Message Type Recognition
;;;============================================================================

;; Jupyter message types we handle
(defconst *shell-message-types*
  '("kernel_info_request"
    "execute_request"
    "complete_request"
    "inspect_request"
    "history_request"
    "is_complete_request"
    "comm_info_request"
    "shutdown_request"))

(defconst *control-message-types*
  '("shutdown_request"
    "interrupt_request"
    "debug_request"))

(define shell-message-type-p ((msg-type stringp))
  :returns (b booleanp)
  :short "Recognize a shell channel message type"
  (if (member-equal msg-type *shell-message-types*) t nil))

(define control-message-type-p ((msg-type stringp))
  :returns (b booleanp)
  :short "Recognize a control channel message type"
  (if (member-equal msg-type *control-message-types*) t nil))

;;;============================================================================
;;; Request Content Extraction
;;;============================================================================

;; Extract code from execute_request content
(define execute-request-code ((content alistp))
  :returns (code stringp)
  :short "Extract code string from execute_request content"
  (let ((pair (assoc-equal "code" content)))
    (if (and pair (stringp (cdr pair)))
        (cdr pair)
      "")))

(define execute-request-silent-p ((content alistp))
  :returns (b booleanp)
  :short "Check if execute_request is silent"
  (let ((pair (assoc-equal "silent" content)))
    (and pair (eq (cdr pair) t))))

(define execute-request-store-history-p ((content alistp))
  :returns (b booleanp)
  :short "Check if execute_request should store history"
  (let ((pair (assoc-equal "store_history" content)))
    (or (not pair)  ; default to true
        (eq (cdr pair) t))))

;;;============================================================================
;;; Response Generation
;;;============================================================================

;; Generate execute_reply content for successful execution
(define make-execute-reply-ok ((execution-count natp))
  :returns (content alistp)
  :short "Create execute_reply content for success"
  (list (cons "status" "ok")
        (cons "execution_count" execution-count)
        (cons "payload" nil)
        (cons "user_expressions" nil)))

;; Generate execute_reply content for error
(define make-execute-reply-error ((execution-count natp)
                                  (ename stringp)
                                  (evalue stringp)
                                  (traceback string-listp))
  :returns (content alistp)
  :short "Create execute_reply content for error"
  (list (cons "status" "error")
        (cons "execution_count" execution-count)
        (cons "ename" ename)
        (cons "evalue" evalue)
        (cons "traceback" traceback)))

;; Generate shutdown_reply content
(define make-shutdown-reply ((restart booleanp))
  :returns (content alistp)
  :short "Create shutdown_reply content"
  (list (cons "restart" restart)
        (cons "status" "ok")))

;; Generate is_complete_reply content
(define make-is-complete-reply ((status stringp))
  :returns (content alistp)
  :guard (member-equal status '("complete" "incomplete" "invalid" "unknown"))
  :short "Create is_complete_reply content"
  (if (equal status "incomplete")
      (list (cons "status" status)
            (cons "indent" "  "))  ; 2-space indent for continuation
    (list (cons "status" status))))

;;;============================================================================
;;; IOPub Message Content
;;;============================================================================

;; Status message content
(define make-status-content ((execution-state stringp))
  :returns (content alistp)
  :guard (member-equal execution-state '("busy" "idle" "starting"))
  :short "Create status message content"
  (list (cons "execution_state" execution-state)))

;; Stream message content (stdout/stderr)
(define make-stream-content ((stream-name stringp) (text stringp))
  :returns (content alistp)
  :guard (member-equal stream-name '("stdout" "stderr"))
  :short "Create stream message content"
  (list (cons "name" stream-name)
        (cons "text" text)))

;; Execute result content
(define make-execute-result-content ((execution-count natp)
                                     (text-plain stringp))
  :returns (content alistp)
  :short "Create execute_result message content"
  (list (cons "execution_count" execution-count)
        (cons "data" (list (cons "text/plain" text-plain)))
        (cons "metadata" nil)))

;; Error message content
(define make-error-content ((ename stringp)
                            (evalue stringp)
                            (traceback string-listp))
  :returns (content alistp)
  :short "Create error message content"
  (list (cons "ename" ename)
        (cons "evalue" evalue)
        (cons "traceback" traceback)))

;;;============================================================================
;;; Message Dispatch (Pure Logic)
;;;============================================================================

;; Determine reply message type from request type
(define reply-message-type ((request-type stringp))
  :returns (reply-type stringp)
  :short "Get reply message type for a request type"
  (cond ((equal request-type "kernel_info_request") "kernel_info_reply")
        ((equal request-type "execute_request") "execute_reply")
        ((equal request-type "complete_request") "complete_reply")
        ((equal request-type "inspect_request") "inspect_reply")
        ((equal request-type "history_request") "history_reply")
        ((equal request-type "is_complete_request") "is_complete_reply")
        ((equal request-type "comm_info_request") "comm_info_reply")
        ((equal request-type "shutdown_request") "shutdown_reply")
        ((equal request-type "interrupt_request") "interrupt_reply")
        (t "error")))

;;;============================================================================
;;; Tests
;;;============================================================================

(local
 (progn
   ;; Test kernel state
   (assert! (alistp (make-kernel-state "sess-123" "key-456" nil)))
   (assert! (equal (kernel-state-session (make-kernel-state "sess-123" "key" nil))
                   "sess-123"))
   (assert! (equal (kernel-state-execution-count (make-kernel-state "sess" "key" nil))
                   0))

   ;; Test increment
   (assert! (equal (kernel-state-execution-count 
                    (increment-execution-count (make-kernel-state "sess" "key" nil)))
                   1))

   ;; Test message types
   (assert! (shell-message-type-p "execute_request"))
   (assert! (shell-message-type-p "kernel_info_request"))
   (assert! (not (shell-message-type-p "unknown_request")))
   (assert! (control-message-type-p "shutdown_request"))
   (assert! (control-message-type-p "interrupt_request"))

   ;; Test execute request extraction
   (assert! (equal (execute-request-code '(("code" . "(+ 1 2)"))) "(+ 1 2)"))
   (assert! (equal (execute-request-code '(("other" . "x"))) ""))
   (assert! (execute-request-silent-p '(("silent" . t))))
   (assert! (not (execute-request-silent-p '(("silent" . nil)))))

   ;; Test reply generation
   (assert! (equal (cdr (assoc-equal "status" (make-execute-reply-ok 1))) "ok"))
   (assert! (equal (cdr (assoc-equal "execution_count" (make-execute-reply-ok 5))) 5))
   (assert! (equal (cdr (assoc-equal "status" (make-execute-reply-error 1 "E" "msg" nil))) "error"))

   ;; Test reply type mapping
   (assert! (equal (reply-message-type "kernel_info_request") "kernel_info_reply"))
   (assert! (equal (reply-message-type "execute_request") "execute_reply"))
   (assert! (equal (reply-message-type "shutdown_request") "shutdown_reply"))))

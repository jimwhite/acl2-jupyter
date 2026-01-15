; ACL2 Jupyter Kernel - Raw Lisp Runtime
; Copyright (C) 2026
;
; License: MIT
;
; This file contains raw Common Lisp code for:
; - UUID generation
; - ZeroMQ socket management 
; - Threading and event loop
; - Output capture
;
; Loaded via include-raw in top.lisp

(in-package "ACL2-KERNEL")

;;;============================================================================
;;; Dependencies (loaded at runtime)
;;;============================================================================

;; These are loaded via Quicklisp at kernel startup
;; - pzmq (ZeroMQ bindings)
;; - bordeaux-threads (threading)
;; - babel (string/octets conversion)

;;;============================================================================
;;; UUID Generation
;;;============================================================================

(defparameter *uuid-random-state* (make-random-state t)
  "Random state seeded from OS entropy for UUID generation.")

(defun make-uuid ()
  "Generate a UUID v4 string (xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx)."
  (let ((bytes (make-array 16 :element-type '(unsigned-byte 8))))
    ;; Fill with random bytes
    (dotimes (i 16)
      (setf (aref bytes i)
            (cond
              ;; Byte 6: version 4 = 0100xxxx
              ((= i 6) (logior #x40 (random 16 *uuid-random-state*)))
              ;; Byte 8: variant 1 = 10xxxxxx
              ((= i 8) (logior #x80 (random 64 *uuid-random-state*)))
              ;; All other bytes: random 0-255
              (t (random 256 *uuid-random-state*)))))
    ;; Format as UUID string
    (format nil "~(~8,'0x-~4,'0x-~4,'0x-~4,'0x-~12,'0x~)"
            (logior (ash (aref bytes 0) 24)
                    (ash (aref bytes 1) 16)
                    (ash (aref bytes 2) 8)
                    (aref bytes 3))
            (logior (ash (aref bytes 4) 8)
                    (aref bytes 5))
            (logior (ash (aref bytes 6) 8)
                    (aref bytes 7))
            (logior (ash (aref bytes 8) 8)
                    (aref bytes 9))
            (logior (ash (aref bytes 10) 40)
                    (ash (aref bytes 11) 32)
                    (ash (aref bytes 12) 24)
                    (ash (aref bytes 13) 16)
                    (ash (aref bytes 14) 8)
                    (aref bytes 15)))))

(defun reinitialize-uuid-random-state ()
  "Reinitialize UUID random state from OS entropy."
  (setf *uuid-random-state* (make-random-state t)))

;;;============================================================================
;;; Date/Time Formatting
;;;============================================================================

(defun iso8601-now ()
  "Return current time in ISO 8601 format for Jupyter messages."
  (multiple-value-bind (sec min hour day month year)
      (get-decoded-time)
    (format nil "~4,'0d-~2,'0d-~2,'0dT~2,'0d:~2,'0d:~2,'0d.000000Z"
            year month day hour min sec)))

;;;============================================================================
;;; ZeroMQ Socket Management
;;;============================================================================

(defparameter *zmq-context* nil
  "ZeroMQ context (shared by all sockets)")

(defparameter *shell-socket* nil)
(defparameter *control-socket* nil)
(defparameter *iopub-socket* nil)
(defparameter *stdin-socket* nil)
(defparameter *heartbeat-socket* nil)

(defun init-zmq-context ()
  "Initialize the ZeroMQ context."
  (setf *zmq-context* (pzmq:ctx-new)))

(defun cleanup-zmq-context ()
  "Cleanup the ZeroMQ context."
  (when *zmq-context*
    (pzmq:ctx-destroy *zmq-context*)
    (setf *zmq-context* nil)))

(defun make-endpoint (transport ip port)
  "Create a ZeroMQ endpoint string.
   For IPC: ipc:///path/to/socket
   For TCP: tcp://ip:port"
  (if (string= transport "ipc")
      (format nil "ipc://~A" port)  ; port is actually the socket path for IPC
    (format nil "tcp://~A:~A" ip port)))

(defun create-sockets (connection)
  "Create all ZeroMQ sockets from connection info.
   CONNECTION is an alist from parse-connection-file."
  (let ((transport (or (cdr (assoc-equal "transport" connection)) "tcp"))
        (ip (or (cdr (assoc-equal "ip" connection)) "127.0.0.1")))
    ;; Shell socket (ROUTER for bidirectional request/reply)
    (setf *shell-socket* (pzmq:socket *zmq-context* :router))
    (pzmq:bind *shell-socket* 
               (make-endpoint transport ip 
                              (cdr (assoc-equal "shell_port" connection))))
    
    ;; Control socket (ROUTER, higher priority than shell)
    (setf *control-socket* (pzmq:socket *zmq-context* :router))
    (pzmq:bind *control-socket*
               (make-endpoint transport ip
                              (cdr (assoc-equal "control_port" connection))))
    
    ;; IOPub socket (PUB for broadcasting to all frontends)
    (setf *iopub-socket* (pzmq:socket *zmq-context* :pub))
    (pzmq:bind *iopub-socket*
               (make-endpoint transport ip
                              (cdr (assoc-equal "iopub_port" connection))))
    
    ;; Stdin socket (ROUTER for input requests)
    (setf *stdin-socket* (pzmq:socket *zmq-context* :router))
    (pzmq:bind *stdin-socket*
               (make-endpoint transport ip
                              (cdr (assoc-equal "stdin_port" connection))))
    
    ;; Heartbeat socket (REP for echo)
    (setf *heartbeat-socket* (pzmq:socket *zmq-context* :rep))
    (pzmq:bind *heartbeat-socket*
               (make-endpoint transport ip
                              (cdr (assoc-equal "hb_port" connection))))))

(defun close-sockets ()
  "Close all ZeroMQ sockets."
  (when *shell-socket* (pzmq:close *shell-socket*) (setf *shell-socket* nil))
  (when *control-socket* (pzmq:close *control-socket*) (setf *control-socket* nil))
  (when *iopub-socket* (pzmq:close *iopub-socket*) (setf *iopub-socket* nil))
  (when *stdin-socket* (pzmq:close *stdin-socket*) (setf *stdin-socket* nil))
  (when *heartbeat-socket* (pzmq:close *heartbeat-socket*) (setf *heartbeat-socket* nil)))

;;;============================================================================
;;; Message Wire Protocol
;;;============================================================================

(defparameter +ids-msg-delimiter+ "<IDS|MSG>"
  "Delimiter separating identities from message content in wire protocol")

(defun recv-multipart (socket)
  "Receive a multipart message from a ZeroMQ socket.
   Returns a list of byte vectors."
  (let ((parts nil))
    (loop
      (let ((msg (pzmq:recv-string socket)))
        (push msg parts))
      (unless (pzmq:getsockopt socket :rcvmore)
        (return)))
    (nreverse parts)))

(defun send-multipart (socket parts)
  "Send a multipart message to a ZeroMQ socket.
   PARTS is a list of strings."
  (loop for (part . rest) on parts
        do (pzmq:send socket part :sndmore (not (null rest)))))

(defun parse-wire-message (parts)
  "Parse a wire protocol message into components.
   Returns: (values identities signature header parent-header metadata content)"
  (let ((delim-pos (position +ids-msg-delimiter+ parts :test #'string=)))
    (if delim-pos
        (let ((identities (subseq parts 0 delim-pos))
              (rest (subseq parts (1+ delim-pos))))
          (when (>= (length rest) 5)
            (values identities
                    (nth 0 rest)  ; signature (HMAC hex)
                    (nth 1 rest)  ; header JSON
                    (nth 2 rest)  ; parent_header JSON
                    (nth 3 rest)  ; metadata JSON
                    (nth 4 rest)))) ; content JSON
      (values nil nil nil nil nil nil))))

(defun build-wire-message (identities signature header parent-header metadata content)
  "Build a wire protocol message from components.
   Returns a list of strings for send-multipart."
  (append identities
          (list +ids-msg-delimiter+
                signature
                header
                parent-header
                metadata
                content)))

;;;============================================================================
;;; Kernel State (Runtime)
;;;============================================================================

(defparameter *kernel-state* nil
  "Current kernel state alist")

(defparameter *kernel-running* nil
  "Flag indicating kernel is running")

(defparameter *execution-count* 0
  "Execution counter (incremented per execute_request)")

(defparameter *session-id* nil
  "Kernel session UUID")

(defparameter *hmac-key* nil
  "HMAC signing key from connection file")

;;;============================================================================
;;; Heartbeat Handler
;;;============================================================================

(defparameter *heartbeat-thread* nil
  "Thread running the heartbeat responder")

(defun heartbeat-loop ()
  "Heartbeat responder loop - echoes messages back."
  (loop while *kernel-running*
        do (handler-case
               (let ((msg (pzmq:recv-string *heartbeat-socket* :dontwait t)))
                 (when msg
                   (pzmq:send *heartbeat-socket* msg)))
             (pzmq:eagain () 
               ;; No message available, sleep briefly
               (sleep 0.01)))))

(defun start-heartbeat-thread ()
  "Start the heartbeat responder in a background thread."
  (setf *heartbeat-thread*
        (bordeaux-threads:make-thread #'heartbeat-loop
                                       :name "jupyter-heartbeat")))

(defun stop-heartbeat-thread ()
  "Stop the heartbeat responder thread."
  (when (and *heartbeat-thread*
             (bordeaux-threads:thread-alive-p *heartbeat-thread*))
    (bordeaux-threads:destroy-thread *heartbeat-thread*)
    (setf *heartbeat-thread* nil)))

;;;============================================================================
;;; Output Capture
;;;============================================================================

(defparameter *captured-output* nil
  "String stream for capturing stdout during execution")

(defmacro with-output-capture (&body body)
  "Execute BODY with stdout captured to *captured-output*."
  `(let ((*captured-output* (make-string-output-stream)))
     (let ((*standard-output* *captured-output*)
           (*error-output* *captured-output*))
       ,@body)))

(defun get-captured-output ()
  "Get the captured output as a string."
  (when *captured-output*
    (get-output-stream-string *captured-output*)))

;;;============================================================================
;;; IOPub Publishing
;;;============================================================================

(defun publish-status (status parent-header)
  "Publish a status message (busy/idle) on IOPub."
  (let* ((header-json (bridge::json-encode 
                       (make-header (make-uuid) "status" 
                                    "acl2-kernel" *session-id* (iso8601-now))))
         (content-json (bridge::json-encode (make-status-content status)))
         (signature (message-signature *hmac-key* header-json parent-header "{}" content-json)))
    (send-multipart *iopub-socket*
                    (build-wire-message nil signature header-json parent-header "{}" content-json))))

(defun publish-stream (stream-name text parent-header)
  "Publish a stream message (stdout/stderr) on IOPub."
  (when (and text (> (length text) 0))
    (let* ((header-json (bridge::json-encode
                         (make-header (make-uuid) "stream"
                                      "acl2-kernel" *session-id* (iso8601-now))))
           (content-json (bridge::json-encode (make-stream-content stream-name text)))
           (signature (message-signature *hmac-key* header-json parent-header "{}" content-json)))
      (send-multipart *iopub-socket*
                      (build-wire-message nil signature header-json parent-header "{}" content-json)))))

(defun publish-execute-result (execution-count text-result parent-header)
  "Publish an execute_result message on IOPub."
  (let* ((header-json (bridge::json-encode
                       (make-header (make-uuid) "execute_result"
                                    "acl2-kernel" *session-id* (iso8601-now))))
         (content-json (bridge::json-encode (make-execute-result-content execution-count text-result)))
         (signature (message-signature *hmac-key* header-json parent-header "{}" content-json)))
    (send-multipart *iopub-socket*
                    (build-wire-message nil signature header-json parent-header "{}" content-json))))

(defun publish-error (ename evalue traceback parent-header)
  "Publish an error message on IOPub."
  (let* ((header-json (bridge::json-encode
                       (make-header (make-uuid) "error"
                                    "acl2-kernel" *session-id* (iso8601-now))))
         (content-json (bridge::json-encode (make-error-content ename evalue traceback)))
         (signature (message-signature *hmac-key* header-json parent-header "{}" content-json)))
    (send-multipart *iopub-socket*
                    (build-wire-message nil signature header-json parent-header "{}" content-json))))

;;;============================================================================
;;; Request Handlers
;;;============================================================================

(defun handle-kernel-info-request (identities parent-header)
  "Handle kernel_info_request, send kernel_info_reply."
  (let* ((header-json (bridge::json-encode
                       (make-header (make-uuid) "kernel_info_reply"
                                    "acl2-kernel" *session-id* (iso8601-now))))
         (content-json (bridge::json-encode (kernel-info-content)))
         (signature (message-signature *hmac-key* header-json parent-header "{}" content-json)))
    (send-multipart *shell-socket*
                    (build-wire-message identities signature header-json parent-header "{}" content-json))))

(defun handle-execute-request (identities parent-header content-json)
  "Handle execute_request, evaluate code and send replies."
  ;; Parse the content
  (multiple-value-bind (erp content)
      (acl2::parse-json content-json)
    (declare (ignore erp))
    (let* ((code (execute-request-code content))
           (silent (execute-request-silent-p content)))
      ;; Increment execution count
      (incf *execution-count*)
      
      ;; Publish busy status
      (publish-status "busy" parent-header)
      
      ;; Execute the code
      (let ((result nil)
            (error-info nil)
            (output ""))
        (handler-case
            (with-output-capture
              ;; TODO: Actually evaluate in ACL2
              ;; For now, just echo the code
              (setf result (format nil "~S" (read-from-string code)))
              (setf output (get-captured-output)))
          (error (e)
            (setf error-info (list (type-of e)
                                   (format nil "~A" e)
                                   nil))))
        
        ;; Publish stdout if any
        (publish-stream "stdout" output parent-header)
        
        (if error-info
            (progn
              ;; Publish error
              (publish-error (format nil "~A" (first error-info))
                             (second error-info)
                             (third error-info)
                             parent-header)
              ;; Send error reply
              (let* ((header-json (bridge::json-encode
                                   (make-header (make-uuid) "execute_reply"
                                                "acl2-kernel" *session-id* (iso8601-now))))
                     (content-json (bridge::json-encode
                                    (make-execute-reply-error *execution-count*
                                                              (format nil "~A" (first error-info))
                                                              (second error-info)
                                                              nil)))
                     (signature (message-signature *hmac-key* header-json parent-header "{}" content-json)))
                (send-multipart *shell-socket*
                                (build-wire-message identities signature header-json parent-header "{}" content-json))))
            (progn
              ;; Publish result (unless silent)
              (unless silent
                (publish-execute-result *execution-count* result parent-header))
              ;; Send OK reply
              (let* ((header-json (bridge::json-encode
                                   (make-header (make-uuid) "execute_reply"
                                                "acl2-kernel" *session-id* (iso8601-now))))
                     (content-json (bridge::json-encode (make-execute-reply-ok *execution-count*)))
                     (signature (message-signature *hmac-key* header-json parent-header "{}" content-json)))
                (send-multipart *shell-socket*
                                (build-wire-message identities signature header-json parent-header "{}" content-json))))))
      
      ;; Publish idle status
      (publish-status "idle" parent-header))))

(defun handle-shutdown-request (identities parent-header content-json)
  "Handle shutdown_request, send reply and stop kernel."
  (multiple-value-bind (erp content)
      (acl2::parse-json content-json)
    (declare (ignore erp))
    (let* ((restart (and (assoc-equal "restart" content)
                         (eq (cdr (assoc-equal "restart" content)) t)))
           (header-json (bridge::json-encode
                         (make-header (make-uuid) "shutdown_reply"
                                      "acl2-kernel" *session-id* (iso8601-now))))
           (content-json (bridge::json-encode (make-shutdown-reply restart)))
           (signature (message-signature *hmac-key* header-json parent-header "{}" content-json)))
      ;; Send reply
      (send-multipart *shell-socket*
                      (build-wire-message identities signature header-json parent-header "{}" content-json))
      ;; Stop the kernel
      (setf *kernel-running* nil))))

;;;============================================================================
;;; Message Dispatch
;;;============================================================================

(defun dispatch-message (socket)
  "Receive and dispatch a message from SOCKET."
  (let ((parts (recv-multipart socket)))
    (multiple-value-bind (identities signature header-json parent-json metadata-json content-json)
        (parse-wire-message parts)
      (when header-json
        ;; Parse header to get msg_type
        (multiple-value-bind (erp header)
            (acl2::parse-json header-json)
          (declare (ignore erp))
          (let ((msg-type (cdr (assoc-equal "msg_type" header))))
            ;; TODO: Verify HMAC signature
            (cond
              ((string= msg-type "kernel_info_request")
               (handle-kernel-info-request identities header-json))
              ((string= msg-type "execute_request")
               (handle-execute-request identities header-json content-json))
              ((string= msg-type "shutdown_request")
               (handle-shutdown-request identities header-json content-json))
              ;; Add more handlers as needed
              (t
               (format t "~&Unknown message type: ~A~%" msg-type)))))))))

;;;============================================================================
;;; Main Event Loop
;;;============================================================================

(defun kernel-main-loop ()
  "Main event loop - poll sockets and dispatch messages."
  (loop while *kernel-running*
        do (handler-case
               (progn
                 ;; Check control socket (higher priority)
                 (when (pzmq:getsockopt *control-socket* :events)
                   (dispatch-message *control-socket*))
                 ;; Check shell socket
                 (when (pzmq:getsockopt *shell-socket* :events)
                   (dispatch-message *shell-socket*))
                 ;; Brief sleep to avoid busy-waiting
                 (sleep 0.001))
             (error (e)
               (format t "~&Error in main loop: ~A~%" e)))))

;;;============================================================================
;;; Kernel Entry Point
;;;============================================================================

(defun start-kernel (connection-file-path)
  "Start the ACL2 Jupyter kernel.
   CONNECTION-FILE-PATH is the path to the Jupyter connection file."
  ;; Parse connection file
  (let ((connection (parse-connection-file connection-file-path)))
    (unless connection
      (error "Failed to parse connection file: ~A" connection-file-path))
    
    ;; Initialize state
    (setf *session-id* (make-uuid))
    (setf *hmac-key* (or (cdr (assoc-equal "key" connection)) ""))
    (setf *execution-count* 0)
    (setf *kernel-running* t)
    
    ;; Initialize ZeroMQ
    (init-zmq-context)
    (create-sockets connection)
    
    ;; Start heartbeat thread
    (start-heartbeat-thread)
    
    (format t "~&ACL2 Jupyter Kernel started~%")
    (format t "Session: ~A~%" *session-id*)
    
    ;; Run main loop
    (unwind-protect
        (kernel-main-loop)
      ;; Cleanup
      (stop-heartbeat-thread)
      (close-sockets)
      (cleanup-zmq-context)
      (format t "~&ACL2 Jupyter Kernel stopped~%"))))

;;;============================================================================
;;; Command-line Entry Point
;;;============================================================================

(defun main ()
  "Command-line entry point for the kernel."
  (let ((args (uiop:command-line-arguments)))
    (cond
      ((null args)
       (format t "Usage: acl2-kernel <connection-file>~%")
       (uiop:quit 1))
      (t
       (start-kernel (first args))))))

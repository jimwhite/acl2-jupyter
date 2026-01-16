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
; - HMAC signing (using OpenSSL)
;
; Following the pattern from centaur/bridge/bridge-sbcl-raw.lsp
;
; Loaded via include-raw in top.lisp

(in-package "ACL2-KERNEL")

;;;============================================================================
;;; Debug Configuration
;;;============================================================================

(defvar *kernel-debug* nil
  "When true, enable verbose debug output.")

(defmacro debug-log (fmt &rest args)
  "Print debug message if *kernel-debug* is true."
  `(when *kernel-debug*
     (format t ,fmt ,@args)
     (force-output)))

;;;============================================================================
;;; Dependencies
;;;============================================================================

;; pzmq and bordeaux-threads are loaded via ACL2 quicklisp books
;; Load shasht for JSON parsing/encoding (same as common-lisp-jupyter)
(ql:quickload "shasht" :silent t)

;;;============================================================================
;;; Connection File Parser (Pure Common Lisp)
;;;============================================================================

(defun parse-connection-file (path)
  "Parse a Jupyter connection file and return a hash-table.
   Uses shasht for JSON parsing (same as common-lisp-jupyter)."
  (let ((content (uiop:read-file-string path)))
    (shasht:read-json content)))

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
   CONNECTION is a hash-table from parse-connection-file."
  (let ((transport (or (gethash "transport" connection) "tcp"))
        (ip (or (gethash "ip" connection) "127.0.0.1")))
    ;; Shell socket (ROUTER for bidirectional request/reply)
    (setf *shell-socket* (pzmq:socket *zmq-context* :router))
    (pzmq:bind *shell-socket* 
               (make-endpoint transport ip 
                              (gethash "shell_port" connection)))
    
    ;; Control socket (ROUTER, higher priority than shell)
    (setf *control-socket* (pzmq:socket *zmq-context* :router))
    (pzmq:bind *control-socket*
               (make-endpoint transport ip
                              (gethash "control_port" connection)))
    
    ;; IOPub socket (PUB for broadcasting to all frontends)
    (setf *iopub-socket* (pzmq:socket *zmq-context* :pub))
    (pzmq:bind *iopub-socket*
               (make-endpoint transport ip
                              (gethash "iopub_port" connection)))
    
    ;; Stdin socket (ROUTER for input requests)
    (setf *stdin-socket* (pzmq:socket *zmq-context* :router))
    (pzmq:bind *stdin-socket*
               (make-endpoint transport ip
                              (gethash "stdin_port" connection)))
    
    ;; Heartbeat socket (REP for echo)
    (setf *heartbeat-socket* (pzmq:socket *zmq-context* :rep))
    (pzmq:bind *heartbeat-socket*
               (make-endpoint transport ip
                              (gethash "hb_port" connection)))))

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

(defun bytes-vector-to-hex-string (bytes)
  "Convert a byte vector to a hex string for identity frames."
  (with-output-to-string (s)
    (loop for byte across bytes
          do (format s "~2,'0x" byte))))

(defun recv-binary-part (socket msg)
  "Receive a binary message part into MSG, return as byte vector."
  (pzmq:msg-recv msg socket)
  (let* ((size (pzmq:msg-size msg))
         (data (pzmq:msg-data msg))
         (result (make-array size :element-type '(unsigned-byte 8))))
    (dotimes (i size)
      (setf (aref result i) (cffi:mem-ref data :unsigned-char i)))
    result))

(defun recv-string-part (socket msg)
  "Receive a message part as UTF-8 string."
  (pzmq:msg-recv msg socket)
  (handler-case
      (cffi:foreign-string-to-lisp (pzmq:msg-data msg)
                                   :count (pzmq:msg-size msg)
                                   :encoding :utf-8)
    (error (e)
      (declare (ignore e))
      ;; If UTF-8 decode fails, return hex representation
      (let* ((size (pzmq:msg-size msg))
             (data (pzmq:msg-data msg))
             (bytes (make-array size :element-type '(unsigned-byte 8))))
        (dotimes (i size)
          (setf (aref bytes i) (cffi:mem-ref data :unsigned-char i)))
        (bytes-vector-to-hex-string bytes)))))

(defun more-parts-p (socket)
  "Check if there are more parts to receive."
  (pzmq:getsockopt socket :rcvmore))

(defun recv-multipart (socket)
  "Receive a multipart message from a ZeroMQ socket.
   Identity frames (before delimiter) are received as raw byte vectors.
   Message body frames (after delimiter) are received as UTF-8 strings.
   Returns a list where identities are byte vectors and body parts are strings."
  (pzmq:with-message msg
    (let ((parts nil)
          (past-delimiter nil))
      (loop
        (if past-delimiter
            ;; After delimiter: read as UTF-8 string
            (push (recv-string-part socket msg) parts)
            ;; Before delimiter: read as binary
            (let ((binary (recv-binary-part socket msg)))
              ;; Check if this is the delimiter
              (if (and (= (length binary) (length +ids-msg-delimiter+))
                       (every #'char= 
                              +ids-msg-delimiter+ 
                              (cl:map 'string #'code-char binary)))
                  (progn
                    (push +ids-msg-delimiter+ parts)
                    (setf past-delimiter t))
                  ;; Identity frame - keep as raw bytes
                  (push binary parts))))
        (unless (more-parts-p socket)
          (return)))
      (nreverse parts))))

(defun send-binary-part (socket bytes sndmore)
  "Send a binary byte vector as a message part."
  (let ((size (length bytes)))
    (cffi:with-foreign-object (buf :unsigned-char size)
      (dotimes (i size)
        (setf (cffi:mem-ref buf :unsigned-char i) (aref bytes i)))
      (pzmq:send socket (cffi:foreign-string-to-lisp buf :count size :encoding :latin-1)
                 :sndmore sndmore))))

(defun send-multipart (socket parts)
  "Send a multipart message to a ZeroMQ socket.
   PARTS is a list where identity frames are byte vectors and body frames are strings."
  (debug-log "~&send-multipart: sending ~D parts~%" (length parts))
  (loop for (part . rest) on parts
        do (if (typep part '(simple-array (unsigned-byte 8) (*)))
               ;; Binary identity frame
               (send-binary-part socket part (not (null rest)))
               ;; String frame
               (pzmq:send socket part :sndmore (not (null rest))))))

(defun wire-part-equal (a b)
  "Compare two wire message parts. A may be byte vector or string, B is typically a string."
  (cond
    ((and (stringp a) (stringp b))
     (string= a b))
    ((and (typep a '(simple-array (unsigned-byte 8) (*))) (stringp b))
     ;; Compare byte vector to string
     (and (= (length a) (length b))
          (every #'= a (cl:map 'list #'char-code b))))
    (t nil)))

(defun parse-wire-message (parts)
  "Parse a wire protocol message into components.
   PARTS is a list where identities may be byte vectors and body parts are strings.
   Returns: (values identities signature header parent-header metadata content)"
  (let ((delim-pos (position +ids-msg-delimiter+ parts :test #'wire-part-equal)))
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
;;; JSON Encoding (Pure Common Lisp using shasht)
;;;============================================================================

(defun json-encode (object)
  "Encode an object (alist) as a JSON string.
   Uses shasht for JSON writing."
  (shasht:write-json object nil))

;;;============================================================================
;;; HMAC Signing (using OpenSSL)
;;;============================================================================

(defun hmac-sign-raw (key &rest messages)
  "Compute HMAC-SHA256 signature for messages concatenated together.
   KEY is the signing key string (empty string means no signing).
   Returns hex string signature.
   Uses OpenSSL command-line tool for production-quality HMAC."
  (if (or (null key) (equal key ""))
      ""  ; No signing if no key
    (let* ((data (apply #'concatenate 'string messages))
           ;; Run openssl and write data to its stdin
           ;; OpenSSL outputs: "SHA2-256(stdin)= <hex>"
           (output (uiop:run-program 
                    (list "openssl" "dgst" "-sha256" "-hmac" key)
                    :input (make-string-input-stream data)
                    :output '(:string :stripped t)
                    :error-output nil)))
      ;; Extract hex from "SHA2-256(stdin)= <hex>" or "(stdin)= <hex>"
      (let ((pos (search "= " output)))
        (if pos
            (subseq output (+ pos 2))
            output)))))

;;;============================================================================
;;; Message Construction (Pure Common Lisp)
;;;============================================================================

(defun make-msg-header (msg-id msg-type username session date)
  "Create a message header as a hash-table (for JSON encoding)."
  (let ((header (make-hash-table :test #'equal)))
    (setf (gethash "msg_id" header) msg-id)
    (setf (gethash "msg_type" header) msg-type)
    (setf (gethash "username" header) username)
    (setf (gethash "session" header) session)
    (setf (gethash "date" header) date)
    (setf (gethash "version" header) "5.3")
    header))

(defun make-status-msg-content (status)
  "Create status message content."
  (let ((content (make-hash-table :test #'equal)))
    (setf (gethash "execution_state" content) status)
    content))

(defun make-stream-msg-content (stream-name text)
  "Create stream message content."
  (let ((content (make-hash-table :test #'equal)))
    (setf (gethash "name" content) stream-name)
    (setf (gethash "text" content) text)
    content))

(defun make-execute-result-msg-content (execution-count text-result)
  "Create execute_result message content."
  (let ((content (make-hash-table :test #'equal))
        (data (make-hash-table :test #'equal))
        (metadata (make-hash-table :test #'equal)))
    (setf (gethash "text/plain" data) text-result)
    (setf (gethash "execution_count" content) execution-count)
    (setf (gethash "data" content) data)
    (setf (gethash "metadata" content) metadata)
    content))

(defun make-error-msg-content (ename evalue traceback)
  "Create error message content."
  (let ((content (make-hash-table :test #'equal)))
    (setf (gethash "ename" content) ename)
    (setf (gethash "evalue" content) evalue)
    (setf (gethash "traceback" content) (or traceback (list evalue)))
    content))

(defun make-execute-reply-ok-content (execution-count)
  "Create execute_reply OK content."
  (let ((content (make-hash-table :test #'equal)))
    (setf (gethash "status" content) "ok")
    (setf (gethash "execution_count" content) execution-count)
    (setf (gethash "user_expressions" content) (make-hash-table :test #'equal))
    content))

(defun make-execute-reply-error-content (execution-count ename evalue traceback)
  "Create execute_reply error content."
  (let ((content (make-hash-table :test #'equal)))
    (setf (gethash "status" content) "error")
    (setf (gethash "execution_count" content) execution-count)
    (setf (gethash "ename" content) ename)
    (setf (gethash "evalue" content) evalue)
    (setf (gethash "traceback" content) (or traceback (list evalue)))
    content))

(defun make-kernel-info-content ()
  "Create kernel_info_reply content."
  (let ((content (make-hash-table :test #'equal))
        (language-info (make-hash-table :test #'equal))
        (help-links (make-hash-table :test #'equal)))
    (setf (gethash "name" language-info) "acl2")
    (setf (gethash "version" language-info) "8.6")
    (setf (gethash "mimetype" language-info) "text/x-common-lisp")
    (setf (gethash "file_extension" language-info) ".lisp")
    (setf (gethash "pygments_lexer" language-info) "common-lisp")
    (setf (gethash "codemirror_mode" language-info) "commonlisp")
    (setf (gethash "nbconvert_exporter" language-info) "")
    
    (setf (gethash "status" content) "ok")  ; Required for reply validation
    (setf (gethash "protocol_version" content) "5.3")
    (setf (gethash "implementation" content) "acl2-kernel")
    (setf (gethash "implementation_version" content) "0.1.0")
    (setf (gethash "language_info" content) language-info)
    (setf (gethash "banner" content) "ACL2 Jupyter Kernel - A Computational Logic for Applicative Common Lisp")
    (setf (gethash "debugger" content) nil)
    (setf (gethash "help_links" content) (list))
    content))

(defun make-shutdown-reply-content (restart)
  "Create shutdown_reply content."
  (let ((content (make-hash-table :test #'equal)))
    (setf (gethash "restart" content) restart)
    content))

;;;============================================================================
;;; IOPub Publishing
;;;============================================================================

(defun publish-status (status parent-header)
  "Publish a status message (busy/idle) on IOPub."
  (let* ((header-json (json-encode 
                       (make-msg-header (make-uuid) "status" 
                                        "acl2-kernel" *session-id* (iso8601-now))))
         (content-json (json-encode (make-status-msg-content status)))
         (signature (hmac-sign-raw *hmac-key* header-json parent-header "{}" content-json)))
    (send-multipart *iopub-socket*
                    (build-wire-message nil signature header-json parent-header "{}" content-json))))

(defun publish-stream (stream-name text parent-header)
  "Publish a stream message (stdout/stderr) on IOPub."
  (when (and text (> (length text) 0))
    (let* ((header-json (json-encode
                         (make-msg-header (make-uuid) "stream"
                                          "acl2-kernel" *session-id* (iso8601-now))))
           (content-json (json-encode (make-stream-msg-content stream-name text)))
           (signature (hmac-sign-raw *hmac-key* header-json parent-header "{}" content-json)))
      (send-multipart *iopub-socket*
                      (build-wire-message nil signature header-json parent-header "{}" content-json)))))

(defun publish-execute-result (execution-count text-result parent-header)
  "Publish an execute_result message on IOPub."
  (let* ((header-json (json-encode
                       (make-msg-header (make-uuid) "execute_result"
                                        "acl2-kernel" *session-id* (iso8601-now))))
         (content-json (json-encode (make-execute-result-msg-content execution-count text-result)))
         (signature (hmac-sign-raw *hmac-key* header-json parent-header "{}" content-json)))
    (send-multipart *iopub-socket*
                    (build-wire-message nil signature header-json parent-header "{}" content-json))))

(defun publish-error (ename evalue traceback parent-header)
  "Publish an error message on IOPub."
  (let* ((header-json (json-encode
                       (make-msg-header (make-uuid) "error"
                                        "acl2-kernel" *session-id* (iso8601-now))))
         (content-json (json-encode (make-error-msg-content ename evalue traceback)))
         (signature (hmac-sign-raw *hmac-key* header-json parent-header "{}" content-json)))
    (send-multipart *iopub-socket*
                    (build-wire-message nil signature header-json parent-header "{}" content-json))))

;;;============================================================================
;;; Request Handlers
;;;============================================================================

(defun handle-kernel-info-request (identities parent-header)
  "Handle kernel_info_request, send kernel_info_reply."
  (debug-log "~&Handling kernel_info_request~%")
  (debug-log "  identities: ~S~%" identities)
  (let* ((header-json (json-encode
                       (make-msg-header (make-uuid) "kernel_info_reply"
                                        "acl2-kernel" *session-id* (iso8601-now))))
         (content-json (json-encode (make-kernel-info-content)))
         (signature (hmac-sign-raw *hmac-key* header-json parent-header "{}" content-json)))
    (debug-log "  Sending kernel_info_reply~%")
    (send-multipart *shell-socket*
                    (build-wire-message identities signature header-json parent-header "{}" content-json))
    (debug-log "  Sent kernel_info_reply~%")))

(defun handle-execute-request (identities parent-header content-json)
  "Handle execute_request, evaluate code and send replies."
  ;; Parse the content using shasht
  (let* ((content (shasht:read-json content-json))
         (code (gethash "code" content ""))
         (silent (gethash "silent" content nil)))
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
            (let* ((header-json (json-encode
                                 (make-msg-header (make-uuid) "execute_reply"
                                                  "acl2-kernel" *session-id* (iso8601-now))))
                   (reply-content-json (json-encode
                                        (make-execute-reply-error-content 
                                         *execution-count*
                                         (format nil "~A" (first error-info))
                                         (second error-info)
                                         nil)))
                   (signature (hmac-sign-raw *hmac-key* header-json parent-header "{}" reply-content-json)))
              (send-multipart *shell-socket*
                              (build-wire-message identities signature header-json parent-header "{}" reply-content-json))))
          (progn
            ;; Publish result (unless silent)
            (unless silent
              (publish-execute-result *execution-count* result parent-header))
            ;; Send OK reply
            (let* ((header-json (json-encode
                                 (make-msg-header (make-uuid) "execute_reply"
                                                  "acl2-kernel" *session-id* (iso8601-now))))
                   (reply-content-json (json-encode (make-execute-reply-ok-content *execution-count*)))
                   (signature (hmac-sign-raw *hmac-key* header-json parent-header "{}" reply-content-json)))
              (send-multipart *shell-socket*
                              (build-wire-message identities signature header-json parent-header "{}" reply-content-json))))))
    
    ;; Publish idle status
    (publish-status "idle" parent-header)))

(defun handle-shutdown-request (identities parent-header content-json)
  "Handle shutdown_request, send reply and stop kernel."
  (let* ((content (shasht:read-json content-json))
         (restart (gethash "restart" content nil))
         (header-json (json-encode
                       (make-msg-header (make-uuid) "shutdown_reply"
                                        "acl2-kernel" *session-id* (iso8601-now))))
         (reply-content-json (json-encode (make-shutdown-reply-content restart)))
         (signature (hmac-sign-raw *hmac-key* header-json parent-header "{}" reply-content-json)))
    ;; Send reply
    (send-multipart *shell-socket*
                    (build-wire-message identities signature header-json parent-header "{}" reply-content-json))
    ;; Stop the kernel
    (setf *kernel-running* nil)))

;;;============================================================================
;;; Message Dispatch
;;;============================================================================

(defun dispatch-message (socket)
  "Receive and dispatch a message from SOCKET."
  (debug-log "~&dispatch-message: receiving...~%")
  (let ((parts (recv-multipart socket)))
    (debug-log "~&dispatch-message: received ~D parts~%" (length parts))
    (multiple-value-bind (identities signature header-json parent-json metadata-json content-json)
        (parse-wire-message parts)
      (debug-log "~&dispatch-message: parsed message~%")
      (when *kernel-debug*
        (format t "  identities: ~S~%" identities)
        (format t "  header-json: ~A~%" (if header-json (subseq header-json 0 (min 100 (length header-json))) nil))
        (force-output))
      (when header-json
        ;; Parse header to get msg_type using shasht
        (let* ((header (shasht:read-json header-json))
               (msg-type (gethash "msg_type" header)))
          (debug-log "~&dispatch-message: msg_type = ~A~%" msg-type)
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
             (format t "~&Unknown message type: ~A~%" msg-type))))))))

;;;============================================================================
;;; Main Event Loop
;;;============================================================================

(defconstant +zmq-poll-timeout+ 500
  "ZMQ poll timeout in milliseconds.")

(defun message-available-p (socket)
  "Check if a message is available to read on SOCKET.
   Returns true if :pollin is in the events list."
  (let ((status (pzmq:getsockopt socket :events)))
    (and (position :pollin status) t)))

(defun kernel-main-loop ()
  "Main event loop - poll sockets and dispatch messages."
  (pzmq:with-poll-items items ((*control-socket* :pollin)
                               (*shell-socket* :pollin))
    (loop while *kernel-running*
          do (handler-case
                 (progn
                   ;; Poll with timeout
                   (let ((ready (pzmq:poll items +zmq-poll-timeout+)))
                     (when (> ready 0)
                       ;; Check control socket (higher priority)
                       (when (member :pollin (pzmq:revents items 0))
                         (debug-log "~&Message on control socket~%")
                         (dispatch-message *control-socket*))
                       ;; Check shell socket
                       (when (member :pollin (pzmq:revents items 1))
                         (debug-log "~&Message on shell socket~%")
                         (dispatch-message *shell-socket*)))))
               (error (e)
                 (format t "~&Error in main loop: ~A~%" e)
                 (force-output))))))

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
    (setf *hmac-key* (or (gethash "key" connection) ""))
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

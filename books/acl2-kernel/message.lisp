; ACL2 Jupyter Kernel - Message Envelope
; Copyright (C) 2026
;
; License: MIT
;
; Implements Jupyter wire protocol message envelope:
; - Message structure and serialization
; - HMAC-SHA-256 signing
; - Uses centaur/bridge/to-json for JSON encoding
; - Uses kestrel/crypto/interfaces/hmac-sha-256 for signing

(in-package "ACL2-KERNEL")
(include-book "centaur/bridge/to-json" :dir :system)
(include-book "kestrel/crypto/interfaces/hmac-sha-256" :dir :system)
(include-book "kestrel/typed-lists-light/map-char-code" :dir :system)
(include-book "kestrel/utilities/strings/hexstrings" :dir :system)
(include-book "std/strings/top" :dir :system)
(include-book "std/util/define" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "std/testing/assert-bang" :dir :system))

;;;============================================================================
;;; Jupyter Message Structure
;;;============================================================================

;; A Jupyter message consists of:
;; - header: contains msg_id, msg_type, username, session, date, version
;; - parent_header: header of message this is a reply to (or empty dict)
;; - metadata: additional metadata
;; - content: actual payload (depends on msg_type)
;; - buffers: optional binary buffers (empty for most messages)
;;
;; Wire format (ZeroMQ multipart):
;; [<IDS|MSG> delimiter, HMAC signature, header, parent_header, metadata, content, buffers...]

;;;============================================================================
;;; String/Byte List Conversions
;;;============================================================================

;; Convert a string to a list of bytes (character codes)
(define string-to-bytes ((s stringp))
  :returns (bytes acl2::byte-listp)
  :short "Convert a string to a list of bytes (character codes)"
  (if (mbt (stringp s))
      (acl2::map-char-code (coerce s 'list))
    nil))

;; Convert bytes to lowercase hex string using existing book
(define bytes-to-hex-string ((bytes (acl2::unsigned-byte-listp 8 bytes)))
  :returns (s stringp)
  :short "Convert a list of bytes to a lowercase hex string"
  (str::downcase-string (acl2::ubyte8s=>hexstring bytes)))

;;;============================================================================
;;; HMAC-SHA-256 Signing
;;;============================================================================

;; Sign a message with HMAC-SHA-256
;; Key and data are strings, result is hex string
;; Note: Uses :mode :program due to HMAC guard complexity (size limit)
(define hmac-sign ((key stringp) (data stringp))
  :mode :program
  :short "Compute HMAC-SHA-256 signature as hex string"
  :long "<p>Given a key and data as strings, compute the HMAC-SHA-256
and return it as a lowercase hex string.</p>"
  (let* ((key-bytes (string-to-bytes key))
         (data-bytes (string-to-bytes data))
         (sig-bytes (crypto::hmac-sha-256 key-bytes data-bytes)))
    (bytes-to-hex-string sig-bytes)))

;;;============================================================================
;;; Message Header
;;;============================================================================

;; Create a message header alist
(define make-header ((msg-id stringp)
                     (msg-type stringp)
                     (username stringp)
                     (session stringp)
                     (date stringp))
  :returns (header alistp)
  :short "Create a Jupyter message header"
  (list (cons "msg_id" msg-id)
        (cons "msg_type" msg-type)
        (cons "username" username)
        (cons "session" session)
        (cons "date" date)
        (cons "version" "5.3")))

;;;============================================================================
;;; JSON Encoding Wrapper
;;;============================================================================

;; Wrapper around bridge::json-encode that handles alists properly
;; Bridge encodes alists with atom keys as JSON objects automatically
(define json-encode (x)
  :returns (json stringp :rule-classes :type-prescription)
  :short "Encode an ACL2 object as JSON"
  (bridge::json-encode x))

;;;============================================================================
;;; Message Envelope
;;;============================================================================

;; Message delimiter (separates identities from message content)
(defconst *msg-delimiter* "<IDS|MSG>")

;; Compute the signature for a message
;; Concatenates JSON parts and signs with HMAC
(define message-signature ((key stringp)
                           (header stringp)
                           (parent-header stringp)
                           (metadata stringp)
                           (content stringp))
  :mode :program
  :short "Compute HMAC signature for message parts"
  :long "<p>The signature is computed over the concatenation of
header, parent_header, metadata, and content (all JSON strings).</p>"
  (if (equal key "")
      ""  ; Empty key means no signature required
    (hmac-sign key (str::cat header parent-header metadata content))))

;; Create a full message envelope for sending
;; Returns a list of strings to be sent as ZeroMQ multipart message
(define make-message-envelope ((identity-frames string-listp)
                               (key stringp)
                               (header alistp)
                               (parent-header alistp)
                               (metadata alistp)
                               (content alistp))
  :mode :program
  :short "Create a complete Jupyter message envelope"
  :long "<p>Creates the multipart message frame list:
[identities..., delimiter, signature, header, parent_header, metadata, content]</p>"
  (let* ((header-json (json-encode header))
         (parent-json (json-encode parent-header))
         (metadata-json (json-encode metadata))
         (content-json (json-encode content))
         (sig (message-signature key header-json parent-json metadata-json content-json)))
    (append identity-frames
            (list *msg-delimiter*
                  sig
                  header-json
                  parent-json
                  metadata-json
                  content-json))))

;;;============================================================================
;;; Message Types
;;;============================================================================

;; Kernel info reply content
(define kernel-info-content ()
  :returns (content alistp)
  :short "Create kernel_info_reply content"
  (list (cons "status" "ok")
        (cons "protocol_version" "5.3")
        (cons "implementation" "acl2")
        (cons "implementation_version" "1.0.0")
        (cons "language_info"
              (list (cons "name" "acl2")
                    (cons "version" "8.6")
                    (cons "mimetype" "text/x-acl2")
                    (cons "file_extension" ".lisp")
                    (cons "codemirror_mode" "commonlisp")))
        (cons "banner" "ACL2 Jupyter Kernel")
        (cons "help_links" nil)))

;; Status message content
(define status-content ((execution-state stringp))
  :returns (content alistp)
  :short "Create status message content"
  (list (cons "execution_state" execution-state)))

;; Execute reply content (success)
(define execute-reply-ok ((execution-count natp))
  :returns (content alistp)
  :short "Create execute_reply content for success"
  (list (cons "status" "ok")
        (cons "execution_count" execution-count)
        (cons "user_expressions" nil)))

;; Execute reply content (error)
(define execute-reply-error ((execution-count natp)
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

;; Stream output content
(define stream-content ((stream-name stringp) (text stringp))
  :returns (content alistp)
  :short "Create stream message content"
  :guard (or (equal stream-name "stdout") (equal stream-name "stderr"))
  (list (cons "name" stream-name)
        (cons "text" text)))

;; Execute result content
(define execute-result-content ((execution-count natp)
                                (data alistp)
                                (metadata alistp))
  :returns (content alistp)
  :short "Create execute_result message content"
  (list (cons "execution_count" execution-count)
        (cons "data" data)
        (cons "metadata" metadata)))

;;;============================================================================
;;; Tests
;;;============================================================================

(local
 (progn
   ;; Test string to bytes
   (assert! (equal (string-to-bytes "ABC") '(65 66 67)))
   (assert! (equal (string-to-bytes "") nil))

   ;; Test bytes to hex string (using ubyte8s=>hexstring)
   (assert! (equal (bytes-to-hex-string '(0 15 255)) "000fff"))
   (assert! (equal (bytes-to-hex-string '(171 205)) "abcd"))

   ;; Test JSON encoding
   (assert! (stringp (json-encode (list (cons "a" "b")))))

   ;; Test header creation
   (assert! (alistp (make-header "id1" "execute_request" "user" "sess" "2026-01-01T00:00:00.000Z")))

   ;; Test message signature (empty key = no signature)
   (assert! (equal (message-signature "" "h" "p" "m" "c") ""))

   ;; Test kernel info content
   (assert! (alistp (kernel-info-content)))
   (assert! (equal (cdr (assoc-equal "status" (kernel-info-content))) "ok"))

   ;; Test execute reply content
   (assert! (alistp (execute-reply-ok 1)))
   (assert! (equal (cdr (assoc-equal "status" (execute-reply-ok 1))) "ok"))))


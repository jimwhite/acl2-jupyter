; ACL2 Jupyter Kernel - Connection File Parser
; Copyright (C) 2026
;
; License: MIT
;
; Parses Jupyter connection files using kestrel/json-parser

(in-package "ACL2-KERNEL")
(include-book "kestrel/json-parser/parse-json" :dir :system)
(include-book "kestrel/json-parser/parse-json-file" :dir :system)
(include-book "kestrel/json-parser/parsed-json" :dir :system)
(include-book "std/strings/cat" :dir :system)
(include-book "std/strings/decimal" :dir :system)
(include-book "std/util/define" :dir :system)
(local (include-book "std/testing/assert-bang" :dir :system))

;;;============================================================================
;;; Connection File Structure
;;;============================================================================

;; A Jupyter connection file contains:
;; {
;;   "transport": "tcp" or "ipc",
;;   "ip": "127.0.0.1" (for TCP),
;;   "shell_port": 12345,
;;   "control_port": 12346,
;;   "iopub_port": 12347,
;;   "stdin_port": 12348,
;;   "hb_port": 12349,
;;   "key": "uuid-string",
;;   "signature_scheme": "hmac-sha256",
;;   "kernel_name": "acl2"
;; }

;;;============================================================================
;;; Accessor Functions for Parsed JSON Objects
;;;============================================================================

;; Lemmas for JSON object manipulation
(local
 (encapsulate ()
   (defthm alistp-when-parsed-json-objectp
     (implies (acl2::parsed-json-objectp obj)
              (alistp (cadr obj)))
     :hints (("Goal" :in-theory (enable acl2::parsed-json-objectp))))

   (defthm parsed-json-objectp-compound-recognizer
     (implies (acl2::parsed-json-objectp obj)
              (and (consp obj)
                   (consp (cdr obj))))
     :rule-classes :compound-recognizer
     :hints (("Goal" :in-theory (enable acl2::parsed-json-objectp))))))

;; Get the pairs from a parsed JSON object
(define json-object-pairs ((obj acl2::parsed-json-objectp))
  :returns (pairs alistp :hyp :guard)
  :short "Extract the pairs from a parsed JSON object"
  (cadr obj)
  :guard-hints (("Goal" :in-theory (enable acl2::parsed-json-objectp))))

;; Look up a string key in parsed JSON object pairs
(define json-lookup ((key stringp) (pairs alistp))
  :returns (result)
  :short "Look up a key in JSON object pairs"
  (cdr (assoc-equal key pairs)))

;; Get a string value from a JSON object
(define json-get-string ((key stringp) (obj acl2::parsed-json-objectp))
  :returns (result)
  :short "Get a string value from a JSON object by key"
  (let ((val (json-lookup key (json-object-pairs obj))))
    (if (stringp val) val nil)))

;; Get an integer value from a JSON object
(define json-get-integer ((key stringp) (obj acl2::parsed-json-objectp))
  :returns (result)
  :short "Get an integer value from a JSON object by key"
  (let ((val (json-lookup key (json-object-pairs obj))))
    (if (integerp val) val nil)))

;;;============================================================================
;;; Connection Configuration Structure
;;;============================================================================

;; Connection configuration as an alist with known keys
(define connection-config-p (x)
  :short "Recognizer for connection configuration"
  (and (alistp x)
       (stringp (cdr (assoc-eq :transport x)))
       (stringp (cdr (assoc-eq :key x)))
       (stringp (cdr (assoc-eq :signature-scheme x)))))

;; Extract connection config from parsed JSON object
(define parse-connection-json ((json acl2::parsed-json-valuep))
  :returns (config alistp)
  :short "Convert parsed JSON to connection configuration alist"
  (if (not (acl2::parsed-json-objectp json))
      nil
    (let ((pairs (json-object-pairs json)))
      (list (cons :transport (json-lookup "transport" pairs))
            (cons :ip (json-lookup "ip" pairs))
            (cons :shell-port (json-lookup "shell_port" pairs))
            (cons :control-port (json-lookup "control_port" pairs))
            (cons :iopub-port (json-lookup "iopub_port" pairs))
            (cons :stdin-port (json-lookup "stdin_port" pairs))
            (cons :hb-port (json-lookup "hb_port" pairs))
            (cons :key (json-lookup "key" pairs))
            (cons :signature-scheme (json-lookup "signature_scheme" pairs))
            (cons :kernel-name (json-lookup "kernel_name" pairs))))))

;;;============================================================================
;;; Build Socket Endpoints
;;;============================================================================

;; Build a TCP endpoint string
(define build-tcp-endpoint ((ip stringp) (port integerp))
  :returns (endpoint stringp)
  :short "Build TCP endpoint string like tcp://127.0.0.1:12345"
  (str::cat "tcp://" ip ":" (str::natstr (nfix port))))

;; Build an IPC endpoint string (Unix domain socket)
(define build-ipc-endpoint ((path stringp))
  :returns (endpoint stringp)
  :short "Build IPC endpoint string like ipc:///path/to/socket"
  (str::cat "ipc://" path))

;; Build endpoint from connection config
(define connection-endpoint ((config alistp) (port-key symbolp))
  :returns (endpoint stringp)
  :short "Build endpoint string for a given port from connection config"
  (let ((transport (cdr (assoc-eq :transport config)))
        (ip (cdr (assoc-eq :ip config)))
        (port (cdr (assoc-eq port-key config))))
    (cond ((equal transport "tcp")
           (if (and (stringp ip) (integerp port))
               (build-tcp-endpoint ip port)
             ""))
          ((equal transport "ipc")
           (if (stringp port)
               (build-ipc-endpoint port)
             ""))
          (t ""))))

;;;============================================================================
;;; Main Entry Point
;;;============================================================================

;; Parse connection file and return configuration
;; Returns (mv erp config state)
(define parse-connection-file ((filename stringp) state)
  :returns (mv erp config state)
  :stobjs state
  :mode :program  ; Uses file I/O
  :short "Parse a Jupyter connection file"
  (b* (((mv erp parsed-json state)
        (acl2::parse-file-as-json filename state))
       ((when erp)
        (mv erp nil state))
       (config (parse-connection-json parsed-json)))
    (mv nil config state)))

;;;============================================================================
;;; Tests
;;;============================================================================

;; Test parsing a TCP connection JSON string
(local
 (progn
   ;; Test JSON parsing
   (defconst *test-tcp-json*
     "{\"transport\": \"tcp\", \"ip\": \"127.0.0.1\", \"shell_port\": 57503, \"control_port\": 50160, \"iopub_port\": 40885, \"stdin_port\": 52597, \"hb_port\": 42540, \"key\": \"test-key-uuid\", \"signature_scheme\": \"hmac-sha256\", \"kernel_name\": \"acl2\"}")

   (defconst *test-parsed*
     (mv-let (erp val)
       (acl2::parse-string-as-json *test-tcp-json*)
       (declare (ignore erp))
       val))

   (defconst *test-config*
     (parse-connection-json *test-parsed*))

   ;; Verify structure
   (assert! (acl2::parsed-json-objectp *test-parsed*))
   (assert! (alistp *test-config*))
   (assert! (equal (cdr (assoc-eq :transport *test-config*)) "tcp"))
   (assert! (equal (cdr (assoc-eq :ip *test-config*)) "127.0.0.1"))
   (assert! (equal (cdr (assoc-eq :shell-port *test-config*)) 57503))
   (assert! (equal (cdr (assoc-eq :key *test-config*)) "test-key-uuid"))
   (assert! (equal (cdr (assoc-eq :signature-scheme *test-config*)) "hmac-sha256"))

   ;; Test endpoint building
   (assert! (equal (build-tcp-endpoint "127.0.0.1" 57503)
                   "tcp://127.0.0.1:57503"))

   (assert! (equal (connection-endpoint *test-config* :shell-port)
                   "tcp://127.0.0.1:57503"))))

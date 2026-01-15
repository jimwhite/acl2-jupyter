; ACL2 Jupyter Kernel - JSON Encoding/Decoding
; Copyright (C) 2026
;
; License: MIT
;
; JSON encoding adapted from centaur/bridge/to-json.lisp
; JSON decoding is new implementation for parsing connection files

(in-package "ACL2-KERNEL")
(include-book "std/util/defines" :dir :system)
(include-book "std/strings/cat" :dir :system)
(include-book "std/strings/decimal" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(local (include-book "std/strings/explode-atom" :dir :system))
(local (include-book "std/testing/assert-bang" :dir :system))
(local (include-book "std/typed-lists/character-listp" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

;;;============================================================================
;;; JSON Encoding (adapted from centaur/bridge/to-json.lisp)
;;;============================================================================

(defsection json-encoding
  :parents (acl2-kernel)
  :short "JSON encoder for ACL2 objects, compatible with Jupyter protocol."
  :long "<p>This encoder maps ACL2 objects to JSON strings. For the Jupyter
kernel, we need proper JSON output for protocol messages.</p>")

(local (xdoc::set-default-parents json-encoding))

;; Character encoding for JSON strings
(define json-encode-weird-char
  :short "Convert control characters to \\uXXXX sequences"
  ((code natp) acc)
  :guard (< code 256)
  :returns (new-acc character-listp :hyp (character-listp acc))
  (b* ((lo (logand code #xF))
       (hi (logand (ash code -4) #xF))
       (acc (cons #\\ acc))
       (acc (cons #\u acc))
       (acc (cons #\0 acc))
       (acc (cons #\0 acc))
       (acc (cons (digit-to-char hi) acc))
       (acc (cons (digit-to-char lo) acc)))
    acc))

(define json-encode-char
  :short "Encode a single character for JSON string"
  ((x characterp) acc)
  :returns (new-acc character-listp :hyp (and (characterp x)
                                              (character-listp acc)))
  (b* (((when (eql x #\\)) (cons #\\ (cons #\\ acc)))
       ((when (eql x #\")) (cons #\" (cons #\\ acc)))
       ((when (eql x #\Newline)) (cons #\n (cons #\\ acc)))
       ((when (eql x #\Tab)) (cons #\t (cons #\\ acc)))
       ((when (eql x #\Return)) (cons #\r (cons #\\ acc)))
       (code (char-code x))
       ((when (or (<= code 31) (>= code 127)))
        (json-encode-weird-char code acc)))
    (cons x acc)))

(define json-encode-chars ((x character-listp) acc)
  :returns (new-acc character-listp :hyp (and (character-listp x)
                                              (character-listp acc)))
  (if (atom x)
      acc
    (json-encode-chars (cdr x) (json-encode-char (car x) acc))))

(define json-encode-str ((x stringp) acc)
  :returns (new-acc character-listp :hyp (character-listp acc))
  (json-encode-chars (coerce x 'list) acc))

;; Encode atoms - for Jupyter we need proper JSON types
(define json-encode-atom-jupyter ((x atom) acc)
  :short "Encode atom for Jupyter protocol - uses proper JSON types"
  :returns (new-acc character-listp :hyp (character-listp acc))
  (cond
   ;; nil -> null (for Jupyter, null is meaningful)
   ((null x) (revappend (coerce "null" 'list) acc))
   ;; t -> true
   ((eq x t) (revappend (coerce "true" 'list) acc))
   ;; Keywords and symbols -> strings (quoted)
   ((symbolp x)
    (let* ((acc (cons #\" acc))
           (acc (if (keywordp x)
                    (json-encode-str (symbol-name x)
                                     (cons #\: acc))
                  (json-encode-str (symbol-name x) acc))))
      (cons #\" acc)))
   ;; Integers -> JSON numbers (unquoted)
   ((integerp x)
    (if (< x 0)
        (revappend (coerce (str::nat-to-dec-string (- x)) 'list)
                   (cons #\- acc))
      (revappend (coerce (str::nat-to-dec-string x) 'list) acc)))
   ;; Strings -> JSON strings (quoted, escaped)
   ((stringp x)
    (let* ((acc (cons #\" acc))
           (acc (json-encode-str x acc)))
      (cons #\" acc)))
   ;; Characters -> single-char strings
   ((characterp x)
    (let* ((acc (cons #\" acc))
           (acc (json-encode-char x acc)))
      (cons #\" acc)))
   ;; Other numbers (rationals, complex) -> strings
   ((acl2-numberp x)
    (let* ((acc (cons #\" acc))
           (acc (json-encode-chars (coerce (str::nat-to-dec-string
                                            (if (< x 0) (- x) x)) 'list) acc)))
      (cons #\" acc)))
   (t acc)))

;; Check if alist has all atom keys (for JSON object encoding)
(define json-simple-alist-p (x)
  :short "Check if x is an alist with atom keys"
  (if (atom x)
      (not x)
    (and (consp (car x))
         (atom (caar x))
         (json-simple-alist-p (cdr x)))))

;; Main encoder with mutual recursion
(defines json-encode-main
  :short "Recursively encode ACL2 object to JSON"

  (define json-encode-main ((x "Any ACL2 object") acc)
    :flag :main
    :measure (acl2::two-nats-measure (acl2-count x) 1)
    (cond
     ((atom x) (json-encode-atom-jupyter x acc))
     ((json-simple-alist-p x)
      (json-encode-alist x (cons #\{ acc)))
     (t (json-encode-list x (cons #\[ acc)))))

  (define json-encode-alist ((x json-simple-alist-p) acc)
    :flag :alist
    :measure (acl2::two-nats-measure (acl2-count x) 0)
    (b* (((when (atom x)) (cons #\} acc))
         (key (caar x))
         (val (cdar x))
         ;; Encode key as string
         (acc (cons #\" acc))
         (acc (if (stringp key)
                  (json-encode-str key acc)
                (if (keywordp key)
                    (json-encode-str (symbol-name key) acc)
                  (json-encode-str (symbol-name key) acc))))
         (acc (cons #\" acc))
         (acc (cons #\: acc))
         (acc (json-encode-main val acc))
         (acc (if (consp (cdr x)) (cons #\, acc) acc)))
      (json-encode-alist (cdr x) acc)))

  (define json-encode-list ((x true-listp) acc)
    :flag :list
    :measure (acl2::two-nats-measure (acl2-count x) 0)
    (b* (((when (atom x)) (cons #\] acc))
         (acc (json-encode-main (car x) acc))
         (acc (if (consp (cdr x)) (cons #\, acc) acc)))
      (json-encode-list (cdr x) acc)))

  ///
  (defthm-json-encode-main-flag
    (defthm character-listp-of-json-encode-main
      (implies (character-listp acc)
               (character-listp (json-encode-main x acc)))
      :flag :main)
    (defthm character-listp-of-json-encode-alist
      (implies (character-listp acc)
               (character-listp (json-encode-alist x acc)))
      :flag :alist)
    (defthm character-listp-of-json-encode-list
      (implies (character-listp acc)
               (character-listp (json-encode-list x acc)))
      :flag :list)))

(define json-encode ((x "Any ACL2 object"))
  :short "Top-level JSON encoder"
  :returns (json stringp :rule-classes :type-prescription)
  (coerce (reverse (json-encode-main x nil)) 'string))

;;;============================================================================
;;; JSON Decoding (new implementation)
;;;============================================================================

(defsection json-decoding
  :parents (acl2-kernel)
  :short "JSON decoder for parsing Jupyter connection files."
  :long "<p>A minimal JSON parser that handles the subset needed for
Jupyter protocol: objects, arrays, strings, numbers, booleans, null.</p>")

;; Skip whitespace
(define json-skip-ws ((chars character-listp))
  :returns (rest character-listp :hyp (character-listp chars))
  (if (or (atom chars)
          (not (member (car chars) '(#\Space #\Tab #\Newline #\Return))))
      chars
    (json-skip-ws (cdr chars))))

;; Parse a JSON string (assumes opening quote consumed)
(define json-parse-string-chars ((chars character-listp) (acc character-listp))
  :returns (mv (str stringp :hyp (character-listp acc))
               (rest character-listp :hyp (character-listp chars)))
  :measure (len chars)
  (b* (((when (atom chars)) (mv (coerce (reverse acc) 'string) nil))
       (c (car chars))
       ((when (eql c #\"))
        (mv (coerce (reverse acc) 'string) (cdr chars)))
       ((when (eql c #\\))
        (b* (((when (atom (cdr chars)))
              (mv (coerce (reverse acc) 'string) nil))
             (escaped (cadr chars))
             (actual (case escaped
                       (#\n #\Newline)
                       (#\t #\Tab)
                       (#\r #\Return)
                       (#\" #\")
                       (#\\ #\\)
                       (#\/ #\/)
                       (otherwise escaped))))
          (json-parse-string-chars (cddr chars) (cons actual acc)))))
    (json-parse-string-chars (cdr chars) (cons c acc))))

;; Parse a JSON number
(define json-parse-number-chars ((chars character-listp) (acc character-listp))
  :returns (mv (num-str stringp :hyp (character-listp acc))
               (rest character-listp :hyp (character-listp chars)))
  :measure (len chars)
  (b* (((when (atom chars)) (mv (coerce (reverse acc) 'string) nil))
       (c (car chars))
       ((unless (or (and (char<= #\0 c) (char<= c #\9))
                    (eql c #\-)
                    (eql c #\+)
                    (eql c #\.)
                    (eql c #\e)
                    (eql c #\E)))
        (mv (coerce (reverse acc) 'string) chars)))
    (json-parse-number-chars (cdr chars) (cons c acc))))

;; Forward declaration for mutual recursion
(mutual-recursion

 (defun json-parse-value (chars)
   (declare (xargs :measure (len chars)
                   :guard (character-listp chars)))
   (b* ((chars (json-skip-ws chars))
        ((when (atom chars)) (mv nil nil))
        (c (car chars)))
     (cond
      ;; String
      ((eql c #\")
       (json-parse-string-chars (cdr chars) nil))
      ;; Object
      ((eql c #\{)
       (json-parse-object (cdr chars) nil))
      ;; Array
      ((eql c #\[)
       (json-parse-array (cdr chars) nil))
      ;; Number (starts with digit or minus)
      ((or (and (char<= #\0 c) (char<= c #\9))
           (eql c #\-))
       (mv-let (num-str rest)
         (json-parse-number-chars chars nil)
         (let ((n (str::strval num-str)))
           (mv (if n n num-str) rest))))
      ;; true
      ((and (eql c #\t)
            (consp (cdr chars)) (eql (cadr chars) #\r)
            (consp (cddr chars)) (eql (caddr chars) #\u)
            (consp (cdddr chars)) (eql (cadddr chars) #\e))
       (mv t (cddddr chars)))
      ;; false
      ((and (eql c #\f)
            (consp (cdr chars)) (eql (cadr chars) #\a)
            (consp (cddr chars)) (eql (caddr chars) #\l)
            (consp (cdddr chars)) (eql (cadddr chars) #\s)
            (consp (cddddr chars)) (eql (car (cddddr chars)) #\e))
       (mv nil (cdr (cddddr chars))))
      ;; null
      ((and (eql c #\n)
            (consp (cdr chars)) (eql (cadr chars) #\u)
            (consp (cddr chars)) (eql (caddr chars) #\l)
            (consp (cdddr chars)) (eql (cadddr chars) #\l))
       (mv nil (cddddr chars)))
      (t (mv nil chars)))))

 (defun json-parse-object (chars acc)
   (declare (xargs :measure (len chars)
                   :guard (and (character-listp chars)
                               (alistp acc))))
   (b* ((chars (json-skip-ws chars))
        ((when (atom chars)) (mv (reverse acc) nil))
        ((when (eql (car chars) #\}))
         (mv (reverse acc) (cdr chars)))
        ;; Skip comma if present
        (chars (if (eql (car chars) #\,)
                   (json-skip-ws (cdr chars))
                 chars))
        ((when (atom chars)) (mv (reverse acc) nil))
        ((when (eql (car chars) #\}))
         (mv (reverse acc) (cdr chars)))
        ;; Parse key (must be string)
        ((unless (eql (car chars) #\"))
         (mv (reverse acc) chars))
        ((mv key chars) (json-parse-string-chars (cdr chars) nil))
        (chars (json-skip-ws chars))
        ((when (atom chars)) (mv (reverse acc) nil))
        ;; Expect colon
        ((unless (eql (car chars) #\:))
         (mv (reverse acc) chars))
        (chars (cdr chars))
        ;; Parse value
        ((mv val chars) (json-parse-value chars))
        ;; Use keyword for key
        (key-sym (intern$ key "KEYWORD")))
     (json-parse-object chars (cons (cons key-sym val) acc))))

 (defun json-parse-array (chars acc)
   (declare (xargs :measure (len chars)
                   :guard (and (character-listp chars)
                               (true-listp acc))))
   (b* ((chars (json-skip-ws chars))
        ((when (atom chars)) (mv (reverse acc) nil))
        ((when (eql (car chars) #\]))
         (mv (reverse acc) (cdr chars)))
        ;; Skip comma if present
        (chars (if (eql (car chars) #\,)
                   (json-skip-ws (cdr chars))
                 chars))
        ((when (atom chars)) (mv (reverse acc) nil))
        ((when (eql (car chars) #\]))
         (mv (reverse acc) (cdr chars)))
        ;; Parse value
        ((mv val chars) (json-parse-value chars)))
     (json-parse-array chars (cons val acc)))))

(define json-parse ((json-str stringp))
  :short "Parse a JSON string into an ACL2 object"
  :returns (result "Parsed JSON as alist/list/atom")
  (mv-let (val rest)
    (json-parse-value (coerce json-str 'list))
    (declare (ignore rest))
    val))

;;;============================================================================
;;; Tests
;;;============================================================================

(local
 (progn
   ;; Test encoding
   (assert! (equal (json-encode nil) "null"))
   (assert! (equal (json-encode t) "true"))
   (assert! (equal (json-encode 42) "42"))
   (assert! (equal (json-encode -123) "-123"))
   (assert! (equal (json-encode "hello") "\"hello\""))
   (assert! (equal (json-encode '(1 2 3)) "[1,2,3]"))
   (assert! (equal (json-encode '((:a . 1) (:b . 2))) "{\"a\":1,\"b\":2}"))

   ;; Test decoding
   (assert! (equal (json-parse "null") nil))
   (assert! (equal (json-parse "true") t))
   (assert! (equal (json-parse "false") nil))
   (assert! (equal (json-parse "42") 42))
   (assert! (equal (json-parse "\"hello\"") "hello"))
   (assert! (equal (json-parse "[1, 2, 3]") '(1 2 3)))
   (assert! (equal (json-parse "{\"a\": 1, \"b\": 2}")
                   '((:a . 1) (:b . 2))))

   ;; Test nested structures
   (assert! (equal (json-parse "{\"key\": [1, 2, {\"nested\": true}]}")
                   '((:key . (1 2 ((:nested . t)))))))

   ;; Test connection file format
   (assert! (equal (json-parse "{\"transport\": \"tcp\", \"ip\": \"127.0.0.1\", \"shell_port\": 57503}")
                   '((:transport . "tcp") (:ip . "127.0.0.1") (:shell_port . 57503))))))

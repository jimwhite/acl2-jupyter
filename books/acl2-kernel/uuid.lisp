; uuid.lisp - UUID v4 generation for ACL2 Jupyter Kernel
; Copyright 2025 - Part of ACL2 Jupyter Kernel
;
; This book provides UUID v4 generation for Jupyter message IDs.
; The actual generation uses raw Lisp (uuid-raw.lsp) for OS entropy.
; This wrapper provides ACL2 type theorems and logical characterization.

(in-package "ACL2-KERNEL")

(include-book "std/strings/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "tools/include-raw" :dir :system)

;;;============================================================================
;;; UUID String Recognition
;;;============================================================================

;; UUID format: xxxxxxxx-xxxx-xxxx-xxxx-xxxxxxxxxxxx
;; 8-4-4-4-12 hex digits with hyphens = 36 characters

(define hex-char-p ((c characterp))
  :returns (b booleanp)
  :short "Recognize a hexadecimal character."
  (let ((code (char-code c)))
    (or (and (<= (char-code #\0) code) (<= code (char-code #\9)))
        (and (<= (char-code #\a) code) (<= code (char-code #\f)))
        (and (<= (char-code #\A) code) (<= code (char-code #\F))))))

(define hex-char-list-p ((chars character-listp))
  :returns (b booleanp)
  :short "Recognize a list of hex characters."
  (if (atom chars)
      t
    (and (hex-char-p (car chars))
         (hex-char-list-p (cdr chars)))))

(define uuid-format-p ((s stringp))
  :returns (b booleanp)
  :short "Recognize a UUID v4 format string."
  :long "UUID format: xxxxxxxx-xxxx-xxxx-xxxx-xxxxxxxxxxxx (36 chars)"
  (and (equal (length s) 36)
       (let ((chars (coerce s 'list)))
         (and ;; 8 hex chars
              (hex-char-list-p (take 8 chars))
              ;; hyphen
              (equal (nth 8 chars) #\-)
              ;; 4 hex chars
              (hex-char-list-p (take 4 (nthcdr 9 chars)))
              ;; hyphen
              (equal (nth 13 chars) #\-)
              ;; 4 hex chars (version nibble position 14)
              (hex-char-list-p (take 4 (nthcdr 14 chars)))
              ;; hyphen
              (equal (nth 18 chars) #\-)
              ;; 4 hex chars (variant nibble position 19)
              (hex-char-list-p (take 4 (nthcdr 19 chars)))
              ;; hyphen
              (equal (nth 23 chars) #\-)
              ;; 12 hex chars
              (hex-char-list-p (nthcdr 24 chars))))))

(define uuid-v4-format-p ((s stringp))
  :returns (b booleanp)
  :short "Recognize a UUID v4 string (version nibble is 4)."
  (and (uuid-format-p s)
       ;; Version nibble at position 14 must be '4'
       (equal (char s 14) #\4)
       ;; Variant nibble at position 19 must be 8, 9, a, b, A, B
       (member (char s 19) '(#\8 #\9 #\a #\b #\A #\B))))

;;;============================================================================
;;; Raw Lisp UUID Generation
;;;============================================================================

;; Load raw Lisp implementation
(include-raw "uuid-raw.lsp"
             :do-not-compile t
             :host-readtable t)

;; Declare the raw function (returns a string, but we can't prove properties
;; about truly random functions in logic mode)
(defttag :uuid-raw)
(remove-untouchable 'generate-uuid-raw nil)
(progn!
 (set-raw-mode t)
 ;; generate-uuid-raw is defined in uuid-raw.lsp
 nil)
(defttag nil)

;; ACL2 wrapper - program mode since we can't reason about randomness
(define generate-uuid ()
  :returns (uuid stringp)
  :mode :program
  :short "Generate a new UUID v4 string."
  :long "Returns a 36-character UUID v4 string using OS entropy.
         Format: xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx"
  (generate-uuid-raw))

;;;============================================================================
;;; Tests - Verify format recognizer works
;;;============================================================================

;; Test hex-char-p
(local
 (assert! (hex-char-p #\0)))
(local
 (assert! (hex-char-p #\9)))
(local
 (assert! (hex-char-p #\a)))
(local
 (assert! (hex-char-p #\f)))
(local
 (assert! (hex-char-p #\A)))
(local
 (assert! (hex-char-p #\F)))
(local
 (assert! (not (hex-char-p #\g))))
(local
 (assert! (not (hex-char-p #\-))))

;; Test uuid-format-p with known valid UUID
(local
 (assert! (uuid-format-p "550e8400-e29b-41d4-a716-446655440000")))

;; Test uuid-v4-format-p - the version nibble must be 4
(local
 (assert! (uuid-v4-format-p "550e8400-e29b-41d4-a716-446655440000")))

;; Invalid: version nibble is 1, not 4
(local
 (assert! (not (uuid-v4-format-p "550e8400-e29b-11d4-a716-446655440000"))))

;; Invalid: wrong length
(local
 (assert! (not (uuid-format-p "550e8400-e29b-41d4-a716"))))

;; Invalid: wrong characters
(local
 (assert! (not (uuid-format-p "550e8400-e29b-41d4-a716-44665544000g"))))

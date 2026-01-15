; uuid-raw.lsp - Raw Lisp for UUID v4 generation
; Part of ACL2 Jupyter Kernel
;
; UUID v4 is random-based:
; - 128 bits (16 bytes) of random data
; - Format: xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx
; - Version nibble (position 13) set to 4
; - Variant nibble (position 17) set to 8, 9, a, or b (RFC 4122)
;
; Loaded via include-raw in uuid.lisp

(in-package "ACL2-KERNEL")

;;; Random state for UUID generation
;;; Use SBCL's MAKE-RANDOM-STATE with T for entropy from OS

(defparameter *uuid-random-state* 
  (make-random-state t)
  "Random state seeded from OS entropy for UUID generation.")

;;; Generate 16 random bytes
(defun generate-random-bytes-16 ()
  "Generate a list of 16 random bytes."
  (loop repeat 16 collect (random 256 *uuid-random-state*)))

;;; Convert a nibble (0-15) to hex char
(defun nibble-to-hex-char (n)
  "Convert nibble (0-15) to lowercase hex character."
  (declare (type (integer 0 15) n))
  (char "0123456789abcdef" n))

;;; Format 16 bytes as UUID v4 string
;;; Sets version nibble to 4 and variant nibble to (8 + low 2 bits)
(defun format-uuid-v4 (bytes)
  "Format 16 bytes as UUID v4 string xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx.
   Modifies byte 7 for version (4) and byte 9 for variant (8-b)."
  (let* ((b (copy-list bytes))
         ;; Set version nibble (high nibble of byte 7) to 4
         ;; Byte 7 becomes 0x4X where X is the low nibble
         (byte7 (nth 6 b))
         (new-byte7 (logior #x40 (logand byte7 #x0f)))
         ;; Set variant nibble (high nibble of byte 9) to 8-b
         ;; Byte 9 becomes 0x8X, 0x9X, 0xaX, or 0xbX
         (byte9 (nth 8 b))
         (new-byte9 (logior #x80 (logand byte9 #x3f))))
    (setf (nth 6 b) new-byte7)
    (setf (nth 8 b) new-byte9)
    ;; Format as xxxxxxxx-xxxx-xxxx-xxxx-xxxxxxxxxxxx
    ;; Positions: 0-3 hyphen 4-5 hyphen 6-7 hyphen 8-9 hyphen 10-15
    (with-output-to-string (s)
      (dotimes (i 4)
        (let ((byte (nth i b)))
          (write-char (nibble-to-hex-char (ash byte -4)) s)
          (write-char (nibble-to-hex-char (logand byte #x0f)) s)))
      (write-char #\- s)
      (dotimes (i 2)
        (let ((byte (nth (+ 4 i) b)))
          (write-char (nibble-to-hex-char (ash byte -4)) s)
          (write-char (nibble-to-hex-char (logand byte #x0f)) s)))
      (write-char #\- s)
      (dotimes (i 2)
        (let ((byte (nth (+ 6 i) b)))
          (write-char (nibble-to-hex-char (ash byte -4)) s)
          (write-char (nibble-to-hex-char (logand byte #x0f)) s)))
      (write-char #\- s)
      (dotimes (i 2)
        (let ((byte (nth (+ 8 i) b)))
          (write-char (nibble-to-hex-char (ash byte -4)) s)
          (write-char (nibble-to-hex-char (logand byte #x0f)) s)))
      (write-char #\- s)
      (dotimes (i 6)
        (let ((byte (nth (+ 10 i) b)))
          (write-char (nibble-to-hex-char (ash byte -4)) s)
          (write-char (nibble-to-hex-char (logand byte #x0f)) s))))))

;;; Main UUID generation function called from ACL2
(defun generate-uuid-raw ()
  "Generate a UUID v4 string. 
   Returns a 36-character string in format xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx."
  (format-uuid-v4 (generate-random-bytes-16)))

;;; Seed the random state from OS (call during initialization if needed)
(defun reseed-uuid-random-state ()
  "Reseed the UUID random state from OS entropy."
  (setf *uuid-random-state* (make-random-state t)))

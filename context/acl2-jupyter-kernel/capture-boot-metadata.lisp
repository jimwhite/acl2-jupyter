;;; capture-boot-metadata.lisp — Capture per-file ACL2 boot-strap event metadata
;;;
;;; This script replicates the two-pass boot-strap process from
;;; initialize-acl2 (interface-raw.lisp) but captures world-diff
;;; metadata (event landmarks) after each file's LD, writing per-file
;;; JSON to $ACL2_HOME/.boot-metadata/.
;;;
;;; IMPORTANT: This file uses acl2:: prefixed symbols and must be loaded
;;; AFTER init.lisp has been loaded (to create the ACL2 package).
;;; Use capture-boot-metadata-loader.lisp as the entry point.
;;;
;;; Usage:
;;;   cd /home/acl2
;;;   sbcl --dynamic-space-size 32000 --control-stack-size 64 \
;;;        --disable-ldb --disable-debugger --no-userinit \
;;;        --load /path/to/capture-boot-metadata-loader.lisp
;;;
;;; The script:
;;;   1. Loads init.lisp → load-acl2 (raw CL compilation artefacts)
;;;   2. Enters boot-strap mode
;;;   3. Pass 1: LD each file in *acl2-files* order (skipping -raw and
;;;      boot-strap-pass-2 files) with ld-skip-proofsp = 'initialize-acl2,
;;;      capturing world-diff events per file
;;;   4. Pass 2: LD *acl2-pass-2-files* with ld-skip-proofsp = 'include-book,
;;;      again capturing events per file
;;;   5. Writes manifest.json and per-file JSON files
;;;   6. Exits
;;;
;;; Output format (per file):
;;;   { "source_file": "axioms.lisp",
;;;     "stem": "axioms",
;;;     "pass": 1,
;;;     "position": 2,
;;;     "baseline_event_number": 0,
;;;     "final_event_number": 3456,
;;;     "event_count": 3456,
;;;     "events": ["(DEFUN FOO ...)", ...],
;;;     "package": "ACL2" }

(in-package "COMMON-LISP-USER")

;;; ── Output directory ──────────────────────────────────────────────

(defvar *metadata-dir*
  (let ((dir (or #+sbcl (sb-ext:posix-getenv "ACL2_BOOT_METADATA_DIR")
                 #-sbcl (ignore-errors (funcall (find-symbol "GETENV" "UIOP")
                                                "ACL2_BOOT_METADATA_DIR"))
                 ".boot-metadata")))
    (ensure-directories-exist
     (make-pathname :directory (append (pathname-directory
                                        (truename "."))
                                       (list dir))
                    :name "probe" :type "tmp"))
    (merge-pathnames (make-pathname :directory (list :relative dir))
                     (truename "."))))

;;; ── JSON writer (minimal, no dependencies) ────────────────────────

(defun json-escape (string)
  "Escape a string for JSON output."
  (with-output-to-string (out)
    (loop for ch across string do
      (case ch
        (#\\ (write-string "\\\\" out))
        (#\" (write-string "\\\"" out))
        (#\Newline (write-string "\\n" out))
        (#\Return (write-string "\\r" out))
        (#\Tab (write-string "\\t" out))
        (#\Backspace (write-string "\\b" out))
        (#\Page (write-string "\\f" out))
        (otherwise
         (if (< (char-code ch) 32)
             (format out "\\u~4,'0X" (char-code ch))
             (write-char ch out)))))))

(defun write-json-string-array (stream strings)
  "Write a JSON array of strings to STREAM."
  (write-char #\[ stream)
  (loop for (s . rest) on strings do
    (write-char #\" stream)
    (write-string (json-escape s) stream)
    (write-char #\" stream)
    (when rest (write-string ", " stream)))
  (write-char #\] stream))

(defun write-metadata-json (pathname alist)
  "Write an alist as a JSON object to PATHNAME.
   Values can be strings, integers, or lists of strings."
  (with-open-file (out pathname :direction :output
                                :if-exists :supersede
                                :if-does-not-exist :create)
    (write-char #\{ out)
    (loop for ((key . val) . rest) on alist do
      (format out "~%  \"~A\": " (json-escape (string key)))
      (etypecase val
        (string  (format out "\"~A\"" (json-escape val)))
        (integer (format out "~D" val))
        (null    (write-string "null" out))
        (list    (write-json-string-array out val))
        ((eql t) (write-string "true" out)))
      (when rest (write-char #\, out)))
    (format out "~%}~%")))

;;; ── World-diff event extraction ───────────────────────────────────
;;; Mirrors the logic in kernel.lisp evaluate-code.

(defun extract-events-since (baseline-world current-world)
  "Return (VALUES events forms) — parallel lists of depth-0
   event-landmark tuple strings and form strings from the world
   triples added since BASELINE-WORLD.

   EVENTS are printed with *print-case* :upcase (matching event tuples).
   FORMS are the original submitted code via access-event-tuple-form,
   printed with *print-case* :downcase (matching the kernel's forms output)."
  (let* ((scan (if baseline-world
                   (ldiff current-world baseline-world)
                   current-world))
         (event-tuples
           (loop for triple in scan
                 when (and (eq (car triple) 'acl2::event-landmark)
                           (eq (cadr triple) 'acl2::global-value))
                 collect (cddr triple)))
         ;; Keep only depth=0 (car is integer, not cons)
         (top-level
           (remove-if-not
            (lambda (et)
              (let ((inner (if (eq (car et) 'acl2::local) (cdr et) et)))
                (integerp (car inner))))
            event-tuples)))
    (let ((*package* (find-package "ACL2"))
          (*print-pretty* nil)
          (*print-length* nil)
          (*print-level* nil))
      (values
       ;; events: uppercase print of tuple (stripped of event number)
       (let ((*print-case* :upcase))
         (mapcar (lambda (et)
                   (let ((inner (if (eq (car et) 'acl2::local) (cdr et) et)))
                     (prin1-to-string (cdr inner))))
                 top-level))
       ;; forms: lowercase print of the original submitted code
       (let ((*print-case* :downcase))
         (mapcar (lambda (et)
                   (prin1-to-string
                    (acl2::access-event-tuple-form et)))
                 top-level))))))

(defun current-event-number ()
  "Return the current max absolute event number."
  (acl2::max-absolute-event-number (acl2::w acl2::*the-live-state*)))

;;; ── Main capture logic ────────────────────────────────────────────

(defvar *capture-results* nil
  "Alist of (stem . metadata-alist) collected during the capture run.")

(defun capture-file-ld (file-stem pass position ld-skip-proofsp
                         &optional pass-2-alist)
  "LD a single file and capture its world-diff metadata.
   Returns T on success, NIL on error."
  (let* ((state acl2::*the-live-state*)
         (world-before (acl2::w state))
         (event-before (current-event-number))
         (filename (or (cdr (assoc file-stem pass-2-alist :test #'equal))
                       (concatenate 'string file-stem "."
                                    acl2::*lisp-extension*))))
    (format t "~&;; [pass ~D, #~D] Loading ~A ...~%" pass position file-stem)
    (force-output)
    (let ((t0 (get-internal-real-time)))
      (multiple-value-bind (er val st)
          (acl2::ld-fn
           (acl2::ld-alist-raw filename ld-skip-proofsp :error)
           state
           nil)
        (declare (ignore val st))
        (multiple-value-bind (events forms)
            (extract-events-since world-before (acl2::w state))
          (let* ((elapsed (/ (- (get-internal-real-time) t0)
                             (float internal-time-units-per-second)))
                 (event-after (current-event-number))
                 (pkg (acl2::current-package state)))
            (cond
              (er
               (format t "~&;; ERROR loading ~A (pass ~D)~%" file-stem pass)
               (let ((meta `(("source_file" . ,(concatenate 'string file-stem "."
                                                             acl2::*lisp-extension*))
                             ("stem" . ,file-stem)
                             ("pass" . ,pass)
                             ("position" . ,position)
                             ("error" . t)
                             ("elapsed_seconds" . ,(round elapsed))
                             ("baseline_event_number" . ,event-before)
                             ("final_event_number" . ,event-after)
                             ("event_count" . ,(length events))
                             ("events" . ,events)
                             ("forms" . ,forms)
                             ("package" . ,pkg))))
                 (push (cons (format nil "~A-pass~D" file-stem pass) meta)
                       *capture-results*))
               nil)
              (t
               (format t "~&;; OK ~A: ~D events (~,1Fs)~%"
                       file-stem (length events) elapsed)
               (let ((meta `(("source_file" . ,(concatenate 'string file-stem "."
                                                             acl2::*lisp-extension*))
                             ("stem" . ,file-stem)
                             ("pass" . ,pass)
                             ("position" . ,position)
                             ("elapsed_seconds" . ,(round elapsed))
                             ("baseline_event_number" . ,event-before)
                             ("final_event_number" . ,event-after)
                             ("event_count" . ,(length events))
                             ("events" . ,events)
                             ("forms" . ,forms)
                             ("package" . ,pkg))))
                 (push (cons (format nil "~A-pass~D" file-stem pass) meta)
                       *capture-results*))
               t))))))))

(defun write-results ()
  "Write all captured metadata to JSON files and a manifest."
  (let ((manifest-entries nil))
    (dolist (entry (reverse *capture-results*))
      (let* ((key (car entry))
             (meta (cdr entry))
             (path (merge-pathnames
                    (make-pathname :name key :type "json")
                    *metadata-dir*)))
        (write-metadata-json path meta)
        (format t "~&;; Wrote ~A~%" path)
        ;; Manifest entry (without the bulky events list)
        (push `(("key" . ,key)
                ("stem" . ,(cdr (assoc "stem" meta :test #'equal)))
                ("pass" . ,(cdr (assoc "pass" meta :test #'equal)))
                ("position" . ,(cdr (assoc "position" meta :test #'equal)))
                ("event_count" . ,(cdr (assoc "event_count" meta :test #'equal)))
                ("baseline_event_number" . ,(cdr (assoc "baseline_event_number" meta :test #'equal)))
                ("final_event_number" . ,(cdr (assoc "final_event_number" meta :test #'equal))))
              manifest-entries)))
    ;; Write manifest
    (let ((manifest-path (merge-pathnames
                          (make-pathname :name "manifest" :type "json")
                          *metadata-dir*)))
      (with-open-file (out manifest-path :direction :output
                                         :if-exists :supersede
                                         :if-does-not-exist :create)
        (write-char #\{ out)
        ;; acl2_files ordering
        (format out "~%  \"acl2_files\": ")
        (write-json-string-array out (mapcar #'identity acl2::*acl2-files*))
        (format out ",~%  \"acl2_pass_2_files\": ")
        (write-json-string-array out (mapcar #'identity acl2::*acl2-pass-2-files*))
        (format out ",~%  \"files\": [")
        (loop for (entry . rest) on (reverse manifest-entries)
              for first = t then nil
              do
              (unless first (write-char #\, out))
              (format out "~%    {")
              (loop for ((k . v) . erest) on entry do
                (format out "\"~A\": " (json-escape k))
                (etypecase v
                  (string (format out "\"~A\"" (json-escape v)))
                  (integer (format out "~D" v))
                  (null (write-string "null" out)))
                (when erest (write-string ", " out)))
              (write-char #\} out))
        (format out "~%  ]~%}~%"))
      (format t "~&;; Wrote manifest: ~A~%" manifest-path))))

(defun safe-exit (&optional (code 0))
  "Exit cleanly — try ACL2's exit-lisp first, fall back to sb-ext:exit."
  (ignore-errors (acl2::exit-lisp))
  #+sbcl (sb-ext:exit :code code)
  #-sbcl (cl-user::quit code))

(defun run-capture ()
  "Main entry point: load ACL2, run 2-pass boot-strap with capture."
  (format t "~&;;~%;; ACL2 Boot-strap Metadata Capture~%;; Output: ~A~%;;~%"
          *metadata-dir*)

  ;; Step 1: init.lisp was already loaded by the loader script.
  ;; Step 2: Load raw CL artefacts via load-acl2
  (format t "~&;; Step 2: Loading raw ACL2 (load-acl2) ...~%")
  (acl2::load-acl2 :load-acl2-proclaims acl2::*do-proclaims*)

  ;; Step 3: Enter boot-strap mode (sets up primordial world)
  (format t "~&;; Step 3: Entering boot-strap mode ...~%")
  (let* ((*features* (cons :acl2-loop-only *features*))
         (state acl2::*the-live-state*))
    (declare (ignorable state))
    (acl2::set-initial-cbd)
    (makunbound 'acl2::*copy-of-common-lisp-symbols-from-main-lisp-package*)
    (acl2::enter-boot-strap-mode nil (acl2::get-os))

    ;; Step 4: Pass 1 — LD each file in :program mode
    (format t "~&;;~%;; === Pass 1: :program mode (ld-skip-proofsp = initialize-acl2) ===~%;;~%")
    (let ((position 0))
      (dolist (fl acl2::*acl2-files*)
        (incf position)
        (unless (or (equal fl "boot-strap-pass-2-a")
                    (equal fl "boot-strap-pass-2-b")
                    (acl2::raw-source-name-p fl))
          (unless (capture-file-ld fl 1 position 'acl2::initialize-acl2)
            (format t "~&;; FATAL: Pass 1 failed on ~A — aborting.~%" fl)
            (write-results)
            (safe-exit 1)))))

    ;; Step 5: Enter pass 2 and LD pass-2 files by filename
    ;; (We skip the read-file pre-caching that initialize-acl2 does,
    ;; as acl2::read-file can cause memory faults in this context.
    ;; ld-alist-raw handles filenames directly.)
    (format t "~&;;~%;; === Pass 2: :logic mode (ld-skip-proofsp = include-book) ===~%;;~%")
    (acl2::enter-boot-strap-pass-2)

    (let ((position 0))
      (dolist (fl acl2::*acl2-pass-2-files*)
        (incf position)
        (unless (capture-file-ld fl 2 position 'acl2::include-book)
          (format t "~&;; FATAL: Pass 2 failed on ~A — aborting.~%" fl)
          (write-results)
          (safe-exit 1)))))

  ;; Step 6: Write results
  (format t "~&;;~%;; Boot-strap capture complete.~%;;~%")
  (write-results)
  (format t "~&;; Done. ~D file(s) captured.~%" (length *capture-results*))
  (safe-exit 0))

;;; ── Auto-run on load ──────────────────────────────────────────────
(handler-case
    (run-capture)
  (serious-condition (c)
    (format *error-output* "~&;; FATAL ERROR: ~A~%" c)
    (format *error-output* "~&;; Writing partial results before exit ...~%")
    (ignore-errors (write-results))
    (sb-ext:exit :code 1)))

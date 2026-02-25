;;;; ACL2 Jupyter Kernel - Extra-World Symbol Metadata
;;;;
;;;; Captures metadata that is NOT in the ACL2 world event landmarks:
;;;;   1. Every symbol referenced in a cell with its resolved package and kind
;;;;   2. Classification of symbols (function, macro, theorem, constant, etc.)
;;;;   3. Dependency edges from defined symbols to referenced symbols
;;;;   4. Macro expansion tracking (original form vs translate1 output)
;;;;   5. Detection of raw CL-level side effects (new fboundp/boundp bindings)
;;;;
;;;; Symbol extraction works by walking the live s-expression that ACL2's own
;;;; reader (read-object) produced.  Since symbols are already interned with
;;;; the correct package by the reader, we have ground-truth resolution.
;;;; No separate parser (tree-sitter, Eclector) is needed.

(in-package #:acl2-jupyter)

;;; ---------------------------------------------------------------------------
;;; Symbol Extraction — Walk a read s-expression
;;; ---------------------------------------------------------------------------

(defun extract-symbols (form)
  "Walk FORM recursively, collecting every symbol into a hash table.
   Keys are symbols; values are plists with collected info:
     :OPERATOR T  — appeared in function position (car of a form)
     :ARGUMENT T  — appeared as an argument (non-car position)
   A symbol can have both :OPERATOR and :ARGUMENT set."
  (let ((table (make-hash-table :test 'eq)))
    (labels
        ((record (sym operator-p)
           (let ((entry (gethash sym table)))
             (unless entry
               (setf entry (list :operator nil :argument nil))
               (setf (gethash sym table) entry))
             (if operator-p
                 (setf (getf entry :operator) t)
                 (setf (getf entry :argument) t))))
         (walk (x operator-p)
           (cond
             ((symbolp x)
              (record x operator-p))
             ((consp x)
              ;; Car is in operator position when the form is a list
              (walk (car x) t)
              (walk-list (cdr x)))
             ;; Ignore atoms like numbers, strings, characters
             (t nil)))
         (walk-list (xs)
           (when (consp xs)
             (walk (car xs) nil)
             (walk-list (cdr xs)))))
      (walk form nil)
      table)))

;;; ---------------------------------------------------------------------------
;;; Symbol Classification — Query ACL2 world + CL level
;;; ---------------------------------------------------------------------------

(defun classify-symbol (sym wrld)
  "Return a keyword classifying SYM against the ACL2 world WRLD.
   Returns one of: :FUNCTION :MACRO :THEOREM :CONSTANT :STOBJ :VARIABLE
   :RAW-FUNCTION :SPECIAL-FORM :UNKNOWN.
   Multiple classifications are possible; returns the most specific."
  (cond
    ;; ACL2 world properties (most specific first)
    ((and (ignore-errors
            (not (eq :none (acl2::getpropc sym 'acl2::formals :none wrld)))))
     :function)
    ((ignore-errors (acl2::getpropc sym 'acl2::macro-args nil wrld))
     :macro)
    ((ignore-errors (acl2::getpropc sym 'acl2::theorem nil wrld))
     :theorem)
    ((ignore-errors (acl2::getpropc sym 'acl2::const nil wrld))
     :constant)
    ((ignore-errors (acl2::getpropc sym 'acl2::stobj nil wrld))
     :stobj)
    ;; CL level
    ((special-operator-p sym)
     :special-form)
    ((macro-function sym)
     :macro)
    ((fboundp sym)
     :raw-function)
    ((boundp sym)
     :variable)
    (t :unknown)))

(defun classify-symbol-safe (sym wrld)
  "Like classify-symbol but catches all errors, returning :UNKNOWN on failure."
  (handler-case (or (classify-symbol sym wrld) :unknown)
    (error () :unknown)))

;;; ---------------------------------------------------------------------------
;;; Symbol Table → JSON-Ready Format
;;; ---------------------------------------------------------------------------

(defun interesting-symbol-p (sym)
  "Return T if SYM should be included in metadata.
   Filters out ubiquitous symbols like T, NIL, QUOTE, and symbols
   from the KEYWORD package."
  (and sym
       (symbolp sym)
       (not (eq sym t))
       (not (eq sym nil))
       (not (eq sym 'quote))
       (not (eq sym 'acl2::quote))
       (not (keywordp sym))
       ;; Skip gensyms (uninterned symbols)
       (symbol-package sym)))

(defun format-symbol-entry (sym plist wrld)
  "Format a single symbol entry as a JSON-ready alist.
   Returns ((\"name\" . name) (\"package\" . pkg) (\"kind\" . kind)
            (\"operator\" . bool) (\"argument\" . bool))."
  (let ((*print-case* :downcase))
    (list (cons "name" (symbol-name sym))
          (cons "package" (package-name (symbol-package sym)))
          (cons "kind" (string-downcase
                        (symbol-name (classify-symbol-safe sym wrld))))
          (cons "operator" (if (getf plist :operator)
                               :true :false))
          (cons "argument" (if (getf plist :argument)
                               :true :false)))))

(defun symbols-table-to-json (table wrld)
  "Convert a symbol hash table (from extract-symbols) to a vector
   of JSON-ready alists for metadata emission."
  (let ((entries nil))
    (maphash (lambda (sym plist)
               (when (interesting-symbol-p sym)
                 (push (cons :object-alist
                             (format-symbol-entry sym plist wrld))
                       entries)))
             table)
    (coerce (nreverse entries) 'vector)))

;;; ---------------------------------------------------------------------------
;;; Raw CL-Level Side Effect Detection
;;; ---------------------------------------------------------------------------

(defun snapshot-bindings (symbols)
  "Snapshot fboundp/boundp status for each symbol in SYMBOLS (a hash table).
   Returns an alist of (sym . (:fboundp bool :boundp bool))."
  (let ((snap nil))
    (maphash (lambda (sym plist)
               (declare (ignore plist))
               (when (interesting-symbol-p sym)
                 (push (cons sym (list :fboundp (and (fboundp sym) t)
                                       :boundp  (and (boundp sym) t)))
                       snap)))
             symbols)
    snap))

(defun detect-raw-changes (pre-snapshot post-symbols)
  "Compare PRE-SNAPSHOT against POST-SYMBOLS (hash table with fresh
   fboundp/boundp checks).  Returns a list of strings naming symbols
   that gained fboundp or boundp status."
  (let ((changes nil))
    (maphash (lambda (sym plist)
               (declare (ignore plist))
               (when (interesting-symbol-p sym)
                 (let ((pre (cdr (assoc sym pre-snapshot :test #'eq))))
                   (when pre
                     (let ((was-fbound (getf pre :fboundp))
                           (was-bound  (getf pre :boundp))
                           (now-fbound (and (fboundp sym) t))
                           (now-bound  (and (boundp sym) t)))
                       (when (or (and now-fbound (not was-fbound))
                                 (and now-bound  (not was-bound)))
                         (let ((*print-case* :downcase))
                           (push (format nil "~A::~A"
                                         (package-name (symbol-package sym))
                                         (symbol-name sym))
                                 changes))))))))
             post-symbols)
    (nreverse changes)))

;;; ---------------------------------------------------------------------------
;;; Dependency Edge Extraction
;;; ---------------------------------------------------------------------------

(defun extract-defined-names (event-tuples)
  "Extract the names of symbols defined by EVENT-TUPLES.
   Each depth-0 tuple looks like:
     (n ((types...) name . mode) form-type form-name formals body...)
   where the second element is a summary subtuple.
   Deep tuples or stripped tuples may vary; we look at the summary.
   Returns a list of symbols."
  (let ((names nil))
    (dolist (et event-tuples)
      (let ((inner (if (eq (car et) 'acl2::local) (cdr et) et)))
        ;; Strip event number if present
        (let* ((rest (if (integerp (car inner)) (cdr inner) inner))
               ;; (car rest) is the summary subtuple: ((types) name . mode)
               (summary (car rest)))
          (when (consp summary)
            (let ((event-types (let ((et-head (car summary)))
                                 (if (listp et-head) et-head (list et-head))))
                  (name (cadr summary)))
              (when (and (symbolp name)
                         (intersection event-types
                                       '(acl2::defun acl2::defuns
                                         acl2::defmacro acl2::defthm
                                         acl2::defconst acl2::defstobj
                                         acl2::defchoose acl2::defpkg
                                         acl2::defabbrev acl2::mutual-recursion
                                         acl2::defaxiom acl2::deflabel
                                         acl2::verify-guards
                                         acl2::in-theory
                                         acl2::encapsulate)))
                (push name names)))))))
    (nreverse names)))

(defun get-symbol-body (sym wrld)
  "Retrieve the body/definition of SYM from the ACL2 world.
   Tries unnormalized-body (functions), macro-body (macros),
   theorem (theorems), const (constants) in order."
  (or (ignore-errors (acl2::getpropc sym 'acl2::unnormalized-body nil wrld))
      (ignore-errors (acl2::getpropc sym 'acl2::macro-body nil wrld))
      (ignore-errors (acl2::getpropc sym 'acl2::theorem nil wrld))
      ;; For constants, the value itself might reference other symbols
      (ignore-errors (acl2::getpropc sym 'acl2::const nil wrld))))

(defun extract-body-references (sym wrld)
  "Extract symbols referenced in SYM's body from the ACL2 world WRLD.
   Returns a list of symbol name strings (package::name format)."
  (let ((body (get-symbol-body sym wrld)))
    (when body
      (let ((table (extract-symbols body))
            (refs nil))
        (maphash (lambda (ref-sym plist)
                   (declare (ignore plist))
                   (when (and (interesting-symbol-p ref-sym)
                              (not (eq ref-sym sym)))
                     (let ((*print-case* :downcase))
                       (push (format nil "~A::~A"
                                     (package-name (symbol-package ref-sym))
                                     (symbol-name ref-sym))
                             refs))))
                 table)
        (nreverse refs)))))

(defun build-dependency-edges (event-tuples wrld)
  "Build dependency edges for symbols defined in EVENT-TUPLES.
   Returns an alist of (defined-name-string . (ref-name-string ...))."
  (let ((edges nil))
    (dolist (sym (extract-defined-names event-tuples))
      (let ((refs (extract-body-references sym wrld)))
        (when refs
          (let ((*print-case* :downcase))
            (push (cons (format nil "~A::~A"
                                (package-name (symbol-package sym))
                                (symbol-name sym))
                        (coerce refs 'vector))
                  edges)))))
    ;; Return as JSON-ready object-plist
    (when edges
      (cons :object-alist (nreverse edges)))))

;;; ---------------------------------------------------------------------------
;;; Macro Expansion Capture
;;; ---------------------------------------------------------------------------

(defun try-translate (form state)
  "Attempt to translate FORM via ACL2's translate1, returning the
   translated term or NIL on failure.  Translation performs full
   macro expansion within the ACL2 logic."
  (ignore-errors
    (let ((wrld (w state)))
      (multiple-value-bind (erp trans bindings new-state)
          (acl2::translate1 form
                            :stobjs-out
                            '((:stobjs-out . :stobjs-out))
                            t            ; known-stobjs
                            'acl2-jupyter ; ctx
                            wrld
                            state)
        (declare (ignore bindings new-state))
        (unless erp trans)))))

(defun capture-expansion (form state)
  "If FORM involves macro expansion, return an alist
   ((\"form\" . original-string) (\"expansion\" . expanded-string))
   or NIL if the form doesn't expand (or translation fails)."
  (let ((translated (try-translate form state)))
    (when (and translated
               (not (equal translated form)))
      (let ((*package* (find-package
                        (acl2::current-package *the-live-state*)))
            (*print-case* :downcase)
            (*print-pretty* t))
        (cons :object-alist
              (list (cons "form" (prin1-to-string form))
                    (cons "expansion" (prin1-to-string translated))))))))

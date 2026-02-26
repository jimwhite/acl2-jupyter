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

(defun defun-like-p (sym)
  "Return T if SYM names a definition form whose second argument is
   a formal parameter list (e.g. DEFUN, DEFUND, DEFMACRO, DEFUN$, etc.)."
  (member sym '(acl2::defun  acl2::defund
                acl2::defmacro
                acl2::defun$  acl2::defund$
                acl2::defun-sk acl2::defun-sk$
                acl2::define)
          :test #'eq))

(defun cl-defun-like-p (sym)
  "Return T if SYM names a CL definition form whose second argument is
   a name (and optionally third is a formal parameter list).
   Covers standard CL definition forms beyond ACL2's set."
  (or (defun-like-p sym)
      (member sym '(cl:defun cl:defmacro cl:defgeneric cl:defmethod
                   cl:deftype cl:defstruct cl:defclass) :test #'eq)))

(defun cl-definition-form-head-p (sym)
  "Like definition-form-head-p but extended for Common Lisp forms.
   Used for raw CL source analysis."
  (or (definition-form-head-p sym)  ; all ACL2 forms
      (member sym '(cl:defvar cl:defparameter cl:defconstant
                   cl:defstruct cl:defclass cl:defgeneric
                   cl:defmethod cl:deftype
                   cl:define-condition cl:define-compiler-macro)
              :test #'eq)))

(defun extract-symbols (form &optional cl-mode-p)
  "Walk FORM recursively, collecting every symbol into a hash table.
   Keys are symbols; values are plists with collected info:
     :OPERATOR T  — appeared in function position (car of a form)
     :ARGUMENT T  — appeared as an argument (non-car position)
   A symbol can have both :OPERATOR and :ARGUMENT set.
   Argument lists of definition forms (defun, defmacro, etc.) are
   walked as flat data so formal parameters are never marked operator.
   When CL-MODE-P is T, uses cl-defun-like-p for broader coverage."
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
              ;; Recognise (defun name (formals...) body ...) and similar:
              ;; walk the formals list as flat data (all :argument, no :operator).
              (let ((head (car x)))
                (cond
                  ((and (symbolp head)
                        (if cl-mode-p
                            (cl-defun-like-p head)
                            (defun-like-p head)))
                   ;; head = defun-like operator
                   (record head t)
                   ;; second element = name being defined
                   (when (cddr x)               ; need at least (op name formals ...)
                     (walk (cadr x) nil)         ; name — argument
                     (walk-flat (caddr x))       ; formals — all arguments
                     (walk-list (cdddr x))))     ; body & rest
                  (t
                   ;; Normal list: car is operator position
                   (walk (car x) t)
                   (walk-list (cdr x))))))
             ;; Ignore atoms like numbers, strings, characters
             (t nil)))
         (walk-flat (x)
           "Walk X treating every symbol as :ARGUMENT, no operator positions.
            Used for formal parameter lists and similar flat data."
           (cond
             ((symbolp x)
              (record x nil))
             ((consp x)
              (walk-flat (car x))
              (walk-flat (cdr x)))
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

(defun reclassify-unknown-symbols (symbols-vector wrld)
  "Re-classify any symbol entries in SYMBOLS-VECTOR that have kind \"unknown\".
   Mutates the vector entries in place.  Called after eval when the world
   has been updated with new definitions."
  (loop for i from 0 below (length symbols-vector)
        for entry = (aref symbols-vector i)
        ;; entry is (:object-alist ("name" . n) ("package" . p) ("kind" . k) ...)
        for alist = (cdr entry)
        for kind-cell = (assoc "kind" alist :test #'string=)
        when (and kind-cell (string= (cdr kind-cell) "unknown"))
          do (let* ((name-cell (assoc "name" alist :test #'string=))
                    (pkg-cell  (assoc "package" alist :test #'string=))
                    (sym (ignore-errors
                           (find-symbol (string-upcase (cdr name-cell))
                                        (cdr pkg-cell)))))
               (when sym
                 (let ((new-kind (string-downcase
                                  (symbol-name
                                   (classify-symbol-safe sym wrld)))))
                   (unless (string= new-kind "unknown")
                     (setf (cdr kind-cell) new-kind)))))))

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
;;; Dependency Edge Extraction (source-based pre/post classify diff)
;;; ---------------------------------------------------------------------------

(defun extract-newly-defined (kind-snapshot post-wrld)
  "Return the list of symbols from KIND-SNAPSHOT whose pre-eval kind was
   :UNKNOWN but whose post-eval kind (via CLASSIFY-SYMBOL-SAFE) is no
   longer :UNKNOWN.  These are the symbols defined by the current cell."
  (loop for (sym . pre-kind) in kind-snapshot
        when (and (eq pre-kind :unknown)
                  (not (eq :unknown (classify-symbol-safe sym post-wrld))))
          collect sym))

(defun extract-event-defined-names (event-tuples)
  "Extract symbol names from event tuple summaries.
   Each depth-0 tuple is (n summary form-type form-name formals body ...).
   The summary is ((event-types...) name . mode).
   Unlike the old extract-defined-names, this does NOT hardcode a list of
   event types — any tuple whose summary has a symbol in the name position
   is included.  This catches re-definitions in bootstrap pass 2 where the
   kind-snapshot diff sees no change."
  (let ((names nil))
    (dolist (et event-tuples)
      (let ((inner (if (eq (car et) 'acl2::local) (cdr et) et)))
        (let* ((rest (if (integerp (car inner)) (cdr inner) inner))
               (summary (car rest)))
          (when (consp summary)
            (let ((name (cadr summary)))
              (when (and (symbolp name)
                         (interesting-symbol-p name))
                (pushnew name names :test #'eq)))))))
    (nreverse names)))

(defun definition-form-head-p (sym)
  "Return T if SYM names a form whose second element (cadr) is the name
   being defined.  Covers defun variants, defmacro, defthm, defconst, etc.
   Used to extract defined names directly from source forms."
  (or (defun-like-p sym)          ; defun, defund, defmacro, defun$, etc.
      (member sym '(acl2::defthm acl2::defthmd
                   acl2::defconst
                   acl2::defstobj acl2::defabsstobj
                   acl2::deflabel
                   acl2::add-macro-fn
                   acl2::verify-termination-boot-strap
                   acl2::verify-guards
                   acl2::defchoose
                   acl2::defattach
                   acl2::defun-df)
              :test #'eq)))

(defun extract-source-defined-names (source-forms)
  "Extract defined symbol names directly from source forms.
   For forms like (defun NAME ...), (defmacro NAME ...), (defconst NAME ...),
   etc., the second element is the name being defined.
   This catches definitions that produce no event tuples in bootstrap pass 2
   (redundant forms) and definitions whose event tuples use a non-symbol name
   position (e.g. TABLE events with 0 in the name slot)."
  (let ((names nil))
    (dolist (form source-forms)
      (when (and (consp form)
                 (symbolp (car form))
                 (definition-form-head-p (car form))
                 (consp (cdr form))
                 (symbolp (cadr form))
                 (interesting-symbol-p (cadr form)))
        (pushnew (cadr form) names :test #'eq)))
    (nreverse names)))

(defun build-source-dependencies (kind-snapshot post-wrld source-forms
                                  &optional event-tuples)
  "Build dependency edges using the pre/post classify diff approach,
   augmented by event tuple extraction and source-form analysis.
   KIND-SNAPSHOT is an alist of (sym . pre-eval-kind).
   POST-WRLD is the ACL2 world after eval.
   SOURCE-FORMS is a list of live s-expressions from the cell.
   EVENT-TUPLES (optional) provides event-landmark tuples from the world diff.

   Three signals are unioned to find what the cell defines:
     1. Kind-snapshot diff — catches fresh definitions (unknown → known)
     2. Event tuple names — catches re-defs that produce event landmarks
     3. Source form heads — catches re-defs with no event landmarks and
        forms whose event tuples use non-symbol names (e.g. TABLE events)

   For each defined symbol, find the source form that mentions it, walk that
   form to extract all referenced symbols, and emit an edge from the defined
   symbol to its references.

   For compound forms where multiple defined symbols match the same form,
   each gets the full reference set minus itself (over-broad, accepted)."
  (let* ((from-kind-diff (extract-newly-defined kind-snapshot post-wrld))
         (from-events (when event-tuples
                        (extract-event-defined-names event-tuples)))
         (from-source (extract-source-defined-names source-forms))
         ;; Union all three signals
         (newly-defined (union (union from-kind-diff from-events :test #'eq)
                               from-source :test #'eq)))
    (when newly-defined
      ;; Pre-compute extract-symbols tables for each source form
      (let ((form-tables (mapcar (lambda (form)
                                   (cons form (extract-symbols form)))
                                 source-forms))
            (edges nil))
        (dolist (sym newly-defined)
          ;; Find the source form that mentions this symbol
          (let ((matching-table nil))
            (dolist (ft form-tables)
              (when (gethash sym (cdr ft))
                (setf matching-table (cdr ft))
                (return)))
            (when matching-table
              ;; Extract all interesting references minus the defined symbol
              (let ((refs nil))
                (maphash (lambda (ref-sym plist)
                           (declare (ignore plist))
                           (when (and (interesting-symbol-p ref-sym)
                                      (not (eq ref-sym sym)))
                             (let ((*print-case* :downcase))
                               (push (format nil "~A::~A"
                                             (package-name
                                              (symbol-package ref-sym))
                                             (symbol-name ref-sym))
                                     refs))))
                         matching-table)
                (when refs
                  (let ((*print-case* :downcase))
                    (push (cons (format nil "~A::~A"
                                        (package-name (symbol-package sym))
                                        (symbol-name sym))
                                (coerce (nreverse refs) 'vector))
                          edges)))))))
        (when edges
          (cons :object-alist (nreverse edges)))))))

;;; ---------------------------------------------------------------------------
;;; Trust Tag Tracking (Phase 5b)
;;; ---------------------------------------------------------------------------

(defun diff-ttags-seen (before-alist after-alist)
  "Compare BEFORE-ALIST and AFTER-ALIST (ttags-seen world global format:
   alist of (ttag-keyword . (book-name-list))).
   Returns a list of JSON-ready alists for new or extended trust tag entries:
   ((:object-alist (\"tag\" . \":foo\") (\"books\" . #(\"bar\"))))
   A ttag is 'new' if it appears in AFTER but not BEFORE, or if its
   book list is longer in AFTER than BEFORE."
  (let ((new-tags nil))
    (dolist (after-entry after-alist)
      (let* ((tag (car after-entry))
             (after-books (cdr after-entry))
             (before-entry (assoc tag before-alist :test #'equal))
             (before-books (cdr before-entry)))
        ;; New tag (not in before) or extended book list
        (when (or (null before-entry)
                  (> (length after-books) (length before-books)))
          ;; Compute only the new books (in after but not before)
          (let ((new-books (if before-entry
                               (set-difference after-books before-books
                                               :test #'equal)
                               after-books)))
            (let ((*print-case* :downcase))
              (push (cons :object-alist
                          (list (cons "tag" (prin1-to-string tag))
                                (cons "books"
                                      (coerce
                                       (mapcar #'prin1-to-string new-books)
                                       'vector))))
                    new-tags))))))
    (nreverse new-tags)))

;;; ---------------------------------------------------------------------------
;;; Include-Raw File Extraction (Phase 5a)
;;; ---------------------------------------------------------------------------

(defun extract-include-raw-files (source-forms)
  "Walk SOURCE-FORMS looking for (include-raw \"filename\" ...) calls.
   Returns a list of filename strings (the cadr of each include-raw form).
   Handles both ACL2::INCLUDE-RAW and any package-qualified variant."
  (let ((files nil))
    (labels ((walk-for-include-raw (form)
               (when (consp form)
                 (let ((head (car form)))
                   (when (and (symbolp head)
                              (string= (symbol-name head) "INCLUDE-RAW")
                              (consp (cdr form))
                              (stringp (cadr form)))
                     (pushnew (cadr form) files :test #'string=)))
                 ;; Recurse into sub-forms (progn, encapsulate, etc.)
                 (when (and (symbolp (car form))
                            (member (symbol-name (car form))
                                    '("PROGN" "PROGN!" "ENCAPSULATE"
                                      "WITH-OUTPUT" "LOCAL")
                                    :test #'string=))
                   (dolist (sub (cdr form))
                     (walk-for-include-raw sub))))))
      (dolist (form source-forms)
        (walk-for-include-raw form)))
    (nreverse files)))

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

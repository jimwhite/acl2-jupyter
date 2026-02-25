;;;; lisp2nb.lisp — Convert .lisp source to .ipynb using rewrite-cl
;;;;
;;;; Usage:
;;;;   sbcl --load lisp2nb.lisp -- [--force] [--fenced] INPUT.lisp [INPUT2.lisp ...] [-o DIR]
;;;;
;;;; This replaces the tree-sitter based Python converter for ACL2 .lisp
;;;; files.  It uses rewrite-cl (a CL-native source parser) which handles
;;;; all Common Lisp syntax correctly, avoiding the tree-sitter grammar
;;;; bugs that caused split cells.
;;;;
;;;; SPDX-License-Identifier: MIT

;;; ─── Bootstrap ──────────────────────────────────────────────────────

(require :asdf)

;; Make rewrite-cl and yason findable.
(let ((here (make-pathname :defaults *load-truename* :name nil :type nil)))
  (pushnew (merge-pathnames #p"../rewrite-cl/" here) asdf:*central-registry*
           :test #'equal))

(asdf:load-system "rewrite-cl" :verbose nil)
(ql:quickload '("yason" "babel") :silent t)

(defpackage #:lisp2nb
  (:use #:cl)
  (:export #:convert-file #:convert-directory #:main))

(in-package #:lisp2nb)

;;; ─── Markdown bracket styles ────────────────────────────────────────

(defvar *markdown-bracket* :none
  "How to bracket comment text in markdown cells.
:NONE — bare text, :FENCED — wrapped in ``` fenced code block,
:PRE — wrapped in <pre>…</pre>.")

(defun format-markdown-source (text)
  "Wrap TEXT according to *MARKDOWN-BRACKET*."  
  (ecase *markdown-bracket*
    (:none text)
    (:fenced (format nil "```~%~A~%```" text))
    (:pre (format nil "<pre>~%~A~%</pre>" text))))

(defun bracket-prefix-len ()
  "Number of characters the bracket prefix adds."
  (ecase *markdown-bracket*
    (:none 0)
    (:fenced 4)   ; "```\n"
    (:pre 6)))    ; "<pre>\n"

;;; ─── Node classification ───────────────────────────────────────────

(defun comment-node-p (node)
  "True for line comments and block comments."
  (member (rewrite-cl.node:node-tag node) '(:comment :block-comment)))

(defun newline-node-p (node)
  (eq (rewrite-cl.node:node-tag node) :newline))

(defun whitespace-node-p (node)
  (eq (rewrite-cl.node:node-tag node) :whitespace))

(defun form-node-p (node)
  "True for anything that is not whitespace, newline, or comment."
  (not (member (rewrite-cl.node:node-tag node)
               '(:comment :block-comment :newline :whitespace))))

;;; ─── Classifying top-level node runs ───────────────────────────────
;;;
;;; We need to detect "blank lines" — runs of whitespace that contain
;;; two or more newlines.  rewrite-cl gives us separate :NEWLINE and
;;; :WHITESPACE nodes.  A blank line is when we see two :NEWLINE nodes
;;; with only :WHITESPACE between them.

(defstruct classified-node
  "Wrapper around a rewrite-cl node with classification."
  (kind nil :type (member :comment :blank :form))
  (text "" :type string)
  ;; Byte offset into the source file (computed by walking).
  (start-byte 0 :type fixnum)
  (end-byte 0 :type fixnum)
  ;; Original rewrite-cl node (only for :form nodes).
  (orig-node nil))

(defun classify-top-level-nodes (nodes)
  "Walk the flat list of rewrite-cl nodes and produce a list of
CLASSIFIED-NODEs (kind = :COMMENT, :BLANK, or :FORM).

Consecutive newlines (2+) are collapsed into a single :BLANK.
Whitespace and single newlines between forms are discarded."
  (let ((result '())
        (byte-pos 0))
    (labels ((node-byte-len (n)
               (length (babel:string-to-octets
                        (rewrite-cl.node:node-string n)
                        :encoding :utf-8)))
             (advance (n)
               (let ((len (node-byte-len n)))
                 (prog1 byte-pos
                   (incf byte-pos len)))))
      (let ((i 0)
            (len (length nodes)))
        (loop while (< i len) do
          (let ((node (nth i nodes)))
            (cond
              ;; Comment nodes.
              ((comment-node-p node)
               (let ((start (advance node)))
                 (push (make-classified-node
                        :kind :comment
                        :text (rewrite-cl.node:node-string node)
                        :start-byte start
                        :end-byte byte-pos)
                       result))
               (incf i))

              ;; Newline — check if this starts a blank line (2+ newlines).
              ((newline-node-p node)
               (let ((start (advance node))
                     (nl-count 1))
                 (incf i)
                 ;; Consume following whitespace and newlines.
                 (loop while (< i len)
                       for next = (nth i nodes)
                       while (or (newline-node-p next)
                                 (whitespace-node-p next))
                       do (when (newline-node-p next)
                            (incf nl-count))
                          (advance next)
                          (incf i))
                 (when (>= nl-count 2)
                   (push (make-classified-node
                          :kind :blank
                          :text ""
                          :start-byte start
                          :end-byte byte-pos)
                         result))))

              ;; Plain whitespace (not newline) — skip.
              ((whitespace-node-p node)
               (advance node)
               (incf i))

              ;; Form — everything else.
              (t
               (let ((start (advance node)))
                 (push (make-classified-node
                        :kind :form
                        :text (rewrite-cl.node:node-string node)
                        :start-byte start
                        :end-byte byte-pos
                        :orig-node node)
                       result))
               (incf i)))))))
    (nreverse result)))

;;; ─── Grouping into cells ───────────────────────────────────────────
;;;
;;; Same logic as converter.py _group_nodes_into_cells:
;;;
;;; - Detached comments: comment run followed by blank → markdown cell
;;; - Attached comments: comment run touching next form → code cell
;;; - Forms without preceding comments → standalone code cell

(defstruct cell
  "A notebook cell."
  (type "code" :type string)       ; "code" or "markdown"
  (source "" :type string)
  (start-byte 0 :type fixnum)
  (end-byte 0 :type fixnum)
  (comment-chars 0 :type fixnum)   ; chars of comment at start of source
  (form-node nil))                 ; original rewrite-cl node (for code cells)

(defun group-nodes-into-cells (classified-nodes source-bytes)
  "Group CLASSIFIED-NODES into CELLs following the detached/attached logic."
  (let ((cells '())
        (run '())          ; current comment run (list of classified-nodes)
        (in-run nil))

    (labels
        ((emit-markdown (node-list)
           "Emit comment nodes as a markdown cell."
           (let ((comments (remove-if-not
                            (lambda (n) (eq (classified-node-kind n) :comment))
                            node-list)))
             (when comments
               (let* ((start (classified-node-start-byte (first comments)))
                      (end (classified-node-end-byte (car (last comments))))
                      (text (babel:octets-to-string
                             (subseq source-bytes start end)
                             :encoding :utf-8))
                      (text (string-right-trim '(#\Newline) text)))
                 (push (make-cell :type "markdown"
                                  :source text
                                  :start-byte start
                                  :end-byte end
                                  :comment-chars (length text))
                       cells)))))

         (flush-run-and-form (form-node)
           "Process accumulated run when a form is encountered."
           (cond
             ;; No comment run — emit form alone.
             ((null run)
              (push (make-cell :type "code"
                               :source (classified-node-text form-node)
                               :start-byte (classified-node-start-byte form-node)
                               :end-byte (classified-node-end-byte form-node)
                               :comment-chars 0
                               :form-node (classified-node-orig-node form-node))
                    cells))

             ;; Run ends with blank → detached.
             ((eq (classified-node-kind (car (last run))) :blank)
              (emit-markdown run)
              (push (make-cell :type "code"
                               :source (classified-node-text form-node)
                               :start-byte (classified-node-start-byte form-node)
                               :end-byte (classified-node-end-byte form-node)
                               :comment-chars 0
                               :form-node (classified-node-orig-node form-node))
                    cells))

             ;; Run ends with comment → attached to the form.
             (t
              (let ((last-blank-idx nil))
                ;; Find last blank in run.
                (loop for i from (1- (length run)) downto 0
                      when (eq (classified-node-kind (nth i run)) :blank)
                        do (setf last-blank-idx i) (return))
                (let ((attached-part
                        (if last-blank-idx
                            (progn
                              (emit-markdown (subseq run 0 last-blank-idx))
                              (subseq run (1+ last-blank-idx)))
                            run)))
                  ;; Build code cell: attached comments + form.
                  (let* ((att-start (classified-node-start-byte
                                     (first attached-part)))
                         (code-end (classified-node-end-byte form-node))
                         (text (babel:octets-to-string
                                (subseq source-bytes att-start code-end)
                                :encoding :utf-8))
                         (text (string-right-trim '(#\Newline) text))
                         (comment-chars (- (length text)
                                           (length (classified-node-text
                                                    form-node)))))
                    (push (make-cell :type "code"
                                     :source text
                                     :start-byte att-start
                                     :end-byte code-end
                                     :comment-chars comment-chars
                                     :form-node (classified-node-orig-node
                                                 form-node))
                          cells))))))

           (setf run '()
                 in-run nil)))

      ;; Main loop.
      (dolist (node classified-nodes)
        (case (classified-node-kind node)
          (:comment
           (setf in-run t)
           (push node run))
          (:blank
           (when in-run
             (push node run)))
          (:form
           ;; Reverse run so it's in order.
           (setf run (nreverse run))
           (flush-run-and-form node))))

      ;; Trailing comments at EOF.
      (when run
        (setf run (nreverse run))
        (emit-markdown run)))

    (nreverse cells)))

;;; ─── Inline comment & docstring annotation ─────────────────────────
;;;
;;; These mirror converter.py's _find_inline_comments and _find_docstrings.
;;; They walk a form's rewrite-cl node tree to find comments and docstrings
;;; within the form body, returning [char-start, char-end] spans relative
;;; to the cell's source string.

(defun node-open-len (node)
  "Return the length of NODE's opening delimiter (for container nodes).
For seq-nodes this is the open paren/bracket; for reader-macro and
quote nodes this is the prefix string. Returns 0 for leaf nodes."
  (typecase node
    (rewrite-cl.node::seq-node
     (length (rewrite-cl.node::seq-node-open node)))
    (rewrite-cl.node::reader-macro-node
     (length (rewrite-cl.node::reader-macro-node-prefix node)))
    (rewrite-cl.node::quote-node
     (length (rewrite-cl.node::quote-node-prefix node)))
    (t 0)))

(defun node-close-len (node)
  "Return the length of NODE's closing delimiter.
For seq-nodes this is the close paren/bracket. Others are 0."
  (typecase node
    (rewrite-cl.node::seq-node
     (length (rewrite-cl.node::seq-node-close node)))
    (t 0)))

(defun find-inner-comments (form-node form-char-offset)
  "Find comment nodes inside FORM-NODE (recursively).
Returns a list of (start end) lists as character offsets from the
start of the cell source. FORM-CHAR-OFFSET is the character position
where the form begins within the cell source."
  (let ((spans '())
        (pos form-char-offset))
    (labels
        ((walk (node)
           (let ((tag (rewrite-cl.node:node-tag node)))
             (cond
               ;; Comment node — record its span.
               ((member tag '(:comment :block-comment))
                (let* ((text (rewrite-cl.node:node-string node))
                       (trimmed (string-right-trim '(#\Newline) text))
                       (start pos))
                  (push (list start (+ start (length trimmed))) spans))
                (incf pos (length (rewrite-cl.node:node-string node))))

               ;; Container node — recurse through children.
               ((rewrite-cl.node:node-inner-p node)
                (incf pos (node-open-len node))
                (dolist (child (rewrite-cl.node:node-children node))
                  (walk child))
                (incf pos (node-close-len node)))

               ;; Leaf node — just advance.
               (t
                (incf pos (length (rewrite-cl.node:node-string node))))))))
      (walk form-node))
    (nreverse spans)))

(defun string-node-p (node)
  "True if NODE is a string literal."
  (eq (rewrite-cl.node:node-tag node) :string))

(defun symbol-node-p (node)
  "True if NODE is a symbol."
  (eq (rewrite-cl.node:node-tag node) :symbol))

(defun def-keyword-p (text)
  "True if TEXT (a symbol name) contains \"def\" (case-insensitive)."
  (search "def" (string-downcase text)))

(defun semantic-children (node)
  "Return the non-whitespace, non-newline children of NODE."
  (remove-if (lambda (c)
               (member (rewrite-cl.node:node-tag c)
                       '(:whitespace :newline)))
             (rewrite-cl.node:node-children node)))

(defun child-char-offset (root target base-offset)
  "Compute the character offset of TARGET node within ROOT's source text.
BASE-OFFSET is ROOT's character position in the cell source.
Returns the character offset of TARGET, or NIL if not found."
  (let ((pos base-offset)
        (found nil))
    (labels
        ((walk (node)
           (when found (return-from walk))
           (cond
             ;; Found the target.
             ((eq node target)
              (setf found pos)
              ;; Advance past it so caller position tracking stays consistent.
              (incf pos (length (rewrite-cl.node:node-string node))))

             ;; Container — recurse.
             ((rewrite-cl.node:node-inner-p node)
              (incf pos (node-open-len node))
              (dolist (child (rewrite-cl.node:node-children node))
                (walk child)
                (when found (return)))
              (unless found
                (incf pos (node-close-len node))))

             ;; Leaf — advance.
             (t
              (incf pos (length (rewrite-cl.node:node-string node)))))))
      (walk root))
    found))

(defun find-docstrings (form-node form-char-offset)
  "Find docstrings in FORM-NODE using a positional heuristic.
A string literal at position 4 (1-indexed among semantic children)
in a form whose first symbol contains \"def\" is treated as a
docstring, provided it is not the last semantic child.
Returns a list of (start end) character-offset pairs."
  ;; Only applies to list forms.
  (unless (and (rewrite-cl.node:node-inner-p form-node)
               (eq (rewrite-cl.node:node-tag form-node) :list))
    (return-from find-docstrings '()))

  (let ((sem (semantic-children form-node)))
    ;; First semantic child must be a symbol containing "def".
    (unless (and sem
                (symbol-node-p (first sem))
                (def-keyword-p (rewrite-cl.node:node-string (first sem))))
      (return-from find-docstrings '()))

    ;; We need at least 4 semantic children for position 4.
    (when (< (length sem) 4)
      (return-from find-docstrings '()))

    ;; Position 4 = sem[3] (0-indexed). Collect consecutive strings
    ;; from position 4, excluding if it's the last semantic child.
    (let ((body-items (nthcdr 3 sem))
          (spans '()))
      (loop for item in body-items
            for i from 0
            while (string-node-p item)
            do (let ((is-last (= (+ 3 i) (1- (length sem)))))
                 (unless is-last
                   ;; Compute character offset of this string within cell source.
                   ;; Walk from form start to find position of this child.
                   (let ((char-pos (child-char-offset form-node item
                                                      form-char-offset)))
                     (when char-pos
                       (push (list char-pos
                                   (+ char-pos
                                      (length (rewrite-cl.node:node-string item))))
                             spans))))))
      (nreverse spans))))

(defun find-all-annotations (cell)
  "Compute the combined inline-comment and docstring annotations for CELL.
Returns a sorted list of (start end) pairs, or NIL if none."
  (let ((form-node (cell-form-node cell)))
    (when (and form-node (string= (cell-type cell) "code"))
      (let* ((comment-chars (cell-comment-chars cell))
             (inline (find-inner-comments form-node comment-chars))
             (docstrings (find-docstrings form-node comment-chars))
             (all-spans (sort (append docstrings inline) #'< :key #'first)))
        (when all-spans
          all-spans)))))

;;; ─── JSON / .ipynb output ──────────────────────────────────────────

(defun make-kernelspec (&optional (name "acl2") (display-name "ACL2"))
  `(("display_name" . ,display-name)
    ("language" . ,name)
    ("name" . ,name)))

(defun make-language-info (&optional (name "acl2"))
  `(("name" . ,name)
    ("mimetype" . "text/x-common-lisp")
    ("file_extension" . ".lisp")
    ("codemirror_mode" . "commonlisp")
    ("pygments_lexer" . "common-lisp")))

(defun split-source-lines (text)
  "Split TEXT into the Jupyter source array format: each element ends with
a newline except the last."
  (if (string= text "")
      (list "")
      (let* ((lines '())
             (start 0)
             (len (length text)))
        (loop for i from 0 below len
              when (char= (char text i) #\Newline)
                do (push (subseq text start (1+ i)) lines)
                   (setf start (1+ i)))
        ;; Remaining text after last newline (no trailing newline).
        (when (< start len)
          (push (subseq text start) lines))
        (nreverse lines))))

(defun write-notebook (cells source-path output-path)
  "Write CELLS as a .ipynb JSON file to OUTPUT-PATH."
  (let* ((source-uri (format nil "file://~A"
                              (namestring (truename source-path))))
         (kernelspec (make-kernelspec))
         (lang-info (make-language-info)))
    (with-open-file (out output-path
                         :direction :output
                         :if-exists :supersede
                         :external-format :utf-8)
      ;; We write the JSON manually using yason for correctness.
      (yason:with-output (out :indent t)
        (yason:with-object ()
          ;; nbformat
          (yason:encode-object-element "nbformat" 4)
          (yason:encode-object-element "nbformat_minor" 5)

          ;; metadata
          (yason:with-object-element ("metadata")
            (yason:with-object ()
              ;; kernelspec
              (yason:with-object-element ("kernelspec")
                (yason:with-object ()
                  (loop for (k . v) in kernelspec
                        do (yason:encode-object-element k v))))
              ;; language_info
              (yason:with-object-element ("language_info")
                (yason:with-object ()
                  (loop for (k . v) in lang-info
                        do (yason:encode-object-element k v))))
              ;; source_file
              (yason:encode-object-element "source_file" source-uri)))

          ;; cells
          (yason:with-object-element ("cells")
            (yason:with-array ()
              (dolist (c cells)
                (yason:with-object ()
                  ;; cell_type
                  (yason:encode-object-element "cell_type" (cell-type c))
                  ;; source (as array of lines)
                  (let ((display-source
                          (if (string= (cell-type c) "markdown")
                            (format-markdown-source (cell-source c))
                            (cell-source c))))
                    (yason:with-object-element ("source")
                      (yason:with-array ()
                        (dolist (line (split-source-lines display-source))
                          (yason:encode-array-element line)))))
                  ;; metadata with provenance
                  (yason:with-object-element ("metadata")
                    (yason:with-object ()
                      (yason:with-object-element ("provenance")
                        (yason:with-object ()
                          (yason:encode-object-element "start"
                                                       (cell-start-byte c))
                          (yason:encode-object-element "end"
                                                       (cell-end-byte c))
                          (when (> (cell-comment-chars c) 0)
                            (let ((prefix (if (string= (cell-type c) "markdown")
                                            (bracket-prefix-len)
                                            0)))
                              (yason:with-object-element ("comment")
                                (yason:with-array ()
                                  (yason:encode-array-element prefix)
                                  (yason:encode-array-element
                                   (+ prefix (cell-comment-chars c)))))))
                          ;; Inline comments and docstrings within form body.
                          (let ((annotations (find-all-annotations c)))
                            (when annotations
                              (yason:with-object-element ("comments")
                                (yason:with-array ()
                                  (dolist (span annotations)
                                    (yason:with-array ()
                                      (yason:encode-array-element (first span))
                                      (yason:encode-array-element
                                       (second span))))))))))))
                  ;; code cells require outputs and execution_count
                  (when (string= (cell-type c) "code")
                    (yason:with-object-element ("outputs")
                      (yason:with-array ()))
                    (yason:encode-object-element
                     "execution_count" nil)))))))))))

;;; ─── Portcullis (.acl2) metadata injection ─────────────────────────

(defun acl2-companion-files (source)
  "Find .acl2 portcullis companion files for SOURCE.
Returns list of (name . content) pairs.  Per-book companion (stem.acl2) takes
precedence over directory-wide cert.acl2 in ACL2, but we record both."
  (let* ((dir (make-pathname :defaults source :name nil :type nil))
         (cert-acl2 (merge-pathnames "cert.acl2" dir))
         (book-acl2 (make-pathname :defaults source :type "acl2"))
         (result nil))
    (dolist (path (list cert-acl2 book-acl2))
      (when (probe-file path)
        (handler-case
            (let ((text (uiop:read-file-string path)))
              (push (cons (file-namestring path) text) result))
          (error () nil))))
    (nreverse result)))

(defun inject-acl2-metadata (notebook-path source-path)
  "Add .acl2 portcullis companion content to NOTEBOOK-PATH metadata.
Reads the notebook JSON, adds an acl2_portcullis key with companion file
contents.  No-op if no companions exist."
  (let ((companions (acl2-companion-files source-path)))
    (when companions
      (let ((nb (with-open-file (in notebook-path :external-format :utf-8)
                  (yason:parse in :json-arrays-as-vectors t))))
        (let ((meta (or (gethash "metadata" nb)
                        (let ((h (make-hash-table :test #'equal)))
                          (setf (gethash "metadata" nb) h)
                          h)))
              (port (make-hash-table :test #'equal)))
          (dolist (pair companions)
            (setf (gethash (car pair) port) (cdr pair)))
          (setf (gethash "acl2_portcullis" meta) port))
        (with-open-file (out notebook-path :direction :output
                                           :if-exists :supersede
                                           :external-format :utf-8)
          (yason:encode nb out)
          (terpri out))))))

;;; ─── Main conversion ───────────────────────────────────────────────

(defun read-file-into-byte-vector (path)
  "Read PATH into a (vector (unsigned-byte 8))."
  (with-open-file (in path :element-type '(unsigned-byte 8))
    (let* ((len (file-length in))
           (buf (make-array len :element-type '(unsigned-byte 8))))
      (read-sequence buf in)
      buf)))

(defun write-placeholder-notebook (input output condition)
  "Write a placeholder .ipynb for INPUT that could not be parsed.
The notebook contains a markdown cell describing the error followed by a
single code cell with the raw source.
CONDITION is the error condition that was signalled."
  (let ((source-text (ignore-errors (uiop:read-file-string input)))
        (*markdown-bracket* :none))   ; no bracket wrapping for placeholder
    (write-notebook
     (list* (make-cell :type "markdown"
                       :source (format nil "**Parse error** — this file could ~
not be converted automatically.~%~%~A" condition))
            (when source-text
              (list (make-cell :type "code"
                               :source source-text
                               :end-byte (length source-text)))))
     input output)
    (format *error-output* "PLACEHOLDER ~A: ~A~%" (namestring input) condition)))

(defun convert-file (input-path &key output-path
                     (markdown-bracket :none)
                     (inject-portcullis t))
  "Convert INPUT-PATH (.lisp) to OUTPUT-PATH (.ipynb).
MARKDOWN-BRACKET can be :NONE, :FENCED, or :PRE.
When INJECT-PORTCULLIS is true (the default), attach .acl2 companion file
contents to the notebook metadata.
Returns the output pathname.
If parsing fails, writes a placeholder notebook with the raw source and
reports the issue to *ERROR-OUTPUT*."
  (let* ((input (pathname input-path))
         (output (or output-path
                     (make-pathname :defaults input :type "ipynb")))
         (*markdown-bracket* markdown-bracket))
    (handler-case
        (let* ((source-bytes (read-file-into-byte-vector input))
               ;; Parse with package locks disabled — ACL2 sources intern
               ;; symbols into the COMMON-LISP package (e.g. COMMON-LISP::TH)
               ;; which trips SBCL's package lock.
               (nodes (#+sbcl sb-ext:without-package-locks
                       #-sbcl progn
                       (rewrite-cl:parse-file-all input)))
               (classified (classify-top-level-nodes nodes))
               (cells (group-nodes-into-cells classified source-bytes)))
          (write-notebook cells input output)
          (when inject-portcullis
            (inject-acl2-metadata output input)))
      (error (e)
        (write-placeholder-notebook input output e)))
    output))

;;; ─── Recursive directory conversion ────────────────────────────────

(defvar *source-extensions* '("lisp" "lsp")
  "File extensions to convert (without the dot).")

(defvar *skip-directory-names* '(".sys")
  "Directory names to skip during recursive source file discovery.
.sys/ directories contain auto-generated useless-runes files from ACL2's
certification system; they are not meaningful source.")

(defun convert-directory (dir &key (force nil)
                                   (markdown-bracket :fenced)
                                   (verbose nil))
  "Convert all .lisp/.lsp files under DIR to .ipynb notebooks.
Skips .sys/ directories and files whose .ipynb is newer than the source
unless FORCE is true.  Each file is processed and forgotten immediately —
no data accumulates across files.
Returns (values converted skipped errors)."
  (let ((converted 0) (skipped 0) (errors 0) (n 0)
        (t-start (get-internal-real-time))
        (t-last-report (get-internal-real-time))
        (root (truename dir)))
    (labels
        ((convert-one (source)
           (incf n)
           (let ((output (make-pathname :defaults source :type "ipynb")))
             (cond
               ;; Skip if up to date.
               ((and (not force)
                     (probe-file output)
                     (<= (file-write-date source) (file-write-date output)))
                (incf skipped))
               ;; Convert.
               (t
                (handler-case
                    (progn
                      (convert-file source
                                    :output-path output
                                    :markdown-bracket markdown-bracket)
                      (incf converted)
                      (when verbose
                        (format t "  ~A~%" (enough-namestring output root))))
                  (error (e)
                    (incf errors)
                    (format *error-output* "FAIL ~A: ~A~%"
                            (enough-namestring source root) e))))))
           ;; Progress report every 10 seconds.
           (let ((now (get-internal-real-time)))
             (when (> (- now t-last-report)
                      (* 10 internal-time-units-per-second))
               (setf t-last-report now)
               (let ((elapsed (/ (- now t-start)
                                 internal-time-units-per-second)))
                 (format t "  progress: ~D files (~D converted, ~D skipped, ~D errors) ~
                            [~,1Fs elapsed]~%"
                         n converted skipped errors elapsed)
                 (finish-output)))))

         (walk (d)
           ;; Process source files in this directory, then recurse.
           (dolist (entry (directory
                           (merge-pathnames
                            (make-pathname :name :wild :type :wild)
                            d)))
             (cond
               ;; Directory — recurse unless skipped.
               ((uiop:directory-pathname-p entry)
                (let ((name (car (last (pathname-directory entry)))))
                  (unless (member name *skip-directory-names*
                                  :test #'string=)
                    (walk entry))))
               ;; Source file — convert immediately.
               ((member (pathname-type entry) *source-extensions*
                        :test #'string-equal)
                (convert-one entry))))))

      (walk root))

    (let ((elapsed (/ (- (get-internal-real-time) t-start)
                      internal-time-units-per-second)))
      (format t "~A: ~D converted, ~D skipped, ~D errors [~,1Fs]~%"
              root converted skipped errors elapsed))
    (values converted skipped errors)))

;;; ─── CLI entry point ───────────────────────────────────────────────

(defun main ()
  "CLI entry point.  Processes command-line arguments.
Supports both individual files and directories:
  lisp2nb [--force] [--fenced] FILE.lisp ...         — convert files
  lisp2nb [--force] [--fenced] --recursive DIR ...    — convert directories"
  (let* ((args (uiop:command-line-arguments))
         (force nil)
         (recursive nil)
         (verbose nil)
         (output-dir nil)
         (markdown-bracket :none)
         (inputs '()))

    ;; Parse args.
    (loop while args do
      (let ((arg (pop args)))
        (cond
          ((string= arg "--force") (setf force t))
          ((string= arg "--fenced") (setf markdown-bracket :fenced))
          ((string= arg "--pre") (setf markdown-bracket :pre))
          ((string= arg "--plain") (setf markdown-bracket :none))
          ((or (string= arg "--recursive") (string= arg "-r"))
           (setf recursive t))
          ((or (string= arg "--verbose") (string= arg "-v"))
           (setf verbose t))
          ((string= arg "-o")
           (setf output-dir (pop args)))
          ((string= arg "--"))
           ;; skip
           
          (t (push arg inputs)))))

    (setf inputs (nreverse inputs))

    (when (null inputs)
      (format *error-output*
              "Usage: lisp2nb [--force] [--fenced] [-r] [-v] INPUT ... [-o DIR]~%")
      (uiop:quit 1))

    (if recursive
        ;; Directory mode: recursively convert all .lisp/.lsp files.
        (let ((total-converted 0) (total-skipped 0) (total-errors 0))
          (dolist (dir-str inputs)
            (multiple-value-bind (c s e)
                (convert-directory dir-str
                                   :force force
                                   :markdown-bracket markdown-bracket
                                   :verbose verbose)
              (incf total-converted c)
              (incf total-skipped s)
              (incf total-errors e)))
          (when (> (length inputs) 1)
            (format t "Total: ~D converted, ~D up-to-date, ~D errors~%"
                    total-converted total-skipped total-errors))
          (uiop:quit (if (> total-errors 0) 1 0)))

        ;; File mode: convert individual files.
        (let ((errors 0) (converted 0))
          (dolist (input-str inputs)
            (let* ((input (pathname input-str))
                   (output (if output-dir
                             (make-pathname
                              :defaults (merge-pathnames
                                         (make-pathname :name (pathname-name input)
                                                        :type "ipynb")
                                         (parse-namestring
                                          (if (uiop:string-suffix-p output-dir "/")
                                            output-dir
                                            (concatenate 'string output-dir "/")))))
                             (make-pathname :defaults input :type "ipynb"))))
              ;; Skip if notebook is newer than source (unless --force).
              (when (or force
                        (not (probe-file output))
                        (> (file-write-date input)
                           (file-write-date output)))
                (handler-case
                    (progn
                      (convert-file input
                                   :output-path output
                                   :markdown-bracket markdown-bracket)
                      (format t "Wrote ~A~%" output)
                      (incf converted))
                  (error (e)
                    (format *error-output* "error: ~A: ~A~%" input e)
                    (incf errors))))))
          (when (> converted 0)
            (format t "Converted ~D file~:P~%" converted))
          (uiop:quit (if (> errors 0) 1 0))))))

;;; When loaded as a script, run main.
(when (and (find-package :uiop)
           (uiop:command-line-arguments))
  (main))

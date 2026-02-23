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
  (:export #:convert-file #:main))

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
  (end-byte 0 :type fixnum))

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
                        :end-byte byte-pos)
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
  (comment-chars 0 :type fixnum))  ; chars of comment at start of source

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
                               :comment-chars 0)
                    cells))

             ;; Run ends with blank → detached.
             ((eq (classified-node-kind (car (last run))) :blank)
              (emit-markdown run)
              (push (make-cell :type "code"
                               :source (classified-node-text form-node)
                               :start-byte (classified-node-start-byte form-node)
                               :end-byte (classified-node-end-byte form-node)
                               :comment-chars 0)
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
                                     :comment-chars comment-chars)
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
                                   (+ prefix (cell-comment-chars c)))))))))))
                  ;; outputs (empty for code cells, absent for markdown)
                  (when (string= (cell-type c) "code")
                    (yason:with-object-element ("outputs")
                      (yason:with-array ()))
                    (yason:encode-object-element "execution_count"
                                                 :null)))))))))))

;;; ─── Main conversion ───────────────────────────────────────────────

(defun read-file-into-byte-vector (path)
  "Read PATH into a (vector (unsigned-byte 8))."
  (with-open-file (in path :element-type '(unsigned-byte 8))
    (let* ((len (file-length in))
           (buf (make-array len :element-type '(unsigned-byte 8))))
      (read-sequence buf in)
      buf)))

(defun convert-file (input-path &key output-path
                     (markdown-bracket :none))
  "Convert INPUT-PATH (.lisp) to OUTPUT-PATH (.ipynb).
MARKDOWN-BRACKET can be :NONE, :FENCED, or :PRE.
Returns the output pathname."
  (let* ((input (pathname input-path))
         (output (or output-path
                     (make-pathname :defaults input :type "ipynb")))
         (*markdown-bracket* markdown-bracket)
         (source-bytes (read-file-into-byte-vector input))
         (nodes (rewrite-cl:parse-file-all input))
         (classified (classify-top-level-nodes nodes))
         (cells (group-nodes-into-cells classified source-bytes)))
    (write-notebook cells input output)
    output))

;;; ─── CLI entry point ───────────────────────────────────────────────

(defun main ()
  "CLI entry point.  Processes command-line arguments."
  (let* ((args (uiop:command-line-arguments))
         (force nil)
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
          ((string= arg "-o")
           (setf output-dir (pop args)))
          ((string= arg "--"))
           ;; skip
           
          (t (push arg inputs)))))

    (setf inputs (nreverse inputs))

    (when (null inputs)
      (format *error-output* "Usage: lisp2nb.lisp [--force] INPUT.lisp ... [-o DIR]~%")
      (uiop:quit 1))

    (let ((errors 0)
          (converted 0))
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
      (uiop:quit (if (> errors 0) 1 0)))))

;;; When loaded as a script, run main.
(when (and (find-package :uiop)
           (uiop:command-line-arguments))
  (main))

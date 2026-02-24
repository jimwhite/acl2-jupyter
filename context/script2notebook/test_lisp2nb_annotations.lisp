;;;; test_lisp2nb_annotations.lisp — Tests for inline comment & docstring annotations
;;;;
;;;; Run via:
;;;;   sbcl --noinform --non-interactive --disable-debugger \
;;;;        --load context/script2notebook/test_lisp2nb_annotations.lisp
;;;;
;;;; Exit code 0 = all pass, 1 = failures.

;;; ─── Bootstrap ──────────────────────────────────────────────────────

(require :asdf)

(let ((here (make-pathname :defaults *load-truename* :name nil :type nil)))
  (pushnew (merge-pathnames #p"../rewrite-cl/" here)
           asdf:*central-registry* :test #'equal))

(asdf:load-system "rewrite-cl" :verbose nil)
(ql:quickload '("yason" "babel") :silent t)

(load (merge-pathnames "lisp2nb.lisp"
                       (make-pathname :defaults *load-truename*
                                      :name nil :type nil)))

(in-package #:lisp2nb)

;;; ─── Test infrastructure ───────────────────────────────────────────

(defvar *test-pass* 0)
(defvar *test-fail* 0)

(defun test-check (name condition)
  (if condition
      (progn (format t "  PASS: ~A~%" name) (incf *test-pass*))
      (progn (format t "  FAIL: ~A~%" name) (incf *test-fail*))))

(defun span-text (src span)
  "Extract the substring of SRC corresponding to SPAN = (start end)."
  (subseq src (first span) (second span)))

(defun parse-form (src)
  "Parse SRC and return the first form node."
  (find-if #'form-node-p (rewrite-cl:parse-string-all src)))

;;; ─── Unit tests: find-inner-comments ───────────────────────────────

(format t "~%=== find-inner-comments ===~%")

;; Single inline comment
(let* ((src "(defun foo (x)
  ;; body comment
  (+ x 1))")
       (form (parse-form src))
       (spans (find-inner-comments form 0)))
  (test-check "single inline count" (= 1 (length spans)))
  (test-check "single inline text"
              (string= ";; body comment" (span-text src (first spans)))))

;; Multiple inline comments
(let* ((src "(defun bar (x y)
  ;; first comment
  (let ((prod (* x y)))
    ;; second comment
    (+ prod 1)))")
       (form (parse-form src))
       (spans (find-inner-comments form 0)))
  (test-check "multi inline count" (= 2 (length spans)))
  (test-check "multi inline text 1"
              (string= ";; first comment" (span-text src (first spans))))
  (test-check "multi inline text 2"
              (string= ";; second comment" (span-text src (second spans)))))

;; Block comment inside form
(let* ((src "(defun baz ()
  #| a block comment |#
  42)")
       (form (parse-form src))
       (spans (find-inner-comments form 0)))
  (test-check "block comment count" (= 1 (length spans)))
  (test-check "block comment text"
              (string= "#| a block comment |#" (span-text src (first spans)))))

;; No comments inside form
(let* ((src "(defun simple (x) (+ x 1))")
       (form (parse-form src))
       (spans (find-inner-comments form 0)))
  (test-check "no inline comments" (= 0 (length spans))))

;; Comment offset when form-char-offset > 0 (attached comment case)
(let* ((src "; attached
(defun qux () ;; trailing
  42)")
       (nodes (rewrite-cl:parse-string-all src))
       (classified (classify-top-level-nodes nodes))
       (source-bytes (babel:string-to-octets src :encoding :utf-8))
       (cells (group-nodes-into-cells classified source-bytes))
       (code-cell (find-if (lambda (c) (string= (cell-type c) "code")) cells))
       (annotations (find-all-annotations code-cell)))
  (test-check "attached + trailing has annotations" (not (null annotations)))
  (when annotations
    (test-check "attached trailing text"
                (string= ";; trailing"
                         (span-text (cell-source code-cell) (first annotations))))))

;;; ─── Unit tests: find-docstrings ───────────────────────────────────

(format t "~%=== find-docstrings ===~%")

;; Standard docstring
(let* ((src "(defun add (a b)
  \"Add two numbers.\"
  (+ a b))")
       (form (parse-form src))
       (spans (find-docstrings form 0)))
  (test-check "standard docstring count" (= 1 (length spans)))
  (test-check "standard docstring text"
              (string= "\"Add two numbers.\"" (span-text src (first spans)))))

;; defmacro docstring
(let* ((src "(defmacro my-if (test then else)
  \"Conditional.\"
  `(cond (,test ,then) (t ,else)))")
       (form (parse-form src))
       (spans (find-docstrings form 0)))
  (test-check "defmacro docstring count" (= 1 (length spans)))
  (test-check "defmacro docstring text"
              (string= "\"Conditional.\"" (span-text src (first spans)))))

;; String as only body (last item → not docstring)
(let* ((src "(defun greeting (name)
  \"just a string\")")
       (form (parse-form src))
       (spans (find-docstrings form 0)))
  (test-check "string-as-last-not-docstring" (= 0 (length spans))))

;; Non-def form — no docstrings
(let* ((src "(let ((x 1))
  \"not a docstring\"
  x)")
       (form (parse-form src))
       (spans (find-docstrings form 0)))
  (test-check "non-def no docstring" (= 0 (length spans))))

;; Too few semantic children
(let* ((src "(defun f (x))")
       (form (parse-form src))
       (spans (find-docstrings form 0)))
  (test-check "too-few-children no docstring" (= 0 (length spans))))

;; defthm (has "def" but different structure)
(let* ((src "(defthm my-thm
  (implies (and (natp x) (natp y))
           (natp (+ x y))))")
       (form (parse-form src))
       (spans (find-docstrings form 0)))
  ;; Position 4 is the implies form, not a string → no docstring
  (test-check "defthm no docstring" (= 0 (length spans))))

;;; ─── Unit tests: find-all-annotations (combined) ───────────────────

(format t "~%=== find-all-annotations ===~%")

;; Combined docstring + inline comments
(let* ((src "(defun compute (x y)
  \"Compute the result.\"
  ;; Step 1
  (let ((sum (+ x y)))
    ;; Step 2
    (* sum 2)))")
       (nodes (rewrite-cl:parse-string-all src))
       (classified (classify-top-level-nodes nodes))
       (source-bytes (babel:string-to-octets src :encoding :utf-8))
       (cells (group-nodes-into-cells classified source-bytes))
       (code-cell (find-if (lambda (c) (string= (cell-type c) "code")) cells))
       (annotations (find-all-annotations code-cell)))
  (test-check "combined count" (= 3 (length annotations)))
  ;; Should be sorted by start position
  (test-check "combined sorted"
              (and annotations
                   (< (first (first annotations))
                      (first (second annotations)))
                   (< (first (second annotations))
                      (first (third annotations)))))
  ;; First should be the docstring
  (test-check "combined first is docstring"
              (string= "\"Compute the result.\""
                       (span-text (cell-source code-cell) (first annotations))))
  ;; Second should be "; Step 1"
  (test-check "combined second is comment"
              (string= ";; Step 1"
                       (span-text (cell-source code-cell) (second annotations))))
  ;; Third should be "; Step 2"
  (test-check "combined third is comment"
              (string= ";; Step 2"
                       (span-text (cell-source code-cell) (third annotations)))))

;; Markdown cells should have no annotations
(let* ((src "; Just a comment

(+ 1 2)")
       (nodes (rewrite-cl:parse-string-all src))
       (classified (classify-top-level-nodes nodes))
       (source-bytes (babel:string-to-octets src :encoding :utf-8))
       (cells (group-nodes-into-cells classified source-bytes))
       (md-cell (find-if (lambda (c) (string= (cell-type c) "markdown")) cells)))
  (test-check "markdown has no annotations"
              (null (find-all-annotations md-cell))))

;;; ─── Integration test: full convert-file ───────────────────────────

(format t "~%=== Integration: convert-file ===~%")

(let ((tmp-lisp "/tmp/test-annot-integration.lisp")
      (tmp-ipynb "/tmp/test-annot-integration.ipynb"))
  ;; Write test file
  (with-open-file (out tmp-lisp :direction :output :if-exists :supersede)
    (format out "; This is a header comment~%~%")
    (format out "(defun my-add (a b)~%")
    (format out "  \"Add two numbers.\"~%")
    (format out "  ;; Do the addition~%")
    (format out "  (+ a b))~%~%")
    (format out "(defun my-sub (a b)~%")
    (format out "  (- a b))~%"))
  ;; Convert
  (convert-file tmp-lisp :output-path tmp-ipynb :markdown-bracket :fenced)
  ;; Read back and check
  (let* ((json (with-open-file (in tmp-ipynb)
                 (yason:parse in)))
         (cells (gethash "cells" json)))
    (test-check "integration cell count" (= 3 (length cells)))

    ;; Cell 0: markdown (header comment)
    (let* ((c0 (first cells))
           (prov (gethash "provenance" (gethash "metadata" c0))))
      (test-check "cell0 is markdown"
                  (string= "markdown" (gethash "cell_type" c0)))
      (test-check "cell0 has comment span" (not (null (gethash "comment" prov))))
      (test-check "cell0 has no comments key" (null (gethash "comments" prov))))

    ;; Cell 1: code (my-add with docstring + inline comment)
    (let* ((c1 (second cells))
           (prov (gethash "provenance" (gethash "metadata" c1))))
      (test-check "cell1 is code"
                  (string= "code" (gethash "cell_type" c1)))
      (test-check "cell1 has comments key" (not (null (gethash "comments" prov))))
      (let ((comments (gethash "comments" prov)))
        (test-check "cell1 comments count" (= 2 (length comments)))
        ;; Verify spans extract correctly from source
        (let ((source (format nil "~{~A~}" (gethash "source" c1))))
          (test-check "cell1 first span is docstring"
                      (and comments
                           (let ((s (subseq source
                                            (first (first comments))
                                            (second (first comments)))))
                             (search "\"Add two numbers.\"" s))))
          (test-check "cell1 second span is comment"
                      (and (>= (length comments) 2)
                           (let ((s (subseq source
                                            (first (second comments))
                                            (second (second comments)))))
                             (search ";; Do the addition" s)))))))

    ;; Cell 2: code (my-sub with no annotations)
    (let* ((c2 (third cells))
           (prov (gethash "provenance" (gethash "metadata" c2))))
      (test-check "cell2 is code"
                  (string= "code" (gethash "cell_type" c2)))
      (test-check "cell2 has no comments key"
                  (null (gethash "comments" prov))))))

;;; ─── Integration test: real ACL2 source file ───────────────────────

(format t "~%=== Integration: real ACL2 files ===~%")

(let ((acl2-home #p"/home/acl2/"))
  (dolist (stem '("defuns" "defthm" "axioms"))
    (let ((lisp-path (merge-pathnames
                      (make-pathname :name stem :type "lisp")
                      acl2-home))
          (tmp-ipynb (format nil "/tmp/test-real-~A.ipynb" stem)))
      (when (probe-file lisp-path)
        (format t "~%--- ~A.lisp ---~%" stem)
        (handler-case
            (progn
              (convert-file lisp-path :output-path tmp-ipynb
                                      :markdown-bracket :fenced)
              (let* ((json (with-open-file (in tmp-ipynb)
                             (yason:parse in)))
                     (cells (gethash "cells" json))
                     (code-cells (remove-if-not
                                  (lambda (c)
                                    (string= "code" (gethash "cell_type" c)))
                                  cells))
                     (cells-with-comments
                       (count-if
                        (lambda (c)
                          (gethash "comments"
                                   (gethash "provenance"
                                            (gethash "metadata" c))))
                        code-cells)))
                (format t "  total cells: ~D, code cells: ~D, with comments: ~D~%"
                        (length cells) (length code-cells) cells-with-comments)
                (test-check (format nil "~A converts" stem) t)
                (test-check (format nil "~A has annotated cells" stem)
                            (> cells-with-comments 0))
                ;; Spot-check: every comments span should be valid
                (let ((bad 0))
                  (dolist (c code-cells)
                    (let* ((prov (gethash "provenance" (gethash "metadata" c)))
                           (comments (gethash "comments" prov))
                           (source (format nil "~{~A~}"
                                           (gethash "source" c)))
                           (src-len (length source)))
                      (when comments
                        (dolist (span comments)
                          (let ((s (first span))
                                (e (second span)))
                            (unless (and (<= 0 s) (< s e) (<= e src-len))
                              (incf bad)))))))
                  (test-check (format nil "~A all spans valid" stem)
                              (= 0 bad)))))
          (error (e)
            (format t "  ERROR: ~A~%" e)
            (test-check (format nil "~A converts" stem) nil)))))))

;;; ─── Integration test: books ───────────────────────────────────────

(format t "~%=== Integration: books ===~%")

(let ((books-dir #p"/home/acl2/books/"))
  (dolist (relpath '("arithmetic-2/floor-mod/floor-mod-helper.lisp"
                     "std/lists/list-defuns.lisp"
                     "std/util/defines.lisp"))
    (let ((lisp-path (merge-pathnames relpath books-dir))
          (tmp-ipynb (format nil "/tmp/test-book-~A.ipynb"
                             (pathname-name (pathname relpath)))))
      (if (probe-file lisp-path)
          (progn
            (format t "~%--- ~A ---~%" relpath)
            (handler-case
                (progn
                  (convert-file lisp-path :output-path tmp-ipynb
                                          :markdown-bracket :fenced)
                  (let* ((json (with-open-file (in tmp-ipynb)
                                 (yason:parse in)))
                         (cells (gethash "cells" json))
                         (code-cells (remove-if-not
                                      (lambda (c)
                                        (string= "code" (gethash "cell_type" c)))
                                      cells))
                         (cells-with-comments
                           (count-if
                            (lambda (c)
                              (gethash "comments"
                                       (gethash "provenance"
                                                (gethash "metadata" c))))
                            code-cells)))
                    (format t "  total: ~D, code: ~D, annotated: ~D~%"
                            (length cells) (length code-cells)
                            cells-with-comments)
                    (test-check (format nil "~A converts" relpath) t)
                    ;; Validate spans
                    (let ((bad 0))
                      (dolist (c code-cells)
                        (let* ((prov (gethash "provenance" (gethash "metadata" c)))
                               (comments (gethash "comments" prov))
                               (source (format nil "~{~A~}"
                                               (gethash "source" c)))
                               (src-len (length source)))
                          (when comments
                            (dolist (span comments)
                              (let ((s (first span))
                                    (e (second span)))
                                (unless (and (<= 0 s) (< s e) (<= e src-len))
                                  (incf bad)))))))
                      (test-check (format nil "~A all spans valid" relpath)
                                  (= 0 bad)))))
              (error (e)
                (format t "  ERROR: ~A~%" e)
                (test-check (format nil "~A converts" relpath) nil))))
          (format t "~%--- ~A (not found, skipping) ---~%" relpath)))))

;;; ─── Summary ───────────────────────────────────────────────────────

(format t "~%========================================~%")
(format t "Results: ~D passed, ~D failed~%" *test-pass* *test-fail*)
(format t "========================================~%")

(uiop:quit (if (> *test-fail* 0) 1 0))

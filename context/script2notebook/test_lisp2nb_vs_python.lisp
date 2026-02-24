;;;; test_lisp2nb_vs_python.lisp — Compare CL converter output against existing Python-generated notebooks
;;;;
;;;; Run via:
;;;;   sbcl --noinform --non-interactive --disable-debugger \
;;;;        --load context/script2notebook/test_lisp2nb_vs_python.lisp
;;;;
;;;; Compares cell counts, cell types, provenance metadata, and annotation
;;;; spans between existing (Python/tree-sitter) .ipynb and fresh CL conversion.

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

;;; ─── Helpers ────────────────────────────────────────────────────────

(defvar *test-pass* 0)
(defvar *test-fail* 0)
(defvar *test-warn* 0)

(defun test-check (name condition)
  (if condition
      (progn (format t "    PASS: ~A~%" name) (incf *test-pass*))
      (progn (format t "    FAIL: ~A~%" name) (incf *test-fail*))))

(defun test-warn (name msg)
  (format t "    WARN: ~A — ~A~%" name msg)
  (incf *test-warn*))

(defun read-notebook (path)
  "Read a .ipynb file and return parsed JSON hashtable."
  (with-open-file (in path :external-format :utf-8)
    (yason:parse in)))

(defun ensure-vector (x)
  (if (listp x) (coerce x 'vector) x))

(defun nb-cells (nb)
  (ensure-vector (gethash "cells" nb)))

(defun cell-type-str (cell)
  (gethash "cell_type" cell))

(defun cell-source-str (cell)
  "Reconstruct cell source from array of lines."
  (let ((src (gethash "source" cell)))
    (format nil "~{~A~}" (if (vectorp src) (coerce src 'list) src))))

(defun cell-provenance (cell)
  (let ((meta (gethash "metadata" cell)))
    (when meta (gethash "provenance" meta))))

(defun cell-comments (cell)
  (let ((prov (cell-provenance cell)))
    (when prov (gethash "comments" prov))))

;;; ─── Comparison per file ────────────────────────────────────────────

(defun compare-notebooks (label lisp-path existing-ipynb)
  "Convert LISP-PATH fresh with CL converter, compare against EXISTING-IPYNB."
  (format t "~%=== ~A ===~%" label)
  (let ((tmp-ipynb (format nil "/tmp/cl-compare-~A.ipynb"
                           (pathname-name lisp-path))))
    ;; Convert with CL
    (handler-case
        (convert-file lisp-path :output-path tmp-ipynb :markdown-bracket :fenced)
      (error (e)
        (format t "  CL conversion FAILED: ~A~%" e)
        (test-check (format nil "~A CL converts" label) nil)
        (return-from compare-notebooks)))

    (let* ((py-nb (read-notebook existing-ipynb))
           (cl-nb (read-notebook tmp-ipynb))
           (py-cells (nb-cells py-nb))
           (cl-cells (nb-cells cl-nb))
           (py-code (remove-if-not (lambda (c) (string= "code" (cell-type-str c))) py-cells))
           (cl-code (remove-if-not (lambda (c) (string= "code" (cell-type-str c))) cl-cells))
           (py-md (remove-if-not (lambda (c) (string= "markdown" (cell-type-str c))) py-cells))
           (cl-md (remove-if-not (lambda (c) (string= "markdown" (cell-type-str c))) cl-cells)))

      (format t "  Python: ~D cells (~D code, ~D markdown)~%"
              (length py-cells) (length py-code) (length py-md))
      (format t "  CL:     ~D cells (~D code, ~D markdown)~%"
              (length cl-cells) (length cl-code) (length cl-md))

      ;; Cell count comparison — tree-sitter bugs may cause different counts
      (if (= (length py-cells) (length cl-cells))
          (test-check (format nil "~A cell count matches" label) t)
          (test-warn (format nil "~A cell count" label)
                     (format nil "Python=~D CL=~D (tree-sitter parse diff expected)"
                             (length py-cells) (length cl-cells))))

      ;; Compare code cell sources when counts match
      (when (= (length py-code) (length cl-code))
        (let ((source-matches 0)
              (source-diffs 0))
          (loop for py-c across py-code
                for cl-c across cl-code
                for i from 0
                do (let ((py-src (cell-source-str py-c))
                         (cl-src (cell-source-str cl-c)))
                     (if (string= py-src cl-src)
                         (incf source-matches)
                         (progn
                           (incf source-diffs)
                           (when (<= source-diffs 3)
                             (format t "    diff code cell ~D:~%" i)
                             (format t "      PY: ~A~%"
                                     (subseq py-src 0 (min 80 (length py-src))))
                             (format t "      CL: ~A~%"
                                     (subseq cl-src 0 (min 80 (length cl-src)))))))))
          (format t "  Code sources: ~D match, ~D diff~%" source-matches source-diffs)
          (if (= source-diffs 0)
              (test-check (format nil "~A all code sources match" label) t)
              (test-warn (format nil "~A code sources" label)
                         (format nil "~D differences" source-diffs)))))

      ;; CL annotation validity
      (let ((cl-annotated 0)
            (cl-bad-spans 0)
            (cl-total-spans 0))
        (loop for c across cl-code do
          (let* ((comments (cell-comments c))
                 (source (cell-source-str c))
                 (src-len (length source)))
            (when comments
              (incf cl-annotated)
              (dolist (span comments)
                (incf cl-total-spans)
                (let ((s (first span))
                      (e (second span)))
                  (unless (and (integerp s) (integerp e)
                               (<= 0 s) (< s e) (<= e src-len))
                    (incf cl-bad-spans)))))))
        (format t "  CL annotations: ~D cells, ~D spans, ~D invalid~%"
                cl-annotated cl-total-spans cl-bad-spans)
        (test-check (format nil "~A CL all spans valid" label)
                    (= 0 cl-bad-spans)))

      ;; Python annotation comparison (where both have them)
      (when (= (length py-code) (length cl-code))
        (let ((py-annotated 0)
              (cl-annotated 0)
              (both-annotated 0)
              (span-match 0)
              (span-mismatch 0))
          (loop for py-c across py-code
                for cl-c across cl-code
                do (let ((py-comments (cell-comments py-c))
                         (cl-comments (cell-comments cl-c)))
                     (when py-comments (incf py-annotated))
                     (when cl-comments (incf cl-annotated))
                     (when (and py-comments cl-comments)
                       (incf both-annotated)
                       (if (equal py-comments cl-comments)
                           (incf span-match)
                           (incf span-mismatch)))))
          (format t "  Annotations: PY=~D CL=~D both=~D match=~D mismatch=~D~%"
                  py-annotated cl-annotated both-annotated span-match span-mismatch)

          ;; Show a few mismatches
          (when (> span-mismatch 0)
            (let ((shown 0))
              (loop for py-c across py-code
                    for cl-c across cl-code
                    for i from 0
                    while (< shown 3)
                    do (let ((py-comments (cell-comments py-c))
                             (cl-comments (cell-comments cl-c))
                             (source (cell-source-str cl-c)))
                         (when (and py-comments cl-comments
                                    (not (equal py-comments cl-comments)))
                           (incf shown)
                           (format t "    mismatch cell ~D:~%" i)
                           (format t "      PY spans: ~S~%" py-comments)
                           (format t "      CL spans: ~S~%" cl-comments)
                           (format t "      source[0:80]: ~A~%"
                                   (subseq source 0
                                           (min 80 (length source)))))))))))

      ;; Spot-check: verify CL annotation text is actually a comment or string
      (let ((bad-text 0)
            (checked 0))
        (loop for c across cl-code do
          (let* ((comments (cell-comments c))
                 (source (cell-source-str c)))
            (when comments
              (dolist (span comments)
                (incf checked)
                (let* ((s (first span))
                       (e (second span))
                       (text (subseq source s e)))
                  (unless (or (and (>= (length text) 1)
                                   (char= (char text 0) #\;))
                              (and (>= (length text) 2)
                                   (string= "#|" (subseq text 0 2)))
                              (and (>= (length text) 1)
                                   (char= (char text 0) #\")))
                    (incf bad-text)
                    (when (<= bad-text 3)
                      (format t "    bad annotation text: ~S~%" text))))))))
        (format t "  Annotation text check: ~D checked, ~D bad~%" checked bad-text)
        (test-check (format nil "~A annotation text valid" label)
                    (= 0 bad-text))))))

;;; ─── Run comparisons ───────────────────────────────────────────────

(format t "~%========================================~%")
(format t "CL vs Python converter comparison~%")
(format t "========================================~%")

(let ((pairs '(("std/lists/list-defuns"
                "/home/acl2/books/std/lists/list-defuns.lisp"
                "/home/acl2/books/std/lists/list-defuns.ipynb")
               ("std/util/defines"
                "/home/acl2/books/std/util/defines.lisp"
                "/home/acl2/books/std/util/defines.ipynb")
               ("arithmetic-2/floor-mod/floor-mod-helper"
                "/home/acl2/books/arithmetic-2/floor-mod/floor-mod-helper.lisp"
                "/home/acl2/books/arithmetic-2/floor-mod/floor-mod-helper.ipynb")
               ("tools/bstar"
                "/home/acl2/books/tools/bstar.lisp"
                "/home/acl2/books/tools/bstar.ipynb")
               ("std/strings/defs-program"
                "/home/acl2/books/std/strings/defs-program.lisp"
                "/home/acl2/books/std/strings/defs-program.ipynb")
               ("std/io/base"
                "/home/acl2/books/std/io/base.lisp"
                "/home/acl2/books/std/io/base.ipynb"))))
  (dolist (entry pairs)
    (destructuring-bind (label lisp-path existing-ipynb) entry
      (if (and (probe-file lisp-path) (probe-file existing-ipynb))
          (compare-notebooks label lisp-path existing-ipynb)
          (format t "~%=== ~A === SKIPPED (files not found)~%" label)))))

;;; Also test a batch of books to make sure CL converter handles them

(format t "~%~%========================================~%")
(format t "Batch conversion test (50 random books)~%")
(format t "========================================~%")

(let ((all-lisp '())
      (converted 0)
      (failed 0)
      (bad-spans 0))
  ;; Collect .lisp files that have matching .ipynb
  (dolist (dir '("/home/acl2/books/std/lists/"
                "/home/acl2/books/std/util/"
                "/home/acl2/books/std/strings/"
                "/home/acl2/books/std/io/"
                "/home/acl2/books/std/typed-lists/"
                "/home/acl2/books/arithmetic-2/floor-mod/"
                "/home/acl2/books/arithmetic-2/meta/"
                "/home/acl2/books/tools/"
                "/home/acl2/books/misc/"))
    (when (probe-file dir)
      (dolist (f (directory (merge-pathnames "*.lisp" dir)))
        (push f all-lisp))))

  ;; Cap at 50
  (setf all-lisp (subseq all-lisp 0 (min 50 (length all-lisp))))

  (dolist (lisp-path all-lisp)
    (let ((tmp-ipynb (format nil "/tmp/cl-batch-~A.ipynb"
                             (pathname-name lisp-path))))
      (handler-case
          (progn
            (convert-file lisp-path :output-path tmp-ipynb
                                    :markdown-bracket :fenced)
            (incf converted)
            ;; Validate spans
            (let* ((nb (read-notebook tmp-ipynb))
                   (cells (nb-cells nb)))
              (loop for c across cells do
                (let ((comments (cell-comments c))
                      (source (cell-source-str c))
                      (src-len))
                  (setf src-len (length source))
                  (when comments
                    (dolist (span comments)
                      (let ((s (first span))
                            (e (second span)))
                        (unless (and (integerp s) (integerp e)
                                     (<= 0 s) (< s e) (<= e src-len))
                          (incf bad-spans)
                          (format t "  BAD SPAN in ~A: ~S (src-len=~D)~%"
                                  (pathname-name lisp-path) span src-len)))))))))
        (error (e)
          (incf failed)
          (format t "  FAIL: ~A: ~A~%" (pathname-name lisp-path) e)))))

  (format t "~%Batch: ~D converted, ~D failed, ~D bad spans~%"
          converted failed bad-spans)
  (test-check "batch all convert" (= 0 failed))
  (test-check "batch all spans valid" (= 0 bad-spans)))

;;; ─── Summary ────────────────────────────────────────────────────────

(format t "~%========================================~%")
(format t "Results: ~D passed, ~D failed, ~D warnings~%"
        *test-pass* *test-fail* *test-warn*)
(format t "========================================~%")

(uiop:quit (if (> *test-fail* 0) 1 0))

;;; Test include-book in the original saved_acl2 (no quicklisp/ASDF loaded).
;;; Usage:  /home/acl2/saved_acl2 < test-include-book-original.lisp

(include-book "std/lists/append" :dir :system)
(cw "INCLUDE-BOOK-ORIGINAL: SUCCESS~%")
(value :q)
(sb-ext:exit :code 0)

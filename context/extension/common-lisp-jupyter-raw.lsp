(in-package "ACL2")
(defttag :common-lisp-jupyter)
(progn!
 (set-raw-mode t)
 #+acl2-raw
 (ql:quickload '(:common-lisp-jupyter))
)

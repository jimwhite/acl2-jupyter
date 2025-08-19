(in-package "ACL2")
(defttag :common-lisp-jupyter)
(progn!
 (set-raw-mode t)
 #+acl2-raw
 (ql:quickload '(:common-lisp-jupyter :cytoscape-clj :kekule-clj :resizable-box-clj :ngl-clj :delta-vega))
 #+acl2-raw
 (jupyter:run-kernel 'jupyter/common-lisp:kernel)
)

; pzmq.lisp - ACL2 Book for loading pzmq (ZeroMQ bindings)
; Part of ACL2 Jupyter Kernel
;
; License: MIT
;
; This book loads pzmq via Quicklisp, providing ZeroMQ bindings
; for the ACL2 Jupyter Kernel.

(in-package "ACL2")
(include-book "quicklisp/base" :dir :system)

(defttag :acl2-kernel-pzmq)
; (depends-on "pzmq-raw.lsp")
(include-raw "pzmq-raw.lsp" :host-readtable t)

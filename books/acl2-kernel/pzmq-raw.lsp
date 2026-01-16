; pzmq-raw.lsp - Load pzmq via Quicklisp/ASDF
; Part of ACL2 Jupyter Kernel
;
; This loads the pzmq ZeroMQ bindings library.

(in-package "ACL2")

(ql:quickload "pzmq" :silent t)

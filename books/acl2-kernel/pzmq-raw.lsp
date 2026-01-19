; pzmq-raw.lsp - Load pzmq via Quicklisp/ASDF
; Part of ACL2 Jupyter Kernel
;
; This loads the pzmq ZeroMQ bindings library.


(in-package "ACL2-KERNEL")

;; This seems to prevent some conflict with common-lisp-jupyter.  Weird.
;; At one point Copilot thought it was about defcallback but then changed its mind.
;;; Now I understand the real issue! The error Undefined callback: PZMQ::FREE-FN shows the problem:
;;; When common-lisp-jupyter compiles pzmq with plain SBCL, CFFI registers callbacks during compilation. 
;;; Those callbacks are runtime state, not in the FASL. When ACL2 later loads the cached FASL, it 
;;; expects the callbacks to exist, but they don't because ACL2 is a different Lisp session that didn't 
;;; register them.
;; Use a separate FASL cache for ACL2 to avoid conflicts with plain SBCL
;; This prevents ACL2-compiled FASLs from being loaded by plain SBCL
#| 
(let ((acl2-cache (merge-pathnames "acl2/" asdf:*user-cache*)))
  (asdf:initialize-output-translations
   `(:output-translations
     :inherit-configuration
     (t (,acl2-cache :implementation)))))
 |#

(ql:quickload "pzmq" :silent t)

; pzmq-raw.lsp - Load pzmq via Quicklisp/ASDF
; Part of ACL2 Jupyter Kernel
;
; This loads the pzmq ZeroMQ bindings library.
; We use a separate FASL cache to avoid corrupting the shared cache
; that plain SBCL/Quicklisp uses.

(in-package "ACL2")

;; Use a separate FASL cache for ACL2 to avoid conflicts with plain SBCL
;; This prevents ACL2-compiled FASLs from being loaded by plain SBCL
(let ((acl2-cache (merge-pathnames "acl2/" asdf:*user-cache*)))
  (asdf:initialize-output-translations
   `(:output-translations
     :inherit-configuration
     (t (,acl2-cache :implementation)))))

(ql:quickload "pzmq" :silent t)

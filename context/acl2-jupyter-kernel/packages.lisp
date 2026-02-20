;;;; ACL2 Jupyter Kernel - Package Definitions
;;;;
;;;; The package is named "ACL2-JUPYTER" to mirror Bridge's "BRIDGE" package.
;;;; Bridge uses ACL2's defpkg with *standard-acl2-imports*, but since we
;;;; load via ASDF (before LP), we use CL's defpackage and import the ACL2
;;;; symbols we need directly — same symbols, so (let ((*standard-co* ...)))
;;;; rebinds the right special.

(defpackage #:acl2-jupyter
  (:nicknames #:acl2-jupyter-kernel)
  (:use #:common-lisp)
  (:import-from #:acl2
                ;; Output channel symbols — must be the SAME symbol as ACL2 uses
                #:*standard-co*
                #:*open-output-channel-key*
                #:*open-output-channel-type-key*
                ;; Input channel symbols — for creating channels from string streams
                #:*open-input-channel-key*
                #:*open-input-channel-type-key*
                #:*the-live-state*
                #:*ld-level*
                ;; State access
                #:f-get-global
                #:f-put-global
                #:global-symbol
                #:raw-mode-p
                #:w
                ;; Keyword command expansion
                #:function-symbolp
                #:formals
                #:getpropc
                #:macro-minimal-arity
                ;; Command landmarks (for :pbt etc.)
                #:maybe-add-command-landmark
                #:default-defun-mode
                #:initialize-accumulated-warnings
                ;; Used in ld / eval
                #:state)
  (:export #:kernel
           #:start
           #:install
           #:install-image))

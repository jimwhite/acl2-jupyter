;;; GUIX manifest for ACL2 development environment
;;; 
;;; This manifest can be used to set up a development environment with ACL2
;;; Use: guix shell -m manifest.scm
;;; Or:  guix install -m manifest.scm

(use-modules (gnu)
             (gnu packages)
             (acl2))  ; Our custom ACL2 package

(packages->manifest
 (list acl2))
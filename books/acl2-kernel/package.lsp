; ACL2 Jupyter Kernel
; Copyright (C) 2026
;
; License: MIT

(in-package "ACL2")
(include-book "std/portcullis" :dir :system)

(defpkg "ACL2-KERNEL"
  (append std::*std-exports*
          '(assert!
            b*
            include-raw
            lnfix
            lifix
            two-nats-measure
            explode
            implode
            defthm
            defund
            defun
            defmacro
            mv
            mv-let
            er
            state
            ;; String functions we'll need
            coerce
            string-append
            length
            subseq
            char
            char-code
            code-char
            ;; List functions
            append
            reverse
            nth
            nthcdr
            assoc
            rassoc
            ;; Arithmetic
            floor
            mod
            ash
            logand
            logior
            logxor
            ;; For xdoc
            acl2-kernel)
          (set-difference-eq acl2::*standard-acl2-imports*
                             '(include-book))))

;; Convenience macro for including books with trust tags
(defmacro ACL2-KERNEL::include-book (&rest args)
  `(ACL2::include-book ,@args :ttags :all))

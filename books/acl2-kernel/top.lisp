; ACL2 Jupyter Kernel - Top Level Book
; Copyright (C) 2026
;
; License: MIT

(in-package "ACL2-KERNEL")
(include-book "xdoc/top" :dir :system)
(include-book "tools/include-raw" :dir :system)
(include-book "std/strings/top" :dir :system)

;; Include kernel component books (to be added as implemented)
;; (include-book "json")
;; (include-book "hmac")
;; (include-book "message")
;; (include-book "channel")
;; (include-book "kernel")

(defxdoc acl2-kernel
  :parents (acl2::interfacing-tools)
  :short "Native ACL2 Jupyter Kernel"
  :long "<p>The ACL2 Jupyter Kernel implements the Jupyter Kernel Protocol
(v5.3) natively in ACL2/SBCL, allowing ACL2 to be used directly from
Jupyter notebooks.</p>

<h3>Features</h3>
<ul>
<li>Direct ACL2 evaluation without subprocess overhead</li>
<li>Full Jupyter protocol support (execute, complete, inspect)</li>
<li>HMAC-SHA256 message authentication</li>
<li>ZeroMQ transport (TCP and Unix domain sockets)</li>
</ul>

<h3>Architecture</h3>
<p>The kernel is implemented as ACL2 books with raw Lisp extensions
for FFI to ZeroMQ and cryptographic libraries. Tests are @(see defthm)
forms proven during certification.</p>")

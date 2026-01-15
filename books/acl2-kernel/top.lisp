; ACL2 Jupyter Kernel - Top Level Book
; Copyright (C) 2026
;
; License: MIT

(in-package "ACL2-KERNEL")
(include-book "xdoc/top" :dir :system)
(include-book "tools/include-raw" :dir :system)
(include-book "std/strings/top" :dir :system)

;; Reuse existing community books
(include-book "kestrel/json-parser/parse-json" :dir :system)     ; JSON parsing
(include-book "centaur/bridge/to-json" :dir :system)             ; JSON encoding
(include-book "kestrel/crypto/interfaces/hmac-sha-256" :dir :system) ; HMAC-SHA-256

;; Include kernel component books (to be added as implemented)
(include-book "connection")
(include-book "message")
(include-book "kernel")

;; Load ZeroMQ bindings and threading support via Quicklisp
(include-book "pzmq")
(include-book "quicklisp/bordeaux" :dir :system)

;; Load raw Lisp runtime (main loop, message handling)
(defttag :acl2-kernel-raw)
; (depends-on "kernel-raw.lsp")
(include-raw "kernel-raw.lsp"
             :do-not-compile t
             :host-readtable t)

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

<h3>Reused Community Books</h3>
<ul>
<li>@(see acl2::parse-json) - JSON parsing from kestrel/json-parser</li>
<li>@(see bridge::json-encode) - JSON encoding from centaur/bridge</li>
<li>@(see crypto::hmac-sha-256) - HMAC from kestrel/crypto</li>
</ul>

<h3>Architecture</h3>
<p>The kernel is implemented as ACL2 books with raw Lisp extensions
for FFI to ZeroMQ. Tests are @(see defthm) forms proven during certification.</p>")

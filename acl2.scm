;;; tojo-tokyo-guix-config --- Guix Channel for git.tojo.tokyo's package
;;; Copyright © 2021, 2022 Masaya Tojo <masaya@tojo.tokyo>
;;;
;;; This file is part of tojo-tokyo-guix-config.
;;;
;;; tojo-tokyo-guix-config is free software; you can redistribute
;;; it and/or modify it under the terms of the GNU General Public
;;; License as published by the Free Software Foundation; either
;;; version 3 of the License, or (at your option) any later version.
;;;
;;; tojo-tokyo-guix-config is distributed in the hope that it will
;;; be useful, but WITHOUT ANY WARRANTY; without even the implied
;;; warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
;;; See the GNU General Public License for more details.
;;;
;;; You should have received a copy of the GNU General Public License
;;; along with extract-green-color.  If not, see
;;; <http://www.gnu.org/licenses/>.

(define-module (wiki3-ai packages acl2)
  #:use-module (guix packages)
  #:use-module ((guix licenses) #:prefix license:)
  #:use-module (guix download)
  #:use-module (guix build-system gnu)
  #:use-module (gnu packages)
  #:use-module (gnu packages base)
  #:use-module (gnu packages lisp)
  #:use-module (gnu packages ruby)
  #:use-module (gnu packages admin)
  #:use-module (gnu packages check)
  #:use-module (gnu packages perl)

  ;; For ACL2 Kernel
  #:use-module (gnu packages python)
  #:use-module (gnu packages python-xyz)
  #:use-module (gnu packages python-web)
  #:use-module (gnu packages python-crypto)
  #:use-module (gnu packages monitoring)
  #:use-module (guix build-system python))

(define-public acl2
  (package
    (name "acl2")
    (version "8.6")
    (source (origin
              (method url-fetch)
              (uri
               (string-append "https://github.com/acl2-devel/acl2-devel/releases/download/"
                              version
                              "/acl2-"
                              version ".tar.gz"))
              (sha256
               (base32
                "0nahdm00wh2gs5lybx487s70y2qigriklv1k6jy51jysnryf9xh3"))))
        (build-system gnu-build-system)
    (arguments
     `(#:tests? #f
       #:phases
       (modify-phases %standard-phases
         (replace 'configure
           (lambda _
             (substitute* '("./acl2-init.lisp"
                            "./books/build/make_cert_help.pl")
               (("#!/bin/sh") (string-append "#!" (which "sh"))))

             ;; XXX: oracle-time-tests.lisp will fail when use libfaketime.
             (delete-file "./books/tools/oracle-time-tests.lisp")
             #t))
         (replace 'build
           (lambda* (#:key outputs #:allow-other-keys)
             (let* ((out (assoc-ref outputs "out"))
                    (acl2 (string-append out "/lib/acl2")))
               (mkdir-p acl2)
               (copy-recursively "." acl2)
               (chdir acl2)
               (setenv "HOME" "/tmp")
               (setenv "TZ" "UTC")

               ;; XXX: Avoid BOOK-HASH-MISMATCH.
               (invoke "which" "make")
               (invoke "make" "--version")
               (invoke "make" "-d")
               (chdir "books")
               (invoke "make"
                       "basic"
                       "system"
                       (string-append "ACL2=" (string-append acl2 "/saved_acl2"))
                       "ACL2_HAS_HONS=1"
                       "ACL2_HAS_ANSI=1"
                       "ACL2_COMP_EXT=fasl"
                       "ACL2_HOST_LISP=SBCL"
                       "USE_QUICKLISP=0"))))
         (replace 'install
           (lambda* (#:key outputs #:allow-other-keys)
             (let* ((out (assoc-ref outputs "out"))
                    (acl2 (string-append out "/lib/acl2"))
                    (bin (string-append out "/bin")))
               (mkdir-p bin)
               (symlink (string-append acl2 "/saved_acl2")
                        (string-append bin "/acl2"))
               #t))))))
    (native-inputs
     `(("make" ,gnu-make)
       ("perl" ,perl)
       ("which" ,which)
       ("inetutils" ,inetutils)
       ("libfaketime" ,libfaketime)))
    (inputs
     `(("sbcl" ,sbcl)))
    (synopsis "A Computational Logic for Applicative Common Lisp")
    (description "ACL2 is a logic and programming language in which you can model computer systems, together with a tool to help you prove properties of those models. \"ACL2\" denotes \" Computational Logic for Applicative Common Lisp\".")
    (home-page "https://www.cs.utexas.edu/users/moore/acl2/")
    ;; XXX: still checking
    (license (list license:bsd-3
                   license:expat
                   license:gpl2+))))

acl2


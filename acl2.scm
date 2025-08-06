;;; ACL2 GUIX package definition
;;; This package provides ACL2 theorem prover running on SBCL

(define-module (acl2)
  #:use-module (guix packages)
  #:use-module (guix download)
  #:use-module (guix git-download)
  #:use-module (guix build-system gnu)
  #:use-module (guix utils)
  #:use-module ((guix licenses) #:prefix license:)
  #:use-module (gnu packages)
  #:use-module (gnu packages autotools)
  #:use-module (gnu packages base)
  #:use-module (gnu packages compression)
  #:use-module (gnu packages curl)
  #:use-module (gnu packages lisp)
  #:use-module (gnu packages perl)
  #:use-module (gnu packages pkg-config)
  #:use-module (gnu packages tls)
  #:use-module (gnu packages version-control))

(define-public acl2
  (package
    (name "acl2")
    ;; Use a recent stable commit from ACL2 repository
    ;; This should be updated to match the latest stable release
    (version "8.6")
    (source
     (origin
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
    (native-inputs
     (list autoconf
           automake
           curl
           git
           gnu-make
           perl
           pkg-config
           zlib
           zstd))
    (inputs
     (list sbcl
           openssl))
    (arguments
     `(#:tests? #f ; No test suite
       #:make-flags (list (string-append "LISP=sbcl"))
       #:phases
       (modify-phases %standard-phases
         (delete 'configure) ; No configure script
         (add-after 'unpack 'prepare-build
           (lambda* (#:key outputs #:allow-other-keys)
             (let ((out (assoc-ref outputs "out")))
               ;; Set up build environment
               (setenv "CERT_PL_RM_OUTFILES" "1")
               #t)))
         (replace 'build
           (lambda* (#:key make-flags #:allow-other-keys)
             ;; Build ACL2 executable
             (apply invoke "make" make-flags)))
         (add-after 'build 'certify-books
           (lambda* (#:key outputs #:allow-other-keys)
             (let ((out (assoc-ref outputs "out")))
               ;; Certify basic books
               (with-directory-excursion "books"
                 (invoke "make" "basic"
                         (string-append "ACL2=" (getcwd) "/../saved_acl2")
                         "-j" "4"))
               #t)))
         (replace 'install
           (lambda* (#:key outputs #:allow-other-keys)
             (let* ((out (assoc-ref outputs "out"))
                    (bin (string-append out "/bin"))
                    (share (string-append out "/share/acl2"))
                    (books (string-append share "/books"))
                    (doc (string-append out "/share/doc/acl2")))
               
               ;; Create directories
               (mkdir-p bin)
               (mkdir-p share)
               (mkdir-p doc)
               
               ;; Install ACL2 executable
               (copy-file "saved_acl2" (string-append bin "/acl2"))
               (chmod (string-append bin "/acl2") #o755)
               
               ;; Install books and support files
               (copy-recursively "books" books)
               
               ;; Install build scripts if they exist
               (when (file-exists? "books/build/cert.pl")
                 (copy-file "books/build/cert.pl" (string-append bin "/cert.pl"))
                 (chmod (string-append bin "/cert.pl") #o755))
               (when (file-exists? "books/build/clean.pl")
                 (copy-file "books/build/clean.pl" (string-append bin "/clean.pl"))
                 (chmod (string-append bin "/clean.pl") #o755))
               (when (file-exists? "books/build/critpath.pl")
                 (copy-file "books/build/critpath.pl" (string-append bin "/critpath.pl"))
                 (chmod (string-append bin "/critpath.pl") #o755))
               
               ;; Install documentation if it exists
               (when (file-exists? "doc")
                 (copy-recursively "doc" (string-append doc "/doc")))
               (when (file-exists? "README")
                 (copy-file "README" (string-append doc "/README")))
               (when (file-exists? "LICENSE")
                 (copy-file "LICENSE" (string-append doc "/LICENSE")))
               
               #t)))
         (add-after 'install 'wrap-program
           (lambda* (#:key outputs #:allow-other-keys)
             (let* ((out (assoc-ref outputs "out"))
                    (bin (string-append out "/bin"))
                    (share (string-append out "/share/acl2"))
                    (books (string-append share "/books")))
               ;; Create wrapper script that sets up environment variables
               (with-output-to-file (string-append bin "/acl2-wrapper")
                 (lambda ()
                   (format #t "#!/bin/sh~%")
                   (format #t "export ACL2_SYSTEM_BOOKS=~s~%" books)
                   (format #t "export ACL2=~s~%" (string-append bin "/acl2"))
                   (format #t "exec ~s \"$@\"~%" (string-append bin "/acl2"))))
               (chmod (string-append bin "/acl2-wrapper") #o755)
               #t))))))
    (home-page "https://www.cs.utexas.edu/users/moore/acl2/")
    (synopsis "ACL2 theorem prover running on SBCL")
    (description
     "ACL2 is a logic and programming language in which you can model computer
systems, together with a tool to help you prove properties of those models.
\"ACL2\" denotes \"A Computational Logic for Applicative Common Lisp\".

This package builds ACL2 using SBCL (Steel Bank Common Lisp) as the underlying
Lisp implementation and includes the basic certified books for immediate use.")
    (license license:bsd-3)))

acl2

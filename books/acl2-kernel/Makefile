# ACL2 Jupyter Kernel Build
# Run: make or cert.pl top.lisp

ACL2 ?= /home/acl2/saved_acl2
CERT_PL ?= /home/acl2/books/build/cert.pl

.PHONY: all clean

all: top.cert

%.cert: %.lisp
	$(CERT_PL) --acl2 $(ACL2) $<

# Dependencies (will grow as we add more books)
portcullis.cert: portcullis.lisp package.lsp
top.cert: top.lisp portcullis.cert

clean:
	rm -f *.cert *.cert.out *.fasl *.lx64fsl *.port .sys/*

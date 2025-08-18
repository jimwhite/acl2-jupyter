# FROM ghcr.io/jimwhite/acl2-jupyter
FROM acl2-jupyter:latest

# Add any other books you might want to certify here.
# See the documentation for cert.pl for more information about how to use it:
# https://www.cs.utexas.edu/~moore/acl2/manuals/current/manual/?topic=BUILD____CERT.PL
RUN echo cert.pl ${ACL2_SYSTEM_BOOKS}/sorting/isort

# Now, when starting a container using the image created by this
# Dockerfile, the sorting/isort book will be certified, and you can
# load it using include-book. e.g.,
# (include-book "sorting/isort" :dir :system)

# ACL2 Docker Image

## Notes
By default, certification is done with 4 parallel tasks. This can be changed by overriding the `ACL2_CERTIFY_OPTS` build argument. (i.e. using `docker build --build-arg ACL2_CERTIFY_OPTS="-j 2"`)

By default, the "basic" book selection is certified. This can be changed by overriding the `ACL2_CERTIFY_TARGETS` build argument. Multiple targets can be provided to this argument if desired.

## Why not Alpine?
Currently `docker-slim` is the base image used because [this osicat bug](https://github.com/osicat/osicat/issues/19) causes the ACL2 build to fail due to Alpine Linux's use of `musl` instead of `glibc` for its libc implementation.

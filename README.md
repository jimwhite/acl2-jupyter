# ACL2 Docker Image

## Notes
By default, certification is done with 4 parallel tasks. This can be changed by overriding the `ACL2_CERTIFY_OPTS` build argument. (i.e. using `docker build --build-arg ACL2_CERTIFY_OPTS="-j 2"`)

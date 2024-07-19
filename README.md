# ACL2 Docker Image

## Availability
This image is available on Docker Hub under [`atwalter/acl2`](https://hub.docker.com/r/atwalter/acl2/) and on the GitHub Container Registry under [`mister-walter/acl2`](https://ghcr.io/mister-walter/acl2).

## M1/M2 Macs
Be aware that the prebuilt Docker image is known to have issues on non-Intel macOS machines. It will work correctly if the image is rebuilt from scratch on an M1/M2 machine.

## Usage

By default, running this Docker image will drop you into the ACL2 REPL. The "basic" selection of books (per the ACL2 Makefile) has been certified, but you may want to certify additional books. One way to do this is to start a Docker container with a shell rather than ACL2; one can do that with a command like `docker run -it atwalter/acl2 /bin/bash`. Then, one can use [cert.pl](https://www.cs.utexas.edu/~moore/acl2/manuals/current/manual/?topic=BUILD____CERT.PL) to certify some books before starting ACL2. A full example is shown below, where lines prefixed by `$` indicate commands executed outside of Docker and `#` indicate commands executed inside of the Docker container.

```
$ docker run -it atwalter/acl2 /bin/bash
# cert.pl ~/acl2/books/sorting/isort
# acl2
# ACL2 !> (include-book "sorting/isort" :dir :system)
# ACL2 !> (isort '(5 2 1 4 3))
(1 2 3 4 5)
```

Note that when the Docker container exits, the certificates for any books certified since the container was started will be lost. If you find yourself repeatedly needing to certify the same set of books, you can create a new Docker image based on this one. You can find an example Dockerfile in `examples/certified-books/Dockerfile`.

## Building

The [`jq`](https://github.com/stedolan/jq) command-line tool bust be installed to use the provided `Makefile` to build an ACL2 Docker image. This tool is used to get the latest commit hash for the ACL2 repo from Github.

To enable reproducible builds, reduce image size, image build time, and download bandwidth during a build, the Dockerfile expects that it is provided a `ACL2_REPO_LATEST_COMMIT` build argument. This argument must be set to a URL-safe string corresponding to a commit or tag format that Github understands. I have tested this with full commit hashes and short commit hashes (e.g. the first 8 characters of the full commit hash). As suggested above, the `build` make target will  use Github's API to determine the commit hash for the latest commit to the ACL2 repo and pass that to Docker when building an image.

## Notes
By default, certification is done with 4 parallel tasks. This can be changed by overriding the `ACL2_CERTIFY_OPTS` build argument. (i.e. using `docker build --build-arg ACL2_CERTIFY_OPTS="-j 2"`)

By default, the "basic" book selection is certified. This can be changed by overriding the `ACL2_CERTIFY_TARGETS` build argument. Multiple targets can be provided to this argument if desired.

## Updating the Gradescope image
To update the Gradescope image, one should update the ACL2_COMMIT value in the make-gradescope.sh script to be the Git hash of the appropriate commit in the ACL2 repo. IMAGE_VERSION should also be modified to be some label appropriate for the semester.

## Why not Alpine?
Currently `docker-slim` is the base image used because [this osicat bug](https://github.com/osicat/osicat/issues/19) causes the ACL2 build to fail due to Alpine Linux's use of `musl` instead of `glibc` for its libc implementation.

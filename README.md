# ACL2 Docker Image

## Availability

This image is available on Docker Hub under [`atwalter/acl2`](https://hub.docker.com/r/atwalter/acl2/) and on the GitHub Container Registry under [`mister-walter/acl2`](https://ghcr.io/mister-walter/acl2).

## Apple Silicon Macs

This image is now built and distributed as a multi-platform Docker image. This means that both a `linux/amd64` and `linux/arm64` version of the image are built, and Docker should automatically use the appropriate version for your computer's architecture.

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

The [`jq`](https://github.com/stedolan/jq) command-line tool must be installed to use the provided `Makefile` to build an ACL2 Docker image. This tool is used to get the latest commit hash for the ACL2 repo from Github.

To enable reproducible builds and reduce image size, image build time, and download bandwidth during a build, the Dockerfile expects that it is provided a `ACL2_REPO_LATEST_COMMIT` build argument. This argument must be set to a URL-safe string corresponding to a commit or tag format that Github understands. I have tested this with full commit hashes and short commit hashes (e.g. the first 8 characters of the full commit hash). As suggested above, the `build` make target will  use Github's API to determine the commit hash for the latest commit to the ACL2 repo and pass that to Docker when building an image.

### Multi-Platform Building

The images on Docker Hub and the GitHub Container Registry are built using the `build-multiplatform` and `build-multiplatform-ghcr` make targets. To use these targets, you need to be using a Docker builder that is capable of building for both the `linux/amd64` and `linux/arm64` platforms. macOS' emulation for `linux/amd64` is at present insufficient, as it does not emulate FPU traps and ACL2 expects these traps to occur. So, I build the images using a Docker builder that consists of two nodes (an Apple Silicon machine and an x86-64 machine). The best information I've found on how to do this is in [this Medium post](https://medium.com/@spurin/using-docker-and-multiple-buildx-nodes-for-simultaneous-cross-platform-builds-cee0f797d939).

## Notes

By default, certification is done with 4 parallel tasks. This can be changed by overriding the `ACL2_CERT_JOBS` variable of the Makefile. For example, to use 2 tasks instead, run `make build ACL2_CERT_JOBS=2`.

To provide additional arguments to the `make` command that will be used to build ACL2's books, you can override the `ACL2_CERTIFY_OPTS` variable of the Makefile. Notice that this will override the effects of the `ACL2_CERT_JOBS` variable, so you will need to provide the appropriate `-j` option in that case.

By default, the "basic" book selection is certified. This can be changed by overriding the `ACL2_CERTIFY_TARGETS` build argument. Multiple targets can be provided to this argument if desired.

## Updating the Gradescope image

To update the Gradescope image, one should update the ACL2_COMMIT value in the make-gradescope.sh script to be the Git hash of the appropriate commit in the ACL2 repo. IMAGE_VERSION should also be modified to be some label appropriate for the semester.

## Why not Alpine?

Currently `docker-slim` is the base image used because [this osicat bug](https://github.com/osicat/osicat/issues/19) causes the ACL2 build to fail due to Alpine Linux's use of `musl` instead of `glibc` for its libc implementation.

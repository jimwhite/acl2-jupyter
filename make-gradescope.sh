#!/bin/bash

#sed 's|FROM debian:stable-slim|FROM gradescope/autograder-base:ubuntu-22.04|g' Dockerfile > Dockerfile-gradescope
export LOCAL_IMAGE_NAME=acl2_gradescope_autograder
export REMOTE_IMAGE_NAME=atwalter/acl2_gradescope_autograder
export DOCKERFILE=Dockerfile-gradescope
export IMAGE_VERSION=cs2800fa24

make build ACL2_COMMIT=1a6eb5cd12d6ed4982e2a5ba9614169ce74af0da
make push
#rm Dockerfile-gradescope

#!/bin/bash

sed 's|FROM debian:stable-slim|FROM gradescope/auto-builds:ubuntu-22.04|g' Dockerfile > Dockerfile-gradescope
export LOCAL_IMAGE_NAME=acl2_gradescope_autograder
export REMOTE_IMAGE_NAME=atwalter/acl2_gradescope_autograder
export DOCKERFILE=Dockerfile-gradescope
export IMAGE_VERSION=cs2800fa22

make build
make push
rm Dockerfile-gradescope

all: build
.PHONY: all build push push-ghcr build-multiplatform build-multiplatform-ghcr build-arm64 build-arm64-ghcr

# By default this builds the latest commit from source at https://github.com/acl2/acl2
# TODO: Default/easy selection of released version.
ACL2_COMMIT ?= $(shell curl --silent https://api.github.com/repos/acl2/acl2/commits/master | jq -r .sha)

BASE_IMAGE ?= quay.io/jupyter/minimal-notebook:latest
IMAGE_NAME ?= acl2-jupyter
IMAGE_VERSION ?= latest

DOCKERHUB_IMAGE_NAME ?= jimwhite/$(IMAGE_NAME)
GHCR_IMAGE_NAME ?= ghcr.io/jimwhite/$(IMAGE_NAME)

# Tried to use podman but had more flakiness in book certification, even with single job.
DOCKER ?= docker
DOCKERFILE ?= Dockerfile
PLATFORM ?= linux/amd64,linux/arm64
BUILD_CACHE ?=
# ACL2_CERT_JOBS ?= 1
# Some books like acl2s and centaur will sometimes fail certification when using multiple jobs.
# Make sure Docker has enough memory allocated if using max jobs.
ACL2_CERT_JOBS ?= $(shell nproc)
# `shell nproc` didn't work for multiplatform on MacOS.
# ACL2_CERT_JOBS ?= 12
# ACL2_CERTIFY_TARGETS="basic"
# ACL2 Bridge is CCL-only so we don't really need anything other than basic.
# ACL2_CERTIFY_TARGETS ?= regression acl2s centaur/bridge
ACL2_CERTIFY_TARGETS ?= basic
ACL2_CERTIFY_OPTS ?= "-j $(ACL2_CERT_JOBS)"

# https://github.com/yitzchak/archlinux-cl/blob/main/Dockerfile
# https://yitzchak.github.io/common-lisp-jupyter/install
# https://github.com/yitzchak/common-lisp-jupyter/blob/2df55291592943851d013c66af920e7c150b1de2/Dockerfile#L5C8-L5C43

# mkdir -p context/quicklisp/local-projects

# sha256 of quicklisp.lisp = 4a7a5c2aebe0716417047854267397e24a44d0cce096127411e9ce9ccfeb2c17
# wget -kL -P context https://beta.quicklisp.org/quicklisp.lisp

# git submodule add https://github.com/jimwhite/acl2-kernel.git context/acl2-kernel
# git submodule add https://github.com/yitzchak/archlinux-cl.git context/archlinux-cl
# git submodule add https://github.com/yitzchak/common-lisp-jupyter.git context/quicklisp/local-projects/common-lisp-jupyter
# git submodule add https://github.com/yitzchak/delta-vega.git context/quicklisp/local-projects/delta-vega
# git submodule add https://github.com/yitzchak/resizable-box-clj.git context/quicklisp/local-projects/resizable-box-clj
# git submodule add https://github.com/yitzchak/ngl-clj.git context/quicklisp/local-projects/ngl-clj

git-submodules:
	git submodule update --init --recursive --remote

build-multiplatform:
	$(DOCKER) buildx build --platform=$(PLATFORM) $(BUILD_CACHE) -t $(DOCKERHUB_IMAGE_NAME):$(IMAGE_VERSION) context \
		--build-arg BASE_IMAGE=$(BASE_IMAGE) \
		--build-arg ACL2_COMMIT=$(ACL2_COMMIT) --build-arg ACL2_CERTIFY_OPTS=$(ACL2_CERTIFY_OPTS) --build-arg "ACL2_CERTIFY_TARGETS=$(ACL2_CERTIFY_TARGETS)" -f $(DOCKERFILE) --push

build-multiplatform-ghcr:
	$(DOCKER) buildx build --platform=$(PLATFORM) $(BUILD_CACHE) -t $(GHCR_IMAGE_NAME):$(IMAGE_VERSION) context \
		--build-arg BASE_IMAGE=$(BASE_IMAGE) \
		--build-arg ACL2_COMMIT=$(ACL2_COMMIT) --build-arg ACL2_CERTIFY_OPTS=$(ACL2_CERTIFY_OPTS) --build-arg "ACL2_CERTIFY_TARGETS=$(ACL2_CERTIFY_TARGETS)" -f $(DOCKERFILE) --push

build-arm64:
	$(DOCKER) buildx build --platform=linux/arm64 $(BUILD_CACHE) -t $(DOCKERHUB_IMAGE_NAME):$(IMAGE_VERSION) context \
		--build-arg BASE_IMAGE=$(BASE_IMAGE) \
		--build-arg ACL2_COMMIT=$(ACL2_COMMIT) --build-arg ACL2_CERTIFY_OPTS=$(ACL2_CERTIFY_OPTS) --build-arg "ACL2_CERTIFY_TARGETS=$(ACL2_CERTIFY_TARGETS)" -f $(DOCKERFILE) --push

build-arm64-ghcr:
	$(DOCKER) buildx build --platform=linux/arm64 $(BUILD_CACHE) -t $(GHCR_IMAGE_NAME):$(IMAGE_VERSION) context \
		--build-arg BASE_IMAGE=$(BASE_IMAGE) \
		--build-arg ACL2_COMMIT=$(ACL2_COMMIT) --build-arg ACL2_CERTIFY_OPTS=$(ACL2_CERTIFY_OPTS) --build-arg "ACL2_CERTIFY_TARGETS=$(ACL2_CERTIFY_TARGETS)" -f $(DOCKERFILE) --push

build:
	$(DOCKER) buildx build context $(BUILD_CACHE) -t $(IMAGE_NAME):$(IMAGE_VERSION) \
		--build-arg BASE_IMAGE=$(BASE_IMAGE) \
		--build-arg ACL2_COMMIT=$(ACL2_COMMIT) --build-arg ACL2_CERTIFY_OPTS=$(ACL2_CERTIFY_OPTS) --build-arg "ACL2_CERTIFY_TARGETS=$(ACL2_CERTIFY_TARGETS)" -f $(DOCKERFILE)

push:
	$(DOCKER) image tag $(IMAGE_NAME):$(IMAGE_VERSION) $(DOCKERHUB_IMAGE_NAME):$(IMAGE_VERSION)
	$(DOCKER) push $(DOCKERHUB_IMAGE_NAME):$(IMAGE_VERSION)

push-ghcr:
	$(DOCKER) image tag $(IMAGE_NAME):$(IMAGE_VERSION) $(GHCR_IMAGE_NAME):$(IMAGE_VERSION)
	$(DOCKER) push $(GHCR_IMAGE_NAME):$(IMAGE_VERSION)

run:
	# docker run -it -p 8888:8888 -v $(PWD):/home/jovyan/work acl2-jupyter:latest
	$(DOCKER) run -it -p 8888:8888 -v $(PWD):/home/jovyan/work $(IMAGE_NAME):$(IMAGE_VERSION)

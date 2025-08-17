all: build
.PHONY: all build push push-ghcr build-multiplatform build-multiplatform-ghcr

ACL2_COMMIT ?= $(shell curl --silent https://api.github.com/repos/acl2/acl2/commits/master | jq -r .sha)

IMAGE_VERSION ?= latest
IMAGE_NAME ?= acl2
DOCKERHUB_IMAGE_NAME ?= jimwhite/$(IMAGE_NAME)
GHCR_IMAGE_NAME ?= ghcr.io/jimwhite/$(IMAGE_NAME)
# Tried to use podman but had more flakiness in book certification, even with single job.
DOCKER ?= docker
DOCKERFILE ?= Dockerfile
PLATFORM ?= linux/amd64,linux/arm64
BUILD_CACHE ?=
# Some books like acl2s and centaur will sometimes fail certification when using multiple jobs.
ACL2_CERT_JOBS ?= 12
# ACL2_CERTIFY_TARGETS="basic"
# ACL2 Bridge is CCL-only so we don't really need anything other than basic.
# ACL2_CERTIFY_TARGETS ?= regression acl2s centaur/bridge
ACL2_CERTIFY_TARGETS ?= basic
ACL2_CERTIFY_OPTS ?= "-j $(ACL2_CERT_JOBS)"

build-multiplatform:
	$(DOCKER) buildx build --platform=$(PLATFORM) $(BUILD_CACHE) -t $(DOCKERHUB_IMAGE_NAME):$(IMAGE_VERSION) context \
		--build-arg ACL2_COMMIT=$(ACL2_COMMIT) --build-arg ACL2_CERTIFY_OPTS=$(ACL2_CERTIFY_OPTS) --build-arg "ACL2_CERTIFY_TARGETS=$(ACL2_CERTIFY_TARGETS)" -f $(DOCKERFILE) --push

build-multiplatform-ghcr:
	$(DOCKER) buildx build --platform=$(PLATFORM) $(BUILD_CACHE) -t $(GHCR_IMAGE_NAME):$(IMAGE_VERSION) context \
		--build-arg ACL2_COMMIT=$(ACL2_COMMIT) --build-arg ACL2_CERTIFY_OPTS=$(ACL2_CERTIFY_OPTS) --build-arg "ACL2_CERTIFY_TARGETS=$(ACL2_CERTIFY_TARGETS)" -f $(DOCKERFILE) --push

build:
	$(DOCKER) build context $(BUILD_CACHE) -t $(IMAGE_NAME):$(IMAGE_VERSION) \
		--build-arg ACL2_COMMIT=$(ACL2_COMMIT) --build-arg ACL2_CERTIFY_OPTS=$(ACL2_CERTIFY_OPTS) --build-arg "ACL2_CERTIFY_TARGETS=$(ACL2_CERTIFY_TARGETS)" -f $(DOCKERFILE)

push:
	$(DOCKER) image tag $(IMAGE_NAME):$(IMAGE_VERSION) $(DOCKERHUB_IMAGE_NAME):$(IMAGE_VERSION)
	$(DOCKER) push $(DOCKERHUB_IMAGE_NAME):$(IMAGE_VERSION)

push-ghcr:
	$(DOCKER) image tag $(IMAGE_NAME):$(IMAGE_VERSION) $(GHCR_IMAGE_NAME):$(IMAGE_VERSION)
	$(DOCKER) push $(GHCR_IMAGE_NAME):$(IMAGE_VERSION)
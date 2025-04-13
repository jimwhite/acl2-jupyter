all: build
.PHONY: all build push push-ghcr build-multiplatform build-multiplatform-ghcr

ACL2_COMMIT ?= $(shell curl --silent https://api.github.com/repos/acl2/acl2/commits/master | jq -r .sha)

IMAGE_VERSION ?= latest
IMAGE_NAME ?= acl2
DOCKERHUB_IMAGE_NAME ?= atwalter/$(IMAGE_NAME)
GHCR_IMAGE_NAME ?= ghcr.io/mister-walter/$(IMAGE_NAME)
DOCKERFILE ?= Dockerfile
PLATFORM ?= linux/amd64,linux/arm64
ACL2_CERT_JOBS ?= 4
ACL2_CERTIFY_OPTS ?= "-j $(ACL2_CERT_JOBS)"

build-multiplatform:
	docker buildx build --platform=$(PLATFORM) -t $(DOCKERHUB_IMAGE_NAME):$(IMAGE_VERSION) . \
		--build-arg ACL2_COMMIT=$(ACL2_COMMIT) --build-arg ACL2_CERTIFY_OPTS=$(ACL2_CERTIFY_OPTS) -f $(DOCKERFILE) --push

build-multiplatform-ghcr:
	docker buildx build --platform=$(PLATFORM) -t $(GHCR_IMAGE_NAME):$(IMAGE_VERSION) . \
		--build-arg ACL2_COMMIT=$(ACL2_COMMIT) --build-arg ACL2_CERTIFY_OPTS=$(ACL2_CERTIFY_OPTS) -f $(DOCKERFILE) --push

build:
	docker build . -t $(IMAGE_NAME):$(IMAGE_VERSION) \
		--build-arg ACL2_COMMIT=$(ACL2_COMMIT) --build-arg ACL2_CERTIFY_OPTS=$(ACL2_CERTIFY_OPTS) -f $(DOCKERFILE)

push:
	docker image tag $(IMAGE_NAME):$(IMAGE_VERSION) $(DOCKERHUB_IMAGE_NAME):$(IMAGE_VERSION)
	docker push $(REMOTE_IMAGE_NAME):$(IMAGE_VERSION)

push-ghcr:
	docker image tag $(IMAGE_NAME):$(IMAGE_VERSION) $(GHCR_IMAGE_NAME):$(IMAGE_VERSION)
	docker push $(GHCR_IMAGE_NAME):$(IMAGE_VERSION)

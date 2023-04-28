all: build
.PHONY: all build push push-ghcr

ACL2_COMMIT ?= $(shell curl --silent https://api.github.com/repos/acl2/acl2/commits/master | jq -r .sha)

IMAGE_VERSION ?= latest
LOCAL_IMAGE_NAME ?= acl2
REMOTE_IMAGE_NAME ?= atwalter/acl2
DOCKERFILE ?= Dockerfile

build:
	docker build . -t $(LOCAL_IMAGE_NAME):$(IMAGE_VERSION) \
		--build-arg ACL2_COMMIT=$(ACL2_COMMIT) -f $(DOCKERFILE)

push:
	docker image tag $(LOCAL_IMAGE_NAME):$(IMAGE_VERSION) $(REMOTE_IMAGE_NAME):$(IMAGE_VERSION)
	docker push $(REMOTE_IMAGE_NAME):$(IMAGE_VERSION)

push-ghcr:
	docker image tag $(LOCAL_IMAGE_NAME):$(IMAGE_VERSION) ghcr.io/mister-walter/$(LOCAL_IMAGE_NAME):$(IMAGE_VERSION)
	docker push ghcr.io/mister-walter/$(LOCAL_IMAGE_NAME):$(IMAGE_VERSION)

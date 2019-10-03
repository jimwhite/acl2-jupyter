all: build
.PHONY: all build push

build:
	docker build . -t acl2:latest \
		--build-arg ACL2_REPO_LATEST_COMMIT=$(shell curl --silent https://api.github.com/repos/acl2/acl2/commits/master | jq -r .sha)

push:
	docker image tag acl2:latest atwalter/acl2:latest
	docker push atwalter/acl2:latest

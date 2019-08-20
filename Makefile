all: build
.PHONY: all build push

build:
	docker build . -t acl2:latest

push:
	docker image tag acl2:latest atwalter/acl2:latest
	docker push atwalter/acl2:latest

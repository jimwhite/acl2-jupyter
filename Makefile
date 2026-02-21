all: build
.PHONY: all build push push-ghcr build-multiplatform build-multiplatform-ghcr build-arm64 build-arm64-ghcr \
        notebooks notebooks-convert notebooks-execute notebooks-force notebooks-dir install-script2notebook

# By default this builds the latest commit from the main branch of https://github.com/jimwhite/acl2
# TODO: Default/easy selection of released version.
ACL2_GITHUB_REPO ?= jimwhite/acl2
ACL2_BRANCH ?= main
ACL2_COMMIT ?= $(shell curl --silent https://api.github.com/repos/$(ACL2_GITHUB_REPO)/commits/$(ACL2_BRANCH) | jq -r .sha)

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

ACL2_SAFETY ?= 
ACL2_BUILD_OPTS ?= "ACL2_SAFETY=$(ACL2_SAFETY)"

# ACL2_CERT_JOBS ?= 1
# Some books like acl2s and centaur will sometimes fail certification when using multiple jobs.
# Make sure Docker has enough memory allocated if using max jobs.
# ACL2_CERT_JOBS ?= $(shell nproc)
# `shell nproc` didn't work for multiplatform on MacOS.
ACL2_CERT_JOBS ?= 6
ACL2_CERTIFY_TARGETS ?= basic acl2s centaur/bridge/top.cert projects/smtlink/top.cert
# ACL2 Bridge is CCL-only so we don't really need anything other than basic.
# ACL2_CERTIFY_TARGETS ?= regression acl2s centaur/bridge
# ACL2_CERTIFY_TARGETS ?= all
ACL2_CERTIFY_OPTS ?= "-k -j $(ACL2_CERT_JOBS)"

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
	git submodule update --init --remote
	git submodule foreach --recursive 'git submodule update --init'

build-multiplatform:
	$(DOCKER) buildx build --platform=$(PLATFORM) $(BUILD_CACHE) -t $(DOCKERHUB_IMAGE_NAME):$(IMAGE_VERSION) context \
		--build-arg BASE_IMAGE=$(BASE_IMAGE) --build-arg ACL2_BUILD_OPTS=$(ACL2_BUILD_OPTS) \
		--build-arg ACL2_GITHUB_REPO=$(ACL2_GITHUB_REPO) --build-arg ACL2_COMMIT=$(ACL2_COMMIT) \
		--build-arg ACL2_CERTIFY_OPTS=$(ACL2_CERTIFY_OPTS) --build-arg "ACL2_CERTIFY_TARGETS=$(ACL2_CERTIFY_TARGETS)" \
		-f $(DOCKERFILE) --push

build-multiplatform-ghcr:
	$(DOCKER) buildx build --platform=$(PLATFORM) $(BUILD_CACHE) -t $(GHCR_IMAGE_NAME):$(IMAGE_VERSION) context \
		--build-arg BASE_IMAGE=$(BASE_IMAGE) --build-arg ACL2_BUILD_OPTS=$(ACL2_BUILD_OPTS) \
		--build-arg ACL2_GITHUB_REPO=$(ACL2_GITHUB_REPO) --build-arg ACL2_COMMIT=$(ACL2_COMMIT) \
		--build-arg ACL2_CERTIFY_OPTS=$(ACL2_CERTIFY_OPTS) --build-arg "ACL2_CERTIFY_TARGETS=$(ACL2_CERTIFY_TARGETS)" \
		-f $(DOCKERFILE) --push

build-arm64:
	$(DOCKER) buildx build --platform=linux/arm64 $(BUILD_CACHE) -t $(DOCKERHUB_IMAGE_NAME):$(IMAGE_VERSION) context \
		--build-arg BASE_IMAGE=$(BASE_IMAGE) --build-arg ACL2_BUILD_OPTS=$(ACL2_BUILD_OPTS) \
		--build-arg ACL2_GITHUB_REPO=$(ACL2_GITHUB_REPO) --build-arg ACL2_COMMIT=$(ACL2_COMMIT) \
		--build-arg ACL2_CERTIFY_OPTS=$(ACL2_CERTIFY_OPTS) --build-arg "ACL2_CERTIFY_TARGETS=$(ACL2_CERTIFY_TARGETS)" \
		-f $(DOCKERFILE) --push

build-arm64-ghcr:
	$(DOCKER) buildx build --platform=linux/arm64 $(BUILD_CACHE) -t $(GHCR_IMAGE_NAME):$(IMAGE_VERSION) context \
		--build-arg BASE_IMAGE=$(BASE_IMAGE) --build-arg ACL2_BUILD_OPTS=$(ACL2_BUILD_OPTS) \
		--build-arg ACL2_GITHUB_REPO=$(ACL2_GITHUB_REPO) --build-arg ACL2_COMMIT=$(ACL2_COMMIT) \
		--build-arg ACL2_CERTIFY_OPTS=$(ACL2_CERTIFY_OPTS) --build-arg "ACL2_CERTIFY_TARGETS=$(ACL2_CERTIFY_TARGETS)" \
		-f $(DOCKERFILE) --push

build:
	$(DOCKER) buildx build context $(BUILD_CACHE) -t $(IMAGE_NAME):$(IMAGE_VERSION) \
		--build-arg BASE_IMAGE=$(BASE_IMAGE) --build-arg ACL2_BUILD_OPTS=$(ACL2_BUILD_OPTS) \
		--build-arg ACL2_GITHUB_REPO=$(ACL2_GITHUB_REPO) --build-arg ACL2_COMMIT=$(ACL2_COMMIT) \
		--build-arg ACL2_CERTIFY_OPTS=$(ACL2_CERTIFY_OPTS) --build-arg "ACL2_CERTIFY_TARGETS=$(ACL2_CERTIFY_TARGETS)" \
		-f $(DOCKERFILE)

push:
	$(DOCKER) image tag $(IMAGE_NAME):$(IMAGE_VERSION) $(DOCKERHUB_IMAGE_NAME):$(IMAGE_VERSION)
	$(DOCKER) push $(DOCKERHUB_IMAGE_NAME):$(IMAGE_VERSION)

push-ghcr:
	$(DOCKER) image tag $(IMAGE_NAME):$(IMAGE_VERSION) $(GHCR_IMAGE_NAME):$(IMAGE_VERSION)
	$(DOCKER) push $(GHCR_IMAGE_NAME):$(IMAGE_VERSION)

run:
	# docker run -it -p 8888:8888 -v $(PWD):/home/jovyan/work acl2-jupyter:latest
	$(DOCKER) run -it -p 8888:8888 -v $(PWD):/home/jovyan/work $(IMAGE_NAME):$(IMAGE_VERSION)

# =============================================================================
# ACL2 Notebook Generation
# =============================================================================
# Convert ACL2 source files (.lisp) to Jupyter notebooks and execute
# certified ones through the ACL2 kernel to capture proof output.
# By default notebooks are placed alongside the source .lisp files (in-place).

.PHONY: notebooks notebooks-convert notebooks-execute install-script2notebook

# Source directory
ACL2_HOME ?= /home/acl2
NOTEBOOK_JOBS ?= 1
NOTEBOOK_CELL_TIMEOUT ?= 600
NOTEBOOK_STARTUP_TIMEOUT ?= 120

# Ensure script2notebook and build-notebooks are available
# Uses local tree-sitter-commonlisp fork with block comment fix.
install-script2notebook:
	@if ! command -v build-notebooks >/dev/null 2>&1; then \
		echo "Installing script2notebook via pipx..."; \
		pipx install $(PWD)/context/script2notebook/; \
		echo "Injecting local tree-sitter-commonlisp..."; \
		pipx inject script2notebook $(PWD)/context/tree-sitter-commonlisp/; \
	else \
		echo "build-notebooks already installed"; \
	fi

# Convert all ACL2 source files to notebooks (incremental, in-place)
notebooks-convert: install-script2notebook
	build-notebooks convert $(ACL2_HOME) -v

# Execute certified notebooks through ACL2 kernel (incremental, in-place)
notebooks-execute: install-script2notebook
	build-notebooks execute $(ACL2_HOME) -v \
		-j $(NOTEBOOK_JOBS) \
		--cell-timeout $(NOTEBOOK_CELL_TIMEOUT) \
		--startup-timeout $(NOTEBOOK_STARTUP_TIMEOUT)

# Convert + execute in one step (in-place)
notebooks: install-script2notebook
	build-notebooks all $(ACL2_HOME) -v \
		-j $(NOTEBOOK_JOBS) \
		--cell-timeout $(NOTEBOOK_CELL_TIMEOUT) \
		--startup-timeout $(NOTEBOOK_STARTUP_TIMEOUT)

# Force rebuild everything
notebooks-force: install-script2notebook
	build-notebooks all $(ACL2_HOME) -v --force \
		-j $(NOTEBOOK_JOBS) \
		--cell-timeout $(NOTEBOOK_CELL_TIMEOUT) \
		--startup-timeout $(NOTEBOOK_STARTUP_TIMEOUT)

# Convert + execute a single directory (usage: make notebooks-dir DIR=/home/acl2/books/defsort)
notebooks-dir: install-script2notebook
	@if [ -z "$(DIR)" ]; then echo "Usage: make notebooks-dir DIR=/home/acl2/books/some-dir"; exit 1; fi
	build-notebooks all $(DIR) -v \
		-j $(NOTEBOOK_JOBS) \
		--cell-timeout $(NOTEBOOK_CELL_TIMEOUT) \
		--startup-timeout $(NOTEBOOK_STARTUP_TIMEOUT)

# =============================================================================
# Rust and Parinfer Setup
# =============================================================================

CARGO_ENV := $(HOME)/.cargo/env

# Source cargo environment - use this prefix for any cargo commands
# Note: Each make recipe runs in a new shell, so we must source in each command
CARGO := . "$(CARGO_ENV)" 2>/dev/null && 

# Install Rust toolchain if not present
install-rust:
	@if [ ! -f "$(CARGO_ENV)" ]; then \
		echo "Installing Rust toolchain..."; \
		curl https://sh.rustup.rs -sSf | sh -s -- -y; \
		echo ""; \
		echo "Rust installed. To use cargo in this shell, run:"; \
		echo "  source $(CARGO_ENV)"; \
	else \
		echo "Rust already installed at $(CARGO_ENV)"; \
	fi

# Install parinfer-rust CLI (not on crates.io, must use GitHub)
install-parinfer: install-rust
	@$(CARGO) \
	if command -v parinfer-rust >/dev/null 2>&1; then \
		echo "parinfer-rust already installed"; \
	else \
		echo "Installing parinfer-rust from GitHub..."; \
		cargo install --git https://github.com/eraserhd/parinfer-rust; \
	fi

# Test parinfer-rust installation  
test-parinfer:
	@$(CARGO) echo '(def x' | parinfer-rust -m indent
	@$(CARGO) echo '(defun foo (x)' | parinfer-rust -m indent --lisp-block-comments
	@echo "Parinfer tests passed!"

# Run a command with Rust/Cargo environment
# Usage: make cargo-run CMD="cargo --version"
cargo-run:
	@$(CARGO) $(CMD)

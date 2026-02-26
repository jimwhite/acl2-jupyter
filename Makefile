all: build
.PHONY: all build push push-ghcr build-multiplatform build-multiplatform-ghcr build-arm64 build-arm64-ghcr \
        notebooks notebooks-convert notebooks-execute notebooks-force notebooks-dir install-script2notebook \
        lisp2nb lisp2nb-force lisp2nb-books sanitize-lisp \
        test-lisp2nb test-lisp2nb-annotations test-lisp2nb-all

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
#
# Pattern rules let `make -j 8` handle parallelism naturally.

.PHONY: notebooks notebooks-convert notebooks-execute install-script2notebook \
       boot-metadata notebooks-inject-boot-metadata \
       lisp2nb lisp2nb-force lisp2nb-books sanitize-lisp

# Source directory
ACL2_HOME ?= /home/acl2
NOTEBOOK_JOBS ?= 8
NOTEBOOK_CELL_TIMEOUT ?= 600
NOTEBOOK_STARTUP_TIMEOUT ?= 120

# CL-based .lisp → .ipynb conversion tool
LISP2NB := $(PWD)/context/script2notebook/lisp2nb.lisp

# Workspace Python venv — all Python/pip commands run through this.
VENV ?= $(PWD)/.venv
VENV_PYTHON := $(VENV)/bin/python
VENV_PIP := $(VENV)/bin/pip
BUILD_NOTEBOOKS := $(VENV)/bin/build-notebooks

# Rename non-source .lisp files so they are not picked up by find
sanitize-lisp:
	@if [ -f "$(ACL2_HOME)/mcl-acl2-startup.lisp" ]; then \
		mv "$(ACL2_HOME)/mcl-acl2-startup.lisp" "$(ACL2_HOME)/mcl-acl2-startup.lisp.txt"; \
		echo "Renamed mcl-acl2-startup.lisp → mcl-acl2-startup.lisp.txt"; \
	fi

# Source file lists (skips .sys/ auto-generated useless-runes)
LISP_SOURCES := $(shell find $(ACL2_HOME) -name '*.lisp' -not -path '*/.sys/*' 2>/dev/null)
LSP_SOURCES  := $(shell find $(ACL2_HOME) -name '*.lsp'  -not -path '*/.sys/*' 2>/dev/null)
ALL_NOTEBOOKS := $(LISP_SOURCES:.lisp=.ipynb) $(LSP_SOURCES:.lsp=.ipynb)

# Top-level only
TOP_LISP := $(wildcard $(ACL2_HOME)/*.lisp)
TOP_NOTEBOOKS := $(TOP_LISP:.lisp=.ipynb)

# Pattern rules — one sbcl process per file
%.ipynb: %.lisp $(LISP2NB)
	@sbcl --noinform --non-interactive --disable-debugger \
		--load "$(LISP2NB)" \
		--eval '(lisp2nb:convert-file "$<" :markdown-bracket :fenced)' \
		--eval '(uiop:quit 0)' >/dev/null 2>&1 \
	|| echo "FAIL $<"

%.ipynb: %.lsp $(LISP2NB)
	@sbcl --noinform --non-interactive --disable-debugger \
		--load "$(LISP2NB)" \
		--eval '(lisp2nb:convert-file "$<" :markdown-bracket :fenced)' \
		--eval '(uiop:quit 0)' >/dev/null 2>&1 \
	|| echo "FAIL $<"

# Ensure the venv exists and build_notebooks (execute phase) is available.
install-script2notebook: $(VENV)/bin/activate
	@if [ ! -x "$(BUILD_NOTEBOOKS)" ]; then \
		echo "Installing script2notebook into venv..."; \
		$(VENV_PIP) install -e $(PWD)/context/script2notebook/; \
	else \
		echo "build-notebooks already installed in venv"; \
	fi

$(VENV)/bin/activate:
	@if [ ! -f "$(VENV)/bin/activate" ]; then \
		echo "Creating venv at $(VENV)..."; \
		python3 -m venv $(VENV); \
	fi

# Convert all source files to notebooks (use: make -j 8 notebooks-convert)
notebooks-convert: sanitize-lisp $(ALL_NOTEBOOKS)

# Convert top-level ACL2 source files only (non-recursive)
lisp2nb: sanitize-lisp $(TOP_NOTEBOOKS)

# Force reconvert top-level ACL2 source files
lisp2nb-force: sanitize-lisp
	rm -f $(TOP_NOTEBOOKS)
	$(MAKE) -j $(NOTEBOOK_JOBS) $(TOP_NOTEBOOKS)

# Convert all .lisp/.lsp files under ACL2_HOME recursively (inc. books)
lisp2nb-books: notebooks-convert

# Execute certified notebooks through ACL2 kernel (incremental, in-place)
notebooks-execute: deploy-kernel install-script2notebook
	$(BUILD_NOTEBOOKS) execute $(ACL2_HOME) -v \
		-j $(NOTEBOOK_JOBS) \
		--cell-timeout $(NOTEBOOK_CELL_TIMEOUT) \
		--startup-timeout $(NOTEBOOK_STARTUP_TIMEOUT)

# Convert + execute in one step
notebooks: notebooks-convert notebooks-execute

# Force reconvert all + re-execute
notebooks-force: sanitize-lisp deploy-kernel install-script2notebook
	find $(ACL2_HOME) -name '*.ipynb' -not -path '*/.sys/*' -delete
	$(MAKE) -j $(NOTEBOOK_JOBS) notebooks-convert
	$(BUILD_NOTEBOOKS) execute $(ACL2_HOME) -v --force \
		-j $(NOTEBOOK_JOBS) \
		--cell-timeout $(NOTEBOOK_CELL_TIMEOUT) \
		--startup-timeout $(NOTEBOOK_STARTUP_TIMEOUT)

# Convert + execute a single directory (usage: make notebooks-dir DIR=/home/acl2/books/defsort)
notebooks-dir: deploy-kernel install-script2notebook
	@if [ -z "$(DIR)" ]; then echo "Usage: make notebooks-dir DIR=/home/acl2/books/some-dir"; exit 1; fi
	$(MAKE) -j $(NOTEBOOK_JOBS) $$(find $(DIR) \( -name '*.lisp' -o -name '*.lsp' \) \
		-not -path '*/.sys/*' | sed 's/\.[^.]*$$/.ipynb/')
	$(BUILD_NOTEBOOKS) execute $(DIR) -v \
		-j $(NOTEBOOK_JOBS) \
		--cell-timeout $(NOTEBOOK_CELL_TIMEOUT) \
		--startup-timeout $(NOTEBOOK_STARTUP_TIMEOUT)

# =============================================================================
# ACL2 Source Boot-strap Metadata Capture
# =============================================================================
# The ACL2 source files (axioms.lisp, basis-a.lisp, etc.) are NOT certifiable
# books — they built the saved_acl2 image via a two-pass boot-strap process.
# This target re-runs that process with instrumentation to capture per-file
# event metadata (event landmarks, package state) into .boot-metadata/ JSON.
#
# Prerequisites: ACL2 must have been compiled (make compile / make full).
# Runtime: roughly the same as 'make init' (~10-20 min).

CAPTURE_LOADER := $(PWD)/context/acl2-jupyter-kernel/capture-boot-metadata-loader.lisp

# Capture boot-strap metadata from ACL2 source files
boot-metadata:
	cd $(ACL2_HOME) && sbcl \
		--dynamic-space-size 32000 \
		--control-stack-size 64 \
		--disable-ldb \
		--disable-debugger \
		--no-userinit \
		--load "$(CAPTURE_LOADER)"

# Inject captured boot-strap metadata into source notebooks (per-cell)
INJECT_BOOT_METADATA := $(VENV)/bin/inject-boot-metadata
notebooks-inject-boot-metadata: install-script2notebook
	$(INJECT_BOOT_METADATA) $(ACL2_HOME) -v --force

# =============================================================================
# ACL2 Boot-strap Notebook Execution (Pass-2-Only)
# =============================================================================
# Runs pass 1 internally via ACL2's ld-fn (correctly handling *1* functions,
# command landmarks, etc.), then executes pass-2 notebooks through the kernel
# REPL to capture per-cell events and forms.
#
# Prerequisites:
#   - ACL2 compiled (saved_acl2 built, but we start from init.lisp)
#   - Notebooks converted from .lisp via lisp2nb
#   - script2notebook installed in venv

BOOTSTRAP_SCRIPT := $(VENV)/bin/build-boot-strap
BOOTSTRAP_STARTUP_TIMEOUT ?= 1200
KERNEL_SRC := $(PWD)/context/acl2-jupyter-kernel
KERNEL_DST := $(HOME)/quicklisp/local-projects/acl2-jupyter-kernel

.PHONY: bootstrap-pass2 deploy-kernel install-kernel bootstrap notebooks-tar

INSTALL_KERNELSPEC := $(KERNEL_SRC)/install-kernelspec.sh

# Deploy kernel source to quicklisp local-projects and clear FASL cache.
# Uses the same glob copy as install-kernelspec.sh (no hardcoded file list).
deploy-kernel:
	@mkdir -p "$(KERNEL_DST)"
	cp -a "$(KERNEL_SRC)"/*.lisp "$(KERNEL_SRC)"/*.asd "$(KERNEL_SRC)"/*.sh "$(KERNEL_DST)/"
	rm -rf $(HOME)/.cache/common-lisp/sbcl-*/home/jovyan/quicklisp/local-projects/acl2-jupyter-kernel/
	@echo "Kernel deployed and FASL cache cleared."

# Full install: deploy source + register kernelspec via saved_acl2
install-kernel:
	$(INSTALL_KERNELSPEC)

# Execute pass-2 notebooks (pass 1 runs inside kernel via ld-fn)
bootstrap-pass2: install-script2notebook
	$(BOOTSTRAP_SCRIPT) $(ACL2_HOME) \
		--pass2-only \
		--cell-timeout $(NOTEBOOK_CELL_TIMEOUT) \
		--startup-timeout $(BOOTSTRAP_STARTUP_TIMEOUT) \
		-v 2>&1

# Full pipeline: deploy kernel → convert .lisp → execute pass-2 notebooks
bootstrap: deploy-kernel lisp2nb bootstrap-pass2

notebooks-tar:
	find $(ACL2_HOME) -name '*.ipynb' -print0 | tar -czvf notebooks.tar.gz --null --files-from -

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

# ─── lisp2nb tests ──────────────────────────────────────────────────

# Core convert-file tests: structure, placeholders, edge cases
test-lisp2nb:
	@sbcl --noinform --non-interactive --disable-debugger \
		--load $(PWD)/context/script2notebook/test_lisp2nb.lisp

# Annotation tests: inner comments, docstrings, provenance
test-lisp2nb-annotations:
	@sbcl --noinform --non-interactive --disable-debugger \
		--load $(PWD)/context/script2notebook/test_lisp2nb_annotations.lisp

# Run all lisp2nb tests
test-lisp2nb-all: test-lisp2nb test-lisp2nb-annotations

# Test parinfer-rust installation  
test-parinfer:
	@$(CARGO) echo '(def x' | parinfer-rust -m indent
	@$(CARGO) echo '(defun foo (x)' | parinfer-rust -m indent --lisp-block-comments
	@echo "Parinfer tests passed!"

# Run a command with Rust/Cargo environment
# Usage: make cargo-run CMD="cargo --version"
cargo-run:
	@$(CARGO) $(CMD)

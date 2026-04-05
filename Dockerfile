# syntax=docker/dockerfile:1
# Multi-stage Docker build for acl2-jupyter
#
# Build targets:
#   --target jupyter  (default) — ACL2 + Jupyter kernel, without certified books
#   --target books             — extends jupyter with certified books
#
# Builder stages (the only multi-stage layers used):
#   sbcl-builder / ccl-builder  compile/download the Lisp implementation
#   z3-builder                  compile Z3 SMT solver
#   stp-builder                 compile STP SAT solver (static binary)
#
# ACL2 and Quicklisp are built directly in the jupyter stage so that
# saved_acl2 and all Lisp binaries share a single consistent environment.
#
# Key build arguments:
#   LISP                  sbcl (default) | ccl  (ccl is x86_64 only)
#   ACL2_GITHUB_REPO      ACL2 source repository (owner/repo)
#   ACL2_COMMIT           ACL2 git commit hash
#   ACL2_REF              Tag label or branch name used in kernel/image naming
#   WITH_REAL             0 (default) | 1  — build ACL2(r) with real numbers
#   WITH_Z3               1 (default) | 0  — include Z3 SMT solver
#   WITH_STP              1 (default) | 0  — include STP SAT solver
#   SBCL_VERSION          SBCL version to compile (LISP=sbcl only)
#   CCL_VERSION           CCL version to download  (LISP=ccl only)
#   Z3_VERSION            Z3 version to compile    (WITH_Z3=1 only)
#   STP_BUILD_JOBS        Parallelism flag for STP cmake build
#   ACL2_BUILD_OPTS       Extra options passed to ACL2 make
#   ACL2_CERTIFY_TARGETS  Books make targets      (books target only)
#   ACL2_CERTIFY_OPTS     Options for books make  (books target only)

ARG BASE_IMAGE=quay.io/jupyter/minimal-notebook:latest
ARG LISP=sbcl

# ============================================================================
# Stage: sbcl-builder — compile SBCL from source
# ============================================================================
FROM ${BASE_IMAGE} AS sbcl-builder

ARG SBCL_VERSION=2.6.1
USER root

RUN apt-get update && apt-get install -y --no-install-recommends \
        bzip2 \
        build-essential \
        ca-certificates \
        libzstd-dev \
        sbcl \
        wget \
        zlib1g-dev \
    && rm -rf /var/lib/apt/lists/*

RUN mkdir /build-sbcl \
    && cd /build-sbcl \
    && wget "https://github.com/sbcl/sbcl/archive/refs/tags/sbcl-${SBCL_VERSION}.tar.gz" \
         -O sbcl.tar.gz -q \
    && tar -xzf sbcl.tar.gz \
    && rm sbcl.tar.gz \
    && cd sbcl-* \
    && sh make.sh \
         --without-immobile-space \
         --without-immobile-code \
         --without-compact-instance-header \
         --fancy \
         --dynamic-space-size=4Gb \
    && apt-get remove -y sbcl \
    && sh install.sh \
    && cd / \
    && rm -rf /build-sbcl

# ============================================================================
# Stage: ccl-builder — download pre-built CCL binary (x86_64 only)
# ============================================================================
FROM ${BASE_IMAGE} AS ccl-builder

ARG CCL_VERSION=1.12.2
USER root

RUN apt-get update && apt-get install -y --no-install-recommends \
        ca-certificates \
        wget \
    && rm -rf /var/lib/apt/lists/* \
    && mkdir -p /usr/local/ccl \
    && wget "https://github.com/Clozure/ccl/releases/download/v${CCL_VERSION}/ccl-${CCL_VERSION}-linuxx86.tar.gz" \
         -O /tmp/ccl.tar.gz -q \
    && tar -xzf /tmp/ccl.tar.gz -C /usr/local/ccl --strip-components=1 \
    && rm /tmp/ccl.tar.gz \
    && ln -sf /usr/local/ccl/lx86cl64 /usr/local/bin/ccl

# ============================================================================
# Stage: lisp — select Lisp implementation (resolves to sbcl-builder or ccl-builder)
# BuildKit only builds the selected builder; the other is skipped entirely.
# ============================================================================
FROM ${LISP}-builder AS lisp

# ============================================================================
# Stage: z3-builder — compile Z3 SMT solver from source
# ============================================================================
FROM ${BASE_IMAGE} AS z3-builder

ARG Z3_VERSION=4.15.7
USER root

RUN apt-get update && apt-get install -y --no-install-recommends \
        build-essential \
        cmake \
        ca-certificates \
        python3-dev \
        wget \
    && rm -rf /var/lib/apt/lists/*

RUN mkdir /build-z3 \
    && cd /build-z3 \
    && wget "https://github.com/Z3Prover/z3/archive/refs/tags/z3-${Z3_VERSION}.tar.gz" \
         -O z3.tar.gz -q \
    && tar -xzf z3.tar.gz --strip-components=1 \
    && ./configure --prefix=/usr/local \
    && cd build \
    && make -j$(nproc) \
    && make install \
    && cd / \
    && rm -rf /build-z3

# ============================================================================
# Stage: stp-builder — compile STP SAT solver from source (static binary)
# ============================================================================
FROM ${BASE_IMAGE} AS stp-builder

# GitHub runner gets OOM running parallel build
ARG STP_BUILD_JOBS="--parallel"
USER root

RUN apt-get update && apt-get install -y --no-install-recommends \
        bison \
        build-essential \
        cmake \
        flex \
        g++ \
        libboost-program-options-dev \
        libgmp-dev \
        libm4ri-dev \
        libtinfo-dev \
        pkg-config \
        zlib1g-dev \
    && rm -rf /var/lib/apt/lists/*

COPY stp /build-stp
RUN cd /build-stp \
    && ./scripts/deps/setup-gtest.sh \
    && ./scripts/deps/setup-cms.sh \
    && ./scripts/deps/setup-minisat.sh \
    && mkdir build && cd build \
    && cmake .. -DENABLE_TESTING=ON -DSTATICCOMPILE=ON -DFORCE_CMS=ON \
    && cmake --build . ${STP_BUILD_JOBS} \
    && cmake --install . \
    && cd / \
    && rm -rf /build-stp

# ============================================================================
# Stage: jupyter — final runtime image (ACL2 + Jupyter kernel, no books)
#
# ACL2 is compiled here directly so that saved_acl2 and the Lisp runtime
# share the same filesystem — no cross-stage binary compatibility issues.
# Quicklisp packages are also installed here for the same reason.
# ============================================================================
FROM ${BASE_IMAGE} AS jupyter
LABEL org.opencontainers.image.source="https://github.com/jimwhite/acl2-jupyter"
LABEL org.opencontainers.image.description="A Docker image for running the ACL2 theorem proving system in JupyterLab"
LABEL org.opencontainers.image.licenses=BSD-3-Clause

ARG LISP=sbcl
ARG ACL2_GITHUB_REPO=jimwhite/acl2
ARG ACL2_COMMIT=0
# ACL2_REF: release tag (e.g. "8.7") or branch/hash label used for naming
ARG ACL2_REF=latest
ARG WITH_REAL=0
ARG WITH_Z3=1
ARG WITH_STP=1
ARG ACL2_BUILD_OPTS=""
ARG USER=jovyan

ENV HOME=/home/${USER}
ENV ACL2_HOME=/home/acl2
ENV ACL2_SYSTEM_BOOKS="${ACL2_HOME}/books"
ENV ACL2_SNAPSHOT_INFO="${ACL2_GITHUB_REPO} git commit hash: ${ACL2_COMMIT}"

USER root

# This will have RW permission for the ACL2 directory.
# `sudo` does not require a password.
RUN echo 'jovyan ALL=(ALL) NOPASSWD: ALL' >> /etc/sudoers \
    && adduser jovyan sudo \
    && groupadd acl2 \
    && usermod -aG acl2 ${USER} \
    && mkdir /opt/acl2 \
    && chown -R ${USER}:acl2 /opt/acl2 \
    && chmod -R g+rx /opt/acl2

# Runtime packages (mirrors the pre-revamp single-stage package set)
# nodejs and npm for Claude Code (TODO: switch to Deno)
# retry may be used to retry flaky book certification makefiles
RUN apt-get update && apt-get install -y --no-install-recommends \
        autoconf \
        automake \
        bison \
        build-essential \
        ca-certificates \
        cmake \
        curl \
        file \
        flex \
        git \
        git-lfs \
        hashalot \
        libboost-program-options-dev \
        libcurl4-openssl-dev \
        libczmq-dev \
        libgmp-dev \
        libm4ri-dev \
        libssl-dev \
        libtinfo-dev \
        libzstd-dev \
        make \
        nodejs npm \
        perl \
        pipx \
        pkg-config \
        python3-dev \
        retry \
        rlwrap \
        rsync \
        unzip \
        wget \
        zlib1g-dev \
    && rm -rf /var/lib/apt/lists/*

# Install Lisp from the lisp builder stage.  ACL2 will be compiled directly
# below using this same binary, so saved_acl2 and the runtime are consistent.
RUN --mount=type=bind,from=lisp,target=/tmp/lisp-stage \
    if [ "${LISP}" = "sbcl" ]; then \
        cp /tmp/lisp-stage/usr/local/bin/sbcl /usr/local/bin/sbcl \
        && mkdir -p /usr/local/lib \
        && cp -r /tmp/lisp-stage/usr/local/lib/sbcl /usr/local/lib/sbcl \
        && ldconfig; \
    elif [ "${LISP}" = "ccl" ]; then \
        mkdir -p /usr/local/ccl \
        && cp -r /tmp/lisp-stage/usr/local/ccl/. /usr/local/ccl/ \
        && ln -sf /usr/local/ccl/lx86cl64 /usr/local/bin/ccl; \
    fi

# Install Z3 (optional).  Uses --mount so no layer cost when WITH_Z3=0.
RUN --mount=type=bind,from=z3-builder,target=/tmp/z3-stage \
    if [ "${WITH_Z3}" = "1" ]; then \
        cp /tmp/z3-stage/usr/local/bin/z3 /usr/local/bin/z3 \
        && find /tmp/z3-stage/usr/local/lib -name 'libz3*' -exec cp {} /usr/local/lib/ \; \
        && ldconfig \
        && HOME=/root conda install -y z3-solver; \
    fi

# Install STP (optional, statically compiled).  No layer cost when WITH_STP=0.
RUN --mount=type=bind,from=stp-builder,target=/tmp/stp-stage \
    if [ "${WITH_STP}" = "1" ]; then \
        cp /tmp/stp-stage/usr/local/bin/stp /usr/local/bin/stp; \
    fi

# Set up ACL2 home directory, download ACL2, and build it directly in this stage.
# Keeping the Lisp runtime and ACL2 build in the same environment ensures
# saved_acl2 (a shell script invoking the Lisp binary) can always execute.
RUN mkdir -p ${ACL2_HOME} \
    && chown -R ${USER}:acl2 ${ACL2_HOME} \
    && chmod -R g+rx ${ACL2_HOME}

RUN wget "https://api.github.com/repos/${ACL2_GITHUB_REPO}/zipball/${ACL2_COMMIT}" \
         -O /tmp/acl2.zip -q \
    && unzip -qq /tmp/acl2.zip -d /tmp/acl2_extract \
    && mv -T /tmp/acl2_extract/$(ls /tmp/acl2_extract) ${ACL2_HOME} \
    && rmdir /tmp/acl2_extract \
    && rm /tmp/acl2.zip \
    && chown -R ${USER}:acl2 ${ACL2_HOME}

USER ${USER}

RUN cd ${ACL2_HOME} \
    && if [ "${WITH_REAL}" = "1" ]; then \
           make LISP="${LISP}" ACL2_REAL=r ACL2_SNAPSHOT_INFO="${ACL2_COMMIT}" ${ACL2_BUILD_OPTS} \
               || (tail -500 make.log && false); \
       else \
           make LISP="${LISP}" ACL2_SNAPSHOT_INFO="${ACL2_COMMIT}" ${ACL2_BUILD_OPTS} \
               || (tail -500 make.log && false); \
       fi

USER root

RUN if [ "${WITH_REAL}" = "1" ]; then saved=saved_acl2r; else saved=saved_acl2; fi \
    && mkdir -p /opt/acl2/bin \
    && ln -s ${ACL2_HOME}/${saved}   /opt/acl2/bin/acl2 \
    && ln -s ${ACL2_HOME}/${saved}   /opt/acl2/bin/saved_acl2 \
    && ln -s ${ACL2_HOME}/books/build/cert.pl     /opt/acl2/bin/cert.pl \
    && ln -s ${ACL2_HOME}/books/build/clean.pl    /opt/acl2/bin/clean.pl \
    && ln -s ${ACL2_HOME}/books/build/critpath.pl /opt/acl2/bin/critpath.pl

ENV PATH="/opt/acl2/bin:${PATH}"
ENV ACL2="/opt/acl2/bin/saved_acl2"

USER ${USER}

# Install Quicklisp and common-lisp-jupyter directly in this stage.
COPY --chown=${USER}:users quicklisp.lisp quicklisp.lisp
COPY --chown=${USER}:users quicklisp quicklisp/
COPY --chown=${USER}:users acl2-jupyter-kernel quicklisp/local-projects/acl2-jupyter-kernel

RUN if [ "${LISP}" = "sbcl" ]; then \
        sbcl --non-interactive --load quicklisp.lisp \
            --eval "(quicklisp-quickstart:install)" \
            --eval "(ql-util:without-prompting (ql:add-to-init-file))" \
            --eval "(ql:quickload '(:common-lisp-jupyter :cytoscape-clj :kekule-clj :resizable-box-clj :ngl-clj :delta-vega))" \
            --eval "(clj:install :implementation t)"; \
    elif [ "${LISP}" = "ccl" ]; then \
        ccl --load quicklisp.lisp \
            --eval "(quicklisp-quickstart:install)" \
            --eval "(ql-util:without-prompting (ql:add-to-init-file))" \
            --eval "(ql:quickload '(:common-lisp-jupyter :cytoscape-clj :kekule-clj :resizable-box-clj :ngl-clj :delta-vega))" \
            --eval "(clj:install :implementation t)" \
            --eval "(ccl:quit)"; \
    fi

ENV QUICKLISP=1

# ACL2 Jupyter kernel (overrides the copy already present in Quicklisp local-projects)
COPY --chown=${USER}:users acl2-jupyter-kernel \
    /home/jovyan/quicklisp/local-projects/acl2-jupyter-kernel

# VSCode extension for ACL2/Common Lisp language support and notebook renderer
COPY extension/acl2-language /opt/acl2/vscode-extensions/acl2-language

# Install ACL2 Jupyter kernelspec (registers kernel name "acl2" initially)
COPY --chown=${USER}:users --chmod=755 \
    acl2-jupyter-kernel/install-kernelspec.sh /opt/acl2/bin/install-kernelspec.sh
RUN /opt/acl2/bin/install-kernelspec.sh

# Rename kernelspec to a unique ID: acl2-<source>[-<lisp>][-real][-z3][-stp]
#   <source> = ACL2_REF when it starts with a digit (release tag, e.g. "8.7")
#            = first 8 chars of ACL2_COMMIT otherwise
RUN source_id=$(echo "${ACL2_REF}" | grep -qE '^[0-9]' \
            && echo "${ACL2_REF}" \
            || printf '%.8s' "${ACL2_COMMIT}") \
    && lisp_part=$([ "${LISP}" != "sbcl" ] && echo "-${LISP}" || echo "") \
    && real_part=$([ "${WITH_REAL}" = "1" ] && echo "-real" || echo "") \
    && tools_part="" \
    && { [ "${WITH_Z3}"  = "1" ] && tools_part="${tools_part}-z3";  } || true \
    && { [ "${WITH_STP}" = "1" ] && tools_part="${tools_part}-stp"; } || true \
    && kernel_name="acl2-${source_id}${lisp_part}${real_part}${tools_part}" \
    && kernels_dir="${HOME}/.local/share/jupyter/kernels" \
    && mv "${kernels_dir}/acl2" "${kernels_dir}/${kernel_name}" \
    && KERNEL="${kernel_name}" KDIR="${kernels_dir}" \
       python3 -c "\
import json, os; \
p = os.path.join(os.environ['KDIR'], os.environ['KERNEL'], 'kernel.json'); \
spec = json.load(open(p)); \
spec['display_name'] = 'ACL2 (' + os.environ['KERNEL'] + ')'; \
json.dump(spec, open(p, 'w'), indent=2)"

# ============================================================================
# Stage: books — certify books (extends jupyter; build with --target books)
#
# Image name convention: acl2-<source>[-<lisp>][-real][-z3][-stp]-<books>
# Examples:
#   acl2-8.7-basic
#   acl2-8.7-ccl-regression
#   acl2-8.7-real-z3-stp-basic-nonstd
#   acl2-f6167977-ccl-real-all
# ============================================================================
FROM jupyter AS books
LABEL org.opencontainers.image.description="A Docker image for running the ACL2 theorem proving system and certified books in JupyterLab"

ARG ACL2_CERTIFY_OPTS="-k -j 6"
ARG ACL2_CERTIFY_TARGETS="basic"
ARG USER=jovyan

SHELL ["/bin/bash", "-c"]
USER ${USER}

RUN if [ "${WITH_REAL}" = "1" ]; then saved=saved_acl2r; else saved=saved_acl2; fi \
    && cd ${ACL2_HOME}/books \
    && make ACL2=${ACL2_HOME}/${saved} ${ACL2_CERTIFY_OPTS} ${ACL2_CERTIFY_TARGETS} \
       >make-books.stdout.log 2> >(tee make-books.stderr.log >&2) ; \
    find * -type f -name "*.cert.out" | tar -czvf make-books-cert-out.tar.gz -T -

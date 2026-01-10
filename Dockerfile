ARG BASE_IMAGE=quay.io/jupyter/minimal-notebook:latest

FROM ${BASE_IMAGE}
LABEL org.opencontainers.image.source="https://github.com/jimwhite/acl2-jupyter"
LABEL org.opencontainers.image.description="A Docker image for running the ACL2 theorem proving system and books in JupyterLab"
LABEL org.opencontainers.image.licenses=BSD-3-Clause

ARG SBCL_VERSION=2.5.11

ARG Z3_VERSION=4.15.4

ARG USER=jovyan
ENV HOME=/home/${USER}

ARG ACL2_COMMIT=0
ENV ACL2_SNAPSHOT_INFO="Git commit hash: ${ACL2_COMMIT}"
ARG ACL2_BUILD_OPTS=""
ARG ACL2_CERTIFY_OPTS="-k -j 6"
ARG ACL2_CERTIFY_TARGETS="basic"
# The ACL2 Bridge and such for Jupyter need everything.
# ARG ACL2_CERTIFY_TARGETS="all acl2s centaur/bridge"

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

# Based on https://github.com/wshito/roswell-base

# openssl-dev is needed for Quicklisp
# perl is needed for ACL2's certification scripts
# wget is needed for downloading some files while building the docker image
# The rest are needed for Roswell

# libczmq-dev because otherwise loading quicklisp in sbcl gets:
# quicklisp/software/pzmq-20210531-git/grovel__grovel.c:6:10: fatal error: zmq.h: No such file or directory
#    6 | #include <zmq.h>
# https://github.com/yitzchak/common-lisp-jupyter/blob/2df55291592943851d013c66af920e7c150b1de2/docs/install.md?plain=1#L18

# pipx is for poetry install for acl2-kernel

# nodejs and npm for Claude Code
# TODO: Switch to Deno.

# retry might be used to retry book certification makefiles that are flaky.

RUN apt-get update && \
    apt-get install -y --no-install-recommends \
        build-essential \
        gcc \
        git \
        automake \
        autoconf \
        make \
        libcurl4-openssl-dev \
        ca-certificates \
        libssl-dev \
        wget \
        perl \
        zlib1g-dev \
        libzstd-dev \
        libczmq-dev \
        curl \
        unzip \
        nodejs npm \
        pipx \
        rlwrap \
        retry \
        sbcl \
    && rm -rf /var/lib/apt/lists/* # remove cached apt files

# This /root/sbcl dir seems to be a tmp so why in /root?
RUN mkdir /root/sbcl \
    && cd /root/sbcl \
    && wget "https://github.com/sbcl/sbcl/archive/refs/tags/sbcl-${SBCL_VERSION}.tar.gz" -O sbcl.tar.gz -q \
    && tar -xzf sbcl.tar.gz \
    && rm sbcl.tar.gz \
    && cd sbcl-* \
    && sh make.sh --without-immobile-space --without-immobile-code --without-compact-instance-header --fancy --dynamic-space-size=4Gb \
    && apt-get remove -y sbcl \
    && sh install.sh \
    && cd /root \
    && rm -R /root/sbcl

# Include Z3
# Do we get everything with pip? pip install z3-solver
RUN mkdir /root/z3 \
    && cd /root/z3 \
    && wget "https://github.com/Z3Prover/z3/archive/refs/tags/z3-${Z3_VERSION}.tar.gz" -O z3.tar.gz -q \
    && tar -xzf z3.tar.gz --strip-components=1 \
    && ./configure \
    && cd build \
    && make -j$(nproc) \
    && make install \
    && cd /root \
    && rm -R /root/z3 \
    && conda install z3-solver

COPY quicklisp.lisp quicklisp.lisp
COPY quicklisp quicklisp/

COPY acl2-kernel acl2-kernel

ENV ACL2_HOME=/home/acl2
ENV ACL2_SYSTEM_BOOKS="${ACL2_HOME}/books"

RUN wget "https://api.github.com/repos/acl2/acl2/zipball/${ACL2_COMMIT}" -O /tmp/acl2.zip -q

RUN unzip -qq /tmp/acl2.zip -d /tmp/acl2_extract \
    && mv -T /tmp/acl2_extract/$(ls /tmp/acl2_extract) /tmp/acl2 \
    && mv -T /tmp/acl2 ${ACL2_HOME} \
    && rmdir /tmp/acl2_extract \
    && rm /tmp/acl2.zip

RUN chown -R ${USER}:users ${HOME} ${ACL2_HOME}

# Needed for books/oslib/tests/copy to certify
RUN touch ${ACL2_HOME}/../foo && chmod a-w ${ACL2_HOME}/../foo && chown ${USER}:users ${ACL2_HOME}/../foo

ENV PATH="/opt/acl2/bin:${PATH}"
ENV ACL2="/opt/acl2/bin/saved_acl2"

RUN mkdir -p /opt/acl2/bin \
    && ln -s ${ACL2_HOME}/saved_acl2 /opt/acl2/bin/acl2 \
    && ln -s ${ACL2_HOME}/saved_acl2 /opt/acl2/bin/saved_acl2 \
    && ln -s ${ACL2_HOME}/books/build/cert.pl /opt/acl2/bin/cert.pl \
    && ln -s ${ACL2_HOME}/books/build/clean.pl /opt/acl2/bin/clean.pl \
    && ln -s ${ACL2_HOME}/books/build/critpath.pl /opt/acl2/bin/critpath.pl

USER ${USER}

RUN sbcl --non-interactive --load quicklisp.lisp \
      --eval "(quicklisp-quickstart:install)" --eval "(ql-util:without-prompting (ql:add-to-init-file))" \
      --eval "(ql:quickload '(:common-lisp-jupyter :cytoscape-clj :kekule-clj :resizable-box-clj :ngl-clj :delta-vega))" \
      --eval "(clj:install :implementation t)"

ENV QUICKLISP=1

RUN cd ${ACL2_HOME} && (make LISP="sbcl" $ACL2_BUILD_OPTS || (tail -500 make.log && false))

RUN cd ${ACL2_HOME}/books \
    && make ACL2=${ACL2_HOME}/saved_acl2 ${ACL2_CERTIFY_OPTS} ${ACL2_CERTIFY_TARGETS} \
       >make-books.stdout.log 2> >(tee make-books.stderr.log >&2) ; \
    find * -type f -name "*.cert.out" | tar -czvf make-books-cert-out.tar.gz -T -

RUN cd acl2-kernel \
    && pipx install poetry \
    && ~/.local/bin/poetry build \
    && pip install --no-cache ./dist/acl2_kernel-*.whl \
    && rm ./dist/acl2_kernel-*.whl \
    && python3 -m acl2_kernel.install --acl2="${ACL2}"

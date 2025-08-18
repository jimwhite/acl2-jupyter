ARG BASE_IMAGE=quay.io/jupyter/pyspark-notebook:latest

FROM ${BASE_IMAGE}
LABEL org.opencontainers.image.source="https://github.com/jimwhite/acl2-jupyter"

ARG SBCL_VERSION=2.5.7
ARG SBCL_SHA256=c4fafeb795699d5bcff9085091acc762dcf5e55f85235625f3d7aef12c89d1d3

ARG USER=jovyan
ENV HOME=/home/${USER}


# https://github.com/yitzchak/archlinux-cl/blob/main/Dockerfile
# https://yitzchak.github.io/common-lisp-jupyter/install
# https://github.com/yitzchak/common-lisp-jupyter/blob/2df55291592943851d013c66af920e7c150b1de2/Dockerfile#L5C8-L5C43

# mkdir -p context/quicklisp/local-projects

# sha256 of quicklisp.lisp = 4a7a5c2aebe0716417047854267397e24a44d0cce096127411e9ce9ccfeb2c17
# wget -kL -P context https://beta.quicklisp.org/quicklisp.lisp

# git submodule add https://github.com/yitzchak/archlinux-cl.git context/archlinux-cl
# git submodule add https://github.com/yitzchak/common-lisp-jupyter.git context/quicklisp/local-projects/common-lisp-jupyter
# git submodule add https://github.com/yitzchak/delta-vega.git context/quicklisp/local-projects/delta-vega
# git submodule add https://github.com/yitzchak/resizable-box-clj.git context/quicklisp/local-projects/resizable-box-clj
# git submodule add https://github.com/yitzchak/ngl-clj.git context/quicklisp/local-projects/ngl-clj
    

USER root

# This will have RW permission for the ACL2 directory.
RUN echo 'jovyan ALL=(ALL) NOPASSWD: ALL' >> /etc/sudoers && \
    adduser jovyan sudo && \
    groupadd acl2 && \
    usermod -aG acl2 ${USER} && \
    mkdir /opt/acl2 && \
    chown -R ${USER}:acl2 /opt/acl2
    # && chmod -R g+rx /opt/acl2

# Based on https://github.com/wshito/roswell-base

# openssl-dev is needed for Quicklisp
# perl is needed for ACL2's certification scripts
# wget is needed for downloading some files while building the docker image
# The rest are needed for Roswell

# libczmq-dev because otherwise loading quicklisp in sbcl gets:
# quicklisp/software/pzmq-20210531-git/grovel__grovel.c:6:10: fatal error: zmq.h: No such file or directory
#    6 | #include <zmq.h>
# https://github.com/yitzchak/common-lisp-jupyter/blob/2df55291592943851d013c66af920e7c150b1de2/docs/install.md?plain=1#L18

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
        rlwrap \
        retry \
        sbcl \
    && rm -rf /var/lib/apt/lists/* # remove cached apt files

# This /root/sbcl dir seems to be a tmp so why in /root?
RUN mkdir /root/sbcl \
    && cd /root/sbcl \
    && wget "http://prdownloads.sourceforge.net/sbcl/sbcl-${SBCL_VERSION}-source.tar.bz2?download" -O sbcl.tar.bz2 -q \
    && echo "${SBCL_SHA256} sbcl.tar.bz2" > sbcl.tar.bz2.sha256 \
    && sha256sum -c sbcl.tar.bz2.sha256 \
    && rm sbcl.tar.bz2.sha256 \
    && tar -xjf sbcl.tar.bz2 \
    && rm sbcl.tar.bz2 \
    && cd sbcl-* \
    && sh make.sh --without-immobile-space --without-immobile-code --without-compact-instance-header --fancy --dynamic-space-size=4Gb \
    && apt-get remove -y sbcl \
    && sh install.sh \
    && cd /root \
    && rm -R /root/sbcl


COPY archlinux-cl/asdf-add /usr/local/bin/asdf-add
COPY archlinux-cl/make-rc /usr/local/bin/make-rc
COPY archlinux-cl/lisp /usr/local/bin/lisp


ARG ACL2_COMMIT=0
ENV ACL2_SNAPSHOT_INFO="Git commit hash: ${ACL2_COMMIT}"
ARG ACL2_BUILD_OPTS=""
ARG ACL2_CERTIFY_OPTS="-j 6"
ARG ACL2_CERTIFY_TARGETS="basic"
# The ACL2 Bridge and such for Jupyter need everything.
# ARG ACL2_CERTIFY_TARGETS="all acl2s centaur/bridge"
ENV CERT_PL_RM_OUTFILES="1"

ENV ACL2_HOME=/home/acl2

RUN wget "https://api.github.com/repos/acl2/acl2/zipball/${ACL2_COMMIT}" -O /tmp/acl2.zip -q

RUN unzip -qq /tmp/acl2.zip -d /tmp/acl2_extract \
    && mv -T /tmp/acl2_extract/$(ls /tmp/acl2_extract) /tmp/acl2 \
    && mv -T /tmp/acl2 ${ACL2_HOME} \
    && cd ${ACL2_HOME} \
    && make LISP="sbcl" $ACL2_BUILD_OPTS \
    && cd ${ACL2_HOME}/books \
    && make ACL2=${ACL2_HOME}/saved_acl2 ${ACL2_CERTIFY_OPTS} ${ACL2_CERTIFY_TARGETS} \
    && chmod go+rx /home \
    && chmod -R g+rwx ${ACL2_HOME} \
    && chmod g+s ${ACL2_HOME} \
    && chown -R ${USER}:acl2 ${ACL2_HOME} \
    && find ${ACL2_HOME} -type d -print0 | xargs -0 chmod g+s

# Don't remove the acl2 zipball.
# This guards against future inaccessibility and speeds up Docker rebuilds
# && rm /tmp/acl2.zip \
# && rmdir /tmp/acl2_extract \

# # Needed for books/oslib/tests/copy to certify
RUN touch ${ACL2_HOME}/../foo && chmod a-w ${ACL2_HOME}/../foo && chown ${USER}:acl2 ${ACL2_HOME}/../foo

RUN mkdir -p /opt/acl2/bin \
    && ln -s ${ACL2_HOME}/saved_acl2 /opt/acl2/bin/acl2 \
    && ln -s ${ACL2_HOME}/saved_acl2 /opt/acl2/bin/saved_acl2 \
    && ln -s ${ACL2_HOME}/books/build/cert.pl /opt/acl2/bin/cert.pl \
    && ln -s ${ACL2_HOME}/books/build/clean.pl /opt/acl2/bin/clean.pl \
    && ln -s ${ACL2_HOME}/books/build/critpath.pl /opt/acl2/bin/critpath.pl

# # Setup tutorial notebooks (if they exist)
# RUN mkdir -p ${HOME}/programming-tutorial
# COPY acl2-notebooks/programming-tutorial/* ${HOME}/programming-tutorial/

COPY quicklisp.lisp quicklisp.lisp
COPY quicklisp quicklisp/

RUN chown -R ${USER}:users ${HOME}

USER ${USER}

# Do we need these XDG vars?
# Yes: https://github.com/yitzchak/common-lisp-jupyter/blob/2df55291592943851d013c66af920e7c150b1de2/src/lab-extension/asdf.lisp#L12
# ... #-(or darwin windows) (uiop:xdg-data-home)))
# ENV XDG_CONFIG_HOME=/root/.config
# ENV XDG_DATA_HOME=/root/.local/share
# ENV XDG_CACHE_HOME=/root/.cache

# Definitely need this stuff:

ENV PATH="/opt/acl2/bin:${PATH}"
ENV ACL2_SYSTEM_BOOKS="${ACL2_HOME}/books"
ENV ACL2="/opt/acl2/bin/saved_acl2"

WORKDIR ${HOME}

RUN sbcl --non-interactive --load quicklisp.lisp \
      --eval "(quicklisp-quickstart:install)" --eval "(ql-util:without-prompting (ql:add-to-init-file))" \
      --eval "(ql:quickload '(:common-lisp-jupyter :cytoscape-clj :kekule-clj :resizable-box-clj :ngl-clj :delta-vega))" \
      --eval "(clj:install :implementation t)"

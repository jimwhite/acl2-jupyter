FROM debian:stable-slim
LABEL org.opencontainers.image.source="https://github.com/mister-walter/acl2-docker"

# This will have RW permission for the ACL2 directory.
RUN groupadd acl2 && usermod -aG acl2 root && exit

# Based on https://github.com/wshito/roswell-base

# openssl-dev is needed for Quicklisp
# perl is needed for ACL2's certification scripts
# wget is needed for downloading some files while building the docker image
# The rest are needed for Roswell

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
        curl \
        unzip \
        sbcl \
    && rm -rf /var/lib/apt/lists/* # remove cached apt files

RUN mkdir /root/sbcl \
    && cd /root/sbcl \
    && wget "http://prdownloads.sourceforge.net/sbcl/sbcl-2.4.7-source.tar.bz2?download" -O sbcl.tar.bz2 -q \
    && echo "68544d2503635acd015d534ccc9b2ae9f68996d429b5a9063fd22ff0925011d2  sbcl.tar.bz2" > sbcl.tar.bz2.sha256 \
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

ARG ACL2_COMMIT=0
ENV ACL2_SNAPSHOT_INFO="Git commit hash: ${ACL2_COMMIT}"
ARG ACL2_BUILD_OPTS=""
ARG ACL2_CERTIFY_OPTS="-j 4"
ARG ACL2_CERTIFY_TARGETS="basic"
ENV CERT_PL_RM_OUTFILES="1"

RUN wget "https://api.github.com/repos/acl2/acl2/zipball/${ACL2_COMMIT}" -O /tmp/acl2.zip -q \
    && unzip -qq /tmp/acl2.zip -d /root/acl2_extract \
    && rm /tmp/acl2.zip \
    && mv /root/acl2_extract/$(ls /root/acl2_extract) /root/acl2 \
    && rmdir /root/acl2_extract \
    && cd /root/acl2 \
    && make LISP="sbcl" $ACL2_BUILD_OPTS \
    && cd books \
    && make $ACL2_CERTIFY_TARGETS ACL2=/root/acl2/saved_acl2 $ACL2_CERTIFY_OPTS \
    && chmod go+rx /root \
    && chown -R :acl2 /root/acl2 \
    && chmod -R g+rwx /root/acl2 \
    && chmod g+s /root/acl2 \
    && find /root/acl2 -type d -print0 | xargs -0 chmod g+s

RUN mkdir -p /opt/acl2/bin \
    && ln -s /root/acl2/saved_acl2 /opt/acl2/bin/acl2 \
    && ln -s /root/acl2/books/build/cert.pl /opt/acl2/bin/cert.pl \
    && ln -s /root/acl2/books/build/clean.pl /opt/acl2/bin/clean.pl \
    && ln -s /root/acl2/books/build/critpath.pl /opt/acl2/bin/critpath.pl

ENV PATH="/opt/acl2/bin:${PATH}"
ENV ACL2_SYSTEM_BOOKS="/root/acl2/books"
ENV ACL2="/root/acl2/saved_acl2"

CMD ["/root/acl2/saved_acl2"]

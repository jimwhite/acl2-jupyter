FROM debian:stable-slim

# Based on https://github.com/wshito/roswell-base

# openssl-dev is needed for Quicklisp
# perl is needed for ACL2's certification scripts
# The rest are needed for Roswell

RUN apt-get update && \
    apt-get install -y --no-install-recommends \
        build-essential \
        git \
        automake \
        autoconf \
        libcurl4-openssl-dev \
        ca-certificates \
        libssl-dev \
        perl \
    && rm -rf /var/lib/apt/lists/* # remove cached apt files

RUN git clone -b release https://github.com/roswell/roswell.git \
    && cd roswell \
    && sh bootstrap \
    && ./configure \
    && make \
    && make install \
    && cd / && rm -rf /tmp/workdir \
    && ros setup

RUN git clone --depth 1 https://github.com/acl2/acl2.git /root/acl2
#RUN git clone --depth 1 -b 8.2 git://github.com/acl2-devel/acl2-devel.git /root/acl2

ARG ACL2_BUILD_OPTS=""
ARG ACL2_CERTIFY_OPTS="-j 4"
ARG ACL2_CERTIFY_TARGETS="basic"

RUN cd /root/acl2 \
    && make LISP="ros run" $ACL2_BUILD_OPTS \
    && cd books \
    && make $ACL2_CERTIFY_TARGETS ACL2=/root/acl2/saved_acl2 $ACL2_CERTIFY_OPTS

RUN apt-get remove -y \
    build-essential \
    git \
    automake \
    autoconf \
    && apt-get autoremove -y

CMD ["/root/acl2/saved_acl2"]

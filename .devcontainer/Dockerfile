# https://qiita.com/tm_tn/items/7f966c38f6f9a3820565

FROM dlang2/dmd-ubuntu

ARG DEBCONF_NOWARNINGS=yes

RUN apt-get update
RUN apt-get install -y --no-install-recommends cmake musl-tools
RUN CC=musl-gcc ldc-build-runtime --dFlags="-w;-mtriple=x86_64-alpine-linux-musl" BUILD_SHARED_LIBS=OFF


FROM dlang2/ldc-ubuntu:1.18.0

ARG DEBCONF_NOWARNINGS=yes

RUN apt-get update
RUN apt-get install -y --no-install-recommends musl-tools git minisat

COPY --from=build /ldc-build-runtime.tmp/lib /dlang/dc/lib-musl
COPY ldc2-musl.conf /dlang/dc/etc/ldc2.conf.2

WORKDIR /dlang/dc/etc
RUN cat ldc2.conf ldc2.conf.2 > ldc2.conf_ && \
    mv ldc2.conf_ ldc2.conf && rm ldc2.conf.2
WORKDIR /
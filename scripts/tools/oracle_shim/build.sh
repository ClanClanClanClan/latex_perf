#!/bin/sh
# Builds lpshim-aarch64.so and lpshim-x86_64.so from lpshim.c (OPEN-128).
# Run from the repository root:
#   docker run --rm --platform linux/arm64 -v "$PWD/scripts/tools/oracle_shim:/s" \
#     ubuntu@sha256:2edbbc5dc405e9612ba3584ce95480277e3eb374407b5505fe26f17df77c7dbc \
#     sh /s/build.sh
# (ubuntu:22.04, the same base and compilers as spike H.2's clockshim-build.sh:
# gcc 11.4.0 and its x86_64 cross compiler). The build is deterministic: no
# timestamps, no build id (-Wl,--build-id=none), a fixed source path (/s).
# _oracle.SHIM_SHA256 pins the two outputs; check_oracle_shim.py checks the
# pin against the committed files, and `--rebuild` rebuilds them here and
# compares bytes.
set -e
apt-get update -qq >/dev/null
apt-get install -y -qq gcc libc6-dev gcc-x86-64-linux-gnu libc6-dev-amd64-cross >/dev/null
cd /s
FLAGS="-O2 -shared -fPIC -Wall -Wextra -Wno-unused-parameter -Wl,--build-id=none -ffile-prefix-map=/s=. -o"
gcc $FLAGS lpshim-aarch64.so lpshim.c -ldl
x86_64-linux-gnu-gcc $FLAGS lpshim-x86_64.so lpshim.c -ldl
gcc --version | head -1
x86_64-linux-gnu-gcc --version | head -1
sha256sum lpshim-aarch64.so lpshim-x86_64.so lpshim.c

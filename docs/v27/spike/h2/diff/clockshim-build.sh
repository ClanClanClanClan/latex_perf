# Builds clockshim-{arm64,amd64}.so from clockshim.c, in an ubuntu:22.04 (arm64) container with
# this directory mounted at /s: docker run --rm --platform linux/arm64 -v $PWD:/s ubuntu:22.04 sh /s/clockshim-build.sh

set -e
apt-get update -qq >/dev/null
apt-get install -y -qq gcc libc6-dev gcc-x86-64-linux-gnu libc6-dev-amd64-cross >/dev/null
cd /s
gcc -O2 -shared -fPIC -o clockshim-arm64.so clockshim.c
x86_64-linux-gnu-gcc -O2 -shared -fPIC -o clockshim-amd64.so clockshim.c
gcc --version | head -1; x86_64-linux-gnu-gcc --version | head -1
sha256sum clockshim*.so clockshim.c

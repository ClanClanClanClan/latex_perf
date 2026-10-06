#!/bin/zsh
# Spike H.5, stage-1 correction (docs/v27/spike/H5-heap-design.md §3.2, C-145).
#
# bintime.sh OUTFILE REPS PREFIX... : the pinned pdfTeX binary's CPU time (user + sys) on meaning-dump
# prefixes, REPS runs per prefix, appended to OUTFILE as one line per run:
#   BIN <prefix> <rep> user <s> sys <s> rc <n> logsize <bytes> logsha <sha256> vmload <1/5/15 min>
# plus a LOAD line (host `uptime` and `memory_pressure`'s free percentage) before and after.
#
# THIS SCRIPT STARTS THE ENGINE OUTSIDE scripts/tools/_oracle.py, ON PURPOSE. It is a timing
# instrument, not a grader: nothing it prints is a verdict, and the byte comparison of model and
# binary stays meancompare.py's (h5/tools/cmp.sh, on the h3/README.md recipe). It bypasses _oracle.py
# because the measurement entry point E7 asks for (an _oracle.py path that runs a pinned binary on a
# given storage and reports its CPU time) is being built on another branch and is not on this one;
# _oracle.py as it stands here writes the job's files to a bind mount on the macOS host (virtiofs),
# and that is exactly the I/O that inflated the first measurement 4-8x (C-145). When E7's entry point
# lands, this script is to be replaced by it, and its numbers re-measured through it.
#
# What makes it fair (C-145): every file the engine writes goes to the container's own storage
# (/tmp inside the container, overlayfs on colima's VM disk), never to the host. The input is copied
# there first. The clock shim fakes the wall clock (TeX reads it), so only user and sys CPU are read.
# The run identity is the h3 meaning-dump recipe's: the same image digest, environment and clock.
setopt err_return
out=$1 reps=$2; shift 2
H5=${H5:-$HOME/.cache/lp-spike-h1/h5}
SHIM=${SHIM:-$HOME/.cache/lp-spike-h1/h2/diff/shim}
IMG=texlive/texlive@sha256:4984977ccf5afe883cb382d0163f267de0d029d140bb7a9e8f4c19f0b781d57b
load() { print -r -- "LOAD $1 $(date +%s) uptime[$(uptime | sed 's/.*load averages*: *//')] mem_free_pct $(memory_pressure 2>/dev/null | awk -F': ' '/free percentage/{print $2}')" >> $out; }
for p in "$@"; do
  [ -f $H5/in/$p/stdin-meanings ] || { echo "no input $p"; return 2; }
  # the spec's clock readings, as the h3 recipe passes them (SEC.USEC,...)
  clock=$(awk '$1 == "clock" {printf "%s%s.%s", (n++ ? "," : ""), $2, $3}' $H5/in/$p/spec)
  load before-$p
  docker run --rm --platform linux/arm64 --network none -v $H5/in/$p:/in:ro -v $SHIM:/shim:ro \
    -e LD_PRELOAD=/shim/clockshim-arm64.so -e LP_CLOCK=$clock -e LP_CLOCK_LOG=/tmp/w/clock.log \
    -e SOURCE_DATE_EPOCH=0 -e FORCE_SOURCE_DATE=1 -e max_print_line=1000000 -e error_line=254 \
    -e half_error_line=238 -e openin_any=p -e openout_any=p -e P=$p -e REPS=$reps $IMG \
    bash -c 'mkdir -p /tmp/w && cp /in/stdin-meanings /tmp/stdin && cd /tmp/w || exit 9
             TIMEFORMAT="%U %S"
             for i in $(seq 1 $REPS); do
               rm -f /tmp/w/*
               t=$( { time pdftex -ini < /tmp/stdin > /tmp/out 2>&1; echo "rc $?" > /tmp/rc; } 2>&1 )
               echo "BIN $P $i user ${t% *} sys ${t#* } $(cat /tmp/rc) logsize $(stat -c %s texput.log) logsha $(sha256sum texput.log | cut -c1-64) vmload $(cut -d" " -f1-3 /proc/loadavg | tr " " /)"
             done' >> $out 2>> $out.err
  load after-$p
done

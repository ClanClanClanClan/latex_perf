#!/bin/zsh
# C-187..C-189 (independent review of 284ef72c, 2026-11-03/04): the commands that produced this directory.
# The B2 tree (dbace323...) at 50 and 250 names, and the review's mutation `mfinish` (mutation.diff: callp_body's
# let-bound `finish` reads st.fp instead of caller_fp, so it captures the caller's state across `exec`) at 50.
P=${0:a:h}/../../../../tools/retention_probe.sh
R=~/.cache/lp-track-C/retprobe-v3; mkdir -p $R
IN=~/.cache/lp-spike-h1/h5/in; B2=~/.cache/lp-spike-h1/h5/b2model/build/ml
# mfinish: a copy of $B2 with mutation.diff applied (patch -p0 Interp.ml < mutation.diff)
for spec in "B2-p50 $B2 p50" "B2-p250 $B2 p250" "mfinish-p50 ~/.cache/lp-track-C/mut/mfinish p50"; do
  set -- ${=spec}
  zsh $P $2 $R/$1 $IN/$3 4000 3600 > $R/$1.log 2>&1; echo "RC=$?" >> $R/$1.log
done
# kill-tests.txt: python3 ${0:a:h}/../../../../tools/b2static_kill.py $B2 ~/.cache/lp-spike-h1/h3/cp2/build/ml

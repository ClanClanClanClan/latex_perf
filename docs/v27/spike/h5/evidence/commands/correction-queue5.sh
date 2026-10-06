#!/bin/zsh
perl -e 'alarm 7200; until (open(F, "<", "~/.cache/lp-spike-h1/h5/queue4.log") && grep { /QUEUE4 DONE/ } <F>) { sleep 15 }' || { echo "queue4 not done"; exit 1; }
echo "START $(date)"
# the deep probe's heap walk needs memory of its own: a tighter GC pacing (o=40) keeps the run under the 4 GB cap
zsh docs/v27/spike/h5/tools/run.sh dB2o40-pall ~/.cache/lp-spike-h1/h5/b2sim/ps-b2sim.exe pall 4000 2400 PS_PROBE=45 PS_PROBE_DEEP=1 OCAMLRUNPARAM=v=0x400,o=40 < /dev/null
echo "QUEUE5 DONE $(date)"

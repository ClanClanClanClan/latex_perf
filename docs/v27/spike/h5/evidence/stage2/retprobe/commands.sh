#!/bin/zsh
# The exact commands that produced the runs in this directory (review hardening, 2026-10-06):
# retention_probe.sh with the deterministic probe schedule (retprobe.ml), on the pre-B2 tree (H.3
# checkpoint 2, 72b2ea79...) and the B2 tree (dbace323...), 50 and 250 names. Each run writes to
# ~/.cache/lp-spike-h1/h5/retprobe2/<name>/ and its log to <name>.log; the committed files are
# copied from there (VERDICT, b2static.txt, probes.txt, probe.sha256, run/verdict, run/load.txt).
R=~/.cache/lp-spike-h1/h5/retprobe2
P=${0:a:h}/../../../tools/retention_probe.sh
for spec in "preB2-p250 $HOME/.cache/lp-spike-h1/h3/cp2/build/ml p250" \
            "B2-p250 $HOME/.cache/lp-spike-h1/h5/b2model/build/ml p250" \
            "preB2-p50 $HOME/.cache/lp-spike-h1/h3/cp2/build/ml p50" \
            "B2-p50 $HOME/.cache/lp-spike-h1/h5/b2model/build/ml p50"; do
  set -- ${=spec}
  zsh $P $2 $R/$1 $HOME/.cache/lp-spike-h1/h5/in/$3 4000 3600 > $R/$1.log 2>&1; echo "RC=$?" >> $R/$1.log
done
echo ALLDONE > $R/ALLDONE

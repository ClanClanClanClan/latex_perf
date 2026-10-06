#!/bin/zsh
# Spike H.5, stage-1 correction (H5-heap-design.md §3.2, C-145): interleaved timing rounds of the
# pinned binary and the model's variants on the SAME name populations.
#
# fairtime.sh TAG ROUNDS BINREPS VARIANTS_FILE PREFIX...
#   VARIANTS_FILE: one variant per line, `NAME EXE CAP_MB TIMEOUT_S [ENV=VAL ...]`.
# For each round, for each prefix: the binary BINREPS times (bintime.sh, container-local storage),
# then each variant once (run.sh, under h3/tools/capped.sh). Every model run is preceded by a LOAD
# line (host uptime, memory_pressure's free percentage). Output: $H5/fair/TAG/{bin.txt,load.log}
# and the runs $H5/runs/TAG<round>-<variant>-<prefix>; fairtable.py makes the table.
# The binary side starts the engine outside _oracle.py: see bintime.sh's header for why.
tag=$1 rounds=$2 breps=$3 vfile=$4; shift 4
H5=${H5:-$HOME/.cache/lp-spike-h1/h5}; T=${0:a:h}
o=$H5/fair/$tag; mkdir -p $o
# the variants are read once, so that no run can consume the list on its stdin
vlines=("${(@f)$(grep -v '^#' $vfile | grep -v '^ *$')}")
load() { print -r -- "LOAD $1 $(date +%s) uptime[$(uptime | sed 's/.*load averages*: *//')] mem_free_pct $(memory_pressure 2>/dev/null | awk -F': ' '/free percentage/{print $2}')" >> $o/load.log; }
for r in $(seq 1 $rounds); do
  for p in "$@"; do
    print "ROUND $r" >> $o/bin.txt
    zsh $T/bintime.sh $o/bin.txt $breps $p
    for line in "${vlines[@]}"; do
      read -r name exe cap to envs <<< "$line"
      load "$tag$r-$name-$p"
      zsh $T/run.sh $tag$r-$name-$p $exe $p $cap $to ${=envs} < /dev/null
      load "end $tag$r-$name-$p $(cat $H5/runs/$tag$r-$name-$p/verdict)"
    done
  done
done
print "FAIRTIME DONE" >> $o/load.log

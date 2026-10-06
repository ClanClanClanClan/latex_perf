#!/bin/zsh
# Spike H.5 stage 1 (docs/v27/spike/H5-heap-design.md). Heavy data: ~/.cache/lp-spike-h1/h5 (in/, runs/).
# run.sh NAME EXE PREFIX CAP_MB TIMEOUT_S [ENV=VAL ...]: one capped model run of a meaning-dump prefix
name=$1 exe=$2 p=$3 cap=$4 to=$5; shift 5
H5=~/.cache/lp-spike-h1/h5; o=$H5/runs/$name; rm -rf $o; mkdir -p $o/dump
sysctl -n vm.loadavg > $o/load.txt
env "$@" PS_DUMPDIR=$o/dump PS_PROCNAMES=$H5/../h3/cp2/procnames.txt zsh ${0:a:h}/../../h3/tools/capped.sh $cap $to $o \
  $exe 4000000000 $H5/in/$p/spec $H5/in/$p/stdin-meanings
sysctl -n vm.loadavg >> $o/load.txt
cat $o/verdict

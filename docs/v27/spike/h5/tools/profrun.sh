#!/bin/zsh
# Spike H.5, stage-1 correction (H5-heap-design.md §3.4): a capped model run profiled by macOS `sample`.
# profrun.sh NAME EXE PREFIX "T1 T2 ..." SECS [ENV=VAL ...]
#   run.sh NAME (cap 4000 MB) with EXE behind a wrapper that records the model's own PID, then, at
#   each wall-clock offset Ti (s) from the start, `sample PID SECS 1` into $H5/sample/NAME-tTi.txt.
# The PID comes from the wrapper's pidfile, never from a process-name search.
name=$1 exe=$2 p=$3 offs=$4 secs=$5; shift 5
H5=${H5:-$HOME/.cache/lp-spike-h1/h5}; T=${0:a:h}
pf=$H5/runs/$name.pid; rm -f $pf; mkdir -p $H5/sample
w=$H5/runs/$name.wrap; print -r -- "#!/bin/zsh
echo \$\$ > $pf; exec $exe \"\$@\"" > $w; chmod +x $w
zsh $T/run.sh $name $w $p 4000 2400 "$@" < /dev/null &
rp=$!
perl -e 'alarm 60; until (-s $ARGV[0]) { select undef, undef, undef, 0.05 }' $pf || { echo "no pid"; wait $rp; exit 1; }
pid=$(cat $pf); t0=$(date +%s)
for t in ${=offs}; do
  while [ $(( $(date +%s) - t0 )) -lt $t ]; do kill -0 $pid 2>/dev/null || break 2; sleep 0.2; done
  kill -0 $pid 2>/dev/null || break
  sample $pid $secs 1 -mayDie -file $H5/sample/$name-t$t.txt > /dev/null 2>&1
done
wait $rp

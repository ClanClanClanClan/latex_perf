#!/bin/zsh
# capped.sh CAP_MB TIMEOUT_S OUTDIR cmd...: run cmd with a resident-memory cap and a wall-clock
# timeout (macOS has no working RLIMIT_AS for OCaml 5, so the footprint is polled); writes
# OUTDIR/rss.tsv (elapsed s, footprint MB) and OUTDIR/verdict (finished rc N | killed: rss | killed: time)
cap=$1; to=$2; out=$3; shift 3
mkdir -p $out; : > $out/rss.tsv
"$@" > $out/stdout 2> $out/stderr & pid=$!
t0=$(date +%s); peak=0
while kill -0 $pid 2>/dev/null; do
  # top's MEM is the physical footprint: resident plus compressed and swapped pages (ps's RSS
  # drops when the system pages the process out, so it cannot cap a process under pressure)
  # the whole process tree: a wrapper (/usr/bin/time, env, a shell) between this script and the
  # measured program must not hide the program's footprint (C-144: a cap on /usr/bin/time's own
  # footprint read 0 MB while the model under it used 3.3 GB)
  pids=($pid); i=1
  while [ $i -le ${#pids} ]; do pids+=($(ps -axo pid=,ppid= | awk -v p=${pids[$i]} '$2 == p {print $1}')); i=$((i+1)); done
  mb=0; got=0
  for q in $pids; do
    m=$(top -l 1 -pid $q -stats mem 2>/dev/null | tail -1 | tr -d ' +-')
    [ -z "$m" ] && continue
    got=1
    mb=$(( mb + $(print -r -- $m | awk '/G$/{printf "%d", $0*1024; next} /M$/{printf "%d", $0; next} /K$/{printf "%d", $0/1024; next} {print 0}') ))
  done
  # no reading (top failed, or the process just ended): poll again; never stop capping
  if [ $got -eq 0 ]; then sleep 0.5; continue; fi
  [ $mb -gt $peak ] && peak=$mb
  el=$(( $(date +%s) - t0 )); print "$el\t$mb" >> $out/rss.tsv
  # a kill takes the whole tree this script started (the wrapper and the program under it)
  if [ $mb -gt $cap ]; then kill -9 $pids 2>/dev/null; wait $pid 2>/dev/null; echo "killed: rss ${mb}MB > ${cap}MB at ${el}s" > $out/verdict; exit 0; fi
  if [ $el -gt $to ]; then kill -9 $pids 2>/dev/null; wait $pid 2>/dev/null; echo "killed: time ${el}s, rss ${mb}MB" > $out/verdict; exit 0; fi
  sleep 0.5
done
wait $pid; echo "finished rc $? peak ${peak}MB in $(( $(date +%s) - t0 ))s" > $out/verdict

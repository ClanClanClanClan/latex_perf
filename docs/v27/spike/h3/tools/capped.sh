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
  m=$(top -l 1 -pid $pid -stats mem 2>/dev/null | tail -1 | tr -d ' +-'); [ -z "$m" ] && break
  mb=$(print -r -- $m | awk '/G$/{printf "%d", $0*1024; next} /M$/{printf "%d", $0; next} /K$/{printf "%d", $0/1024; next} {print 0}')
  [ $mb -gt $peak ] && peak=$mb
  el=$(( $(date +%s) - t0 )); print "$el\t$mb" >> $out/rss.tsv
  if [ $mb -gt $cap ]; then kill -9 $pid; wait $pid 2>/dev/null; echo "killed: rss ${mb}MB > ${cap}MB at ${el}s" > $out/verdict; exit 0; fi
  if [ $el -gt $to ]; then kill -9 $pid; wait $pid 2>/dev/null; echo "killed: time ${el}s, rss ${mb}MB" > $out/verdict; exit 0; fi
  sleep 0.5
done
wait $pid; echo "finished rc $? peak ${peak}MB in $(( $(date +%s) - t0 ))s" > $out/verdict

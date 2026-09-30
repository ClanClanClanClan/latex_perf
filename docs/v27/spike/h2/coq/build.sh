#!/bin/zsh
cd ${0:a:h}
export PATH=$HOME/.opam/l0-testing/bin:$PATH
t0=$(date +%s)
for f in Syntax.v ProgGlobals.v Prog_*.v(n) Prog.v; do
  /usr/bin/time -l coqc -Q . PS $f > log.$f.txt 2>&1; rc=$?
  rss=$(grep 'maximum resident' log.$f.txt | awk '{print $1}')
  real=$(grep ' real ' log.$f.txt | awk '{print $1}')
  echo "$f rc=$rc real=${real}s maxrss=$((rss/1048576))MB"
done
echo "TOTAL $(( $(date +%s)-t0 ))s"

#!/bin/sh
# The recorded protocol (_oracle.run_to_fixpoint): up to 3 passes to the
# first rc 0, then one confirming pass; the verdict is the last pass's rc.
# Each witness runs in its own fresh directory.
for f in h1-multipass h2-thepage h2-thepage-body h2-label m2-catcode m2-recut; do
  d=/tmp/w/$f; mkdir -p $d; cp /w/$f.tex $d/; cd $d
  n=0; rc=1
  while [ $n -lt 3 ]; do
    n=$((n+1)); pdflatex -interaction=nonstopmode -halt-on-error $f.tex >/dev/null 2>&1; rc=$?
    echo "$f pass $n rc $rc  first error: $(grep -m1 '^!' $f.log)"
    [ $rc -eq 0 ] && break
  done
  if [ $rc -eq 0 ]; then
    n=$((n+1)); pdflatex -interaction=nonstopmode -halt-on-error $f.tex >/dev/null 2>&1; rc=$?
    echo "$f pass $n rc $rc (confirming)  first error: $(grep -m1 '^!' $f.log)"
  fi
  echo "$f VERDICT rc $rc after $n passes"
  [ -f $f.aux ] && { echo "$f final .aux:"; sed 's/^/    /' $f.aux; }
done

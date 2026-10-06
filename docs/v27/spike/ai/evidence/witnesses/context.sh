#!/bin/sh
# Pass 1 of each witness, with the error's context lines from the log.
for f in h2-thepage h2-thepage-body h2-label m2-catcode m2-recut; do
  d=/tmp/c/$f; mkdir -p $d; cp /w/$f.tex $d/; cd $d
  pdflatex -interaction=nonstopmode -halt-on-error $f.tex >/dev/null 2>&1; rc=$?
  echo "== $f pass 1 rc $rc"
  sed -n '/^!/,/^Here is how much/p' $f.log | head -12 | sed 's/^/    /'
done

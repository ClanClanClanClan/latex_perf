#!/bin/zsh
# Spike H.2 end to end: translate -> Coq (per file, timed) -> extract -> OCaml -> ps.exe
# Everything is written under $OUT (default ~/.cache/lp-spike-h1/h2/run); nothing in the repo.
# Measurements: $OUT/measure.tsv (one row per stage and file: wall s, user s, peak RSS MB,
# the 1-minute load average when the step started), and $OUT/provenance.json (sha256 of
# every input, every committed source, every generated file, and ps.exe). Commit both with
# `provenance.py record` (into evidence/build/) when they back a number in the report.
set -u
H2=${0:a:h}
SRC=${SRC:-$HOME/.cache/lp-spike-h1/b-arm64/repo}
OUT=${OUT:-$HOME/.cache/lp-spike-h1/h2/run}
CMAINJ=$H2/evidence/cmain          # the committed gdb measurement is the build input
# the opam switch with the pinned tools (coqc 8.18.0, OCaml 5.2.0: provenance.json records both)
SWITCH=${OPAM_SWITCH:-l0-testing}
[ -d $HOME/.opam/$SWITCH/bin ] && export PATH=$HOME/.opam/$SWITCH/bin:$PATH
eval $(opam env --switch=$SWITCH 2>/dev/null)
mkdir -p "$OUT/gen" "$OUT/build"
M=$OUT/measure.tsv
print -r -- $'stage\tfile\trc\twall_s\tuser_s\tmaxrss_mb\tload1' > $M
# macOS (BSD time -l, sysctl) or Linux (GNU time -f, /proc/loadavg): the same four numbers
if [[ $OSTYPE == darwin* ]]; then
  load1() { sysctl -n vm.loadavg | awk '{print $2}' }
else
  load1() { awk '{print $1}' /proc/loadavg }
fi
# timed STAGE FILE LOG cmd...: run under /usr/bin/time, append a row to measure.tsv
timed() {
  local stage=$1 file=$2 log=$3; shift 3
  local l=$(load1) rss real user rc
  if [[ $OSTYPE == darwin* ]]; then
    /usr/bin/time -l "$@" > $log 2>&1; rc=$?
    rss=$(grep 'maximum resident' $log | awk '{print $1}')       # bytes
    real=$(grep ' real ' $log | awk '{print $1}') user=$(grep ' real ' $log | awk '{print $3}')
  else
    /usr/bin/time -f 'LPTIME %e %U %M' "$@" > $log 2>&1; rc=$?
    rss=$(( $(grep '^LPTIME ' $log | tail -1 | awk '{print $4}') * 1024 ))   # GNU %M is KiB
    real=$(grep '^LPTIME ' $log | tail -1 | awk '{print $2}') user=$(grep '^LPTIME ' $log | tail -1 | awk '{print $3}')
  fi
  print -r -- "$stage"$'\t'"$file"$'\t'"$rc"$'\t'"$real"$'\t'"$user"$'\t'"$(( ${rss:-0} / 1048576 ))"$'\t'"$l" >> $M
  return $rc
}
W=$SRC/texk/web2c
t0=$(date +%s)
timed translate emit_coq.py $OUT/log.translate.txt python3 $H2/translate/emit_coq.py $SRC/Work/texk/web2c/pdftex.p \
  $W/web2c/common.defines $W/web2c/texmf.defines $W/synctexdir/synctex.defines $W/pdftexdir/pdftex.defines \
  --coerce $SRC/Work/texk/web2c/pdftexcoerce.h --pool $SRC/Work/texk/web2c/pdftex.pool --out "$OUT/gen" \
  || { cat $OUT/log.translate.txt; exit 1; }
python3 $H2/translate/gen_cmain.py "$OUT/gen/manifest.json" $CMAINJ/cmain_globals.json $CMAINJ/cmain_globals2.json \
  $CMAINJ/cmain_globals3.json > "$OUT/gen/CMain.v" || exit 1
cd "$OUT/build" || exit 1
find . -maxdepth 1 -type f \( -name '*.v' -o -name '*.vo*' -o -name '*.glob' -o -name 'log.*' -o -name '*.ml' -o -name '*.mli' \) -delete
cp $H2/coq/*.v "$OUT/gen/"*.v .
for f in Syntax.v Values.v Interp.v ProgGlobals.v PoolData.v Prog_*.v(n) Prog.v Boundary.v CMain.v Main.v Extract.v; do
  stage=coqc; [ $f = Extract.v ] && stage=extraction    # Extract.v's coqc run IS the extraction
  timed $stage $f log.$f.txt coqc -Q . PS $f; rc=$?
  [ $rc -eq 0 ] || { grep -v 'resident\|real\|context\|instructions\|cycles\|footprint\|page\|block\|messages\|signals\|swaps' log.$f.txt | head -20; exit 1; }
done
mkdir -p ml new_ml && find new_ml -type f -delete && mv ./*.ml ./*.mli new_ml/ 2>/dev/null
# the extracted OCaml is compiled as Coq wrote it: no textual patch (see Extract.v)
cp $H2/coq/driver.ml new_ml/
# a module is recompiled if its source changed or a module it depends on was
for f in new_ml/*; do cmp -s $f ml/${f:t} || cp $f ml/${f:t}; done
for f in ml/*.ml(N) ml/*.mli(N); do [ -e new_ml/${f:t} ] || rm -f $f ${f:r}.cmx ${f:r}.cmi ${f:r}.o; done
cd ml
order=($(ocamlfind ocamldep -sort *.ml *.mli))
typeset -A deps; typeset -A redo
while IFS= read -r line; do tgt=${line%%:*}; deps[$tgt]=${line#*:}; done < <(ocamlfind ocamldep -modules *.ml *.mli)
nre=0
for f in $order; do
  base=${f%.*}; out=$base.cmx; [ ${f:e} = mli ] && out=$base.cmi
  need=0
  [ ! -e $out ] && need=1
  [ -e $out ] && [ $f -nt $out ] && need=1
  for m in ${=deps[$f]}; do [ -n "${redo[$m]:-}" ] && need=1; done
  if [ $need -eq 1 ]; then
    redo[${(C)base}]=1; redo[$base]=1; nre=$((nre+1))
    timed ocamlopt $f ../ocaml.$f.log ocamlfind ocamlopt -package zarith,coq-core.kernel,unix -c $f \
      || { echo "ocamlopt $f FAILED"; head -30 ../ocaml.$f.log; exit 1; }
  fi
done
cmx=($(for f in $order; do case $f in *.ml) echo ${f%.ml}.cmx;; esac; done))
timed link ps.exe ../ocaml.link.log ocamlfind ocamlopt -package zarith,coq-core.kernel,unix -linkpkg $cmx -o ../ps.exe || exit 1
echo "recompiled $nre of ${#order} OCaml files"
cd ..
python3 -c "import json;print('\n'.join(json.load(open('$OUT/gen/manifest.json'))['proc_names']))" > $OUT/procnames.txt
echo "TOTAL $(( $(date +%s)-t0 ))s"
python3 $H2/provenance.py write --src "$SRC" --out "$OUT" || exit 1
python3 $H2/provenance.py summary --out "$OUT"

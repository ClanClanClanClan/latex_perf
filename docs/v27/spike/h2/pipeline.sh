#!/bin/zsh
# Spike H.2 end to end: translate -> Coq (per file, timed) -> extract -> OCaml -> ps.exe
# Everything is written under $OUT (default ~/.cache/lp-spike-h1/h2/run); nothing in the repo.
set -u
H2=${0:a:h}
SRC=${SRC:-$HOME/.cache/lp-spike-h1/b-arm64/repo}
OUT=${OUT:-$HOME/.cache/lp-spike-h1/h2/run}
CMAINJ=${CMAINJ:-$HOME/.cache/lp-spike-h1/h2/cmain/w}
export PATH=$HOME/.opam/l0-testing/bin:$PATH
eval $(opam env --switch=l0-testing 2>/dev/null)
mkdir -p "$OUT/gen" "$OUT/build"
W=$SRC/texk/web2c
t0=$(date +%s)
python3 $H2/translate/emit_coq.py $SRC/Work/texk/web2c/pdftex.p $W/web2c/common.defines $W/web2c/texmf.defines \
  $W/synctexdir/synctex.defines $W/pdftexdir/pdftex.defines --coerce $SRC/Work/texk/web2c/pdftexcoerce.h --pool $SRC/Work/texk/web2c/pdftex.pool \
  --out "$OUT/gen" || exit 1
python3 $H2/translate/gen_cmain.py "$OUT/gen/manifest.json" $CMAINJ/cmain_globals.json $CMAINJ/cmain_globals2.json \
  $CMAINJ/cmain_globals3.json > "$OUT/gen/CMain.v" || exit 1
cd "$OUT/build" || exit 1
find . -maxdepth 1 -type f \( -name '*.v' -o -name '*.vo*' -o -name '*.glob' -o -name 'log.*' \) -delete
cp $H2/coq/*.v "$OUT/gen/"*.v .
for f in Syntax.v Values.v Interp.v ProgGlobals.v PoolData.v Prog_*.v(n) Prog.v Boundary.v CMain.v Main.v Extract.v; do
  /usr/bin/time -l coqc -Q . PS $f > log.$f.txt 2>&1; rc=$?
  rss=$(grep 'maximum resident' log.$f.txt | awk '{print $1}')
  real=$(grep ' real ' log.$f.txt | awk '{print $1}')
  echo "coqc $f rc=$rc real=${real}s maxrss=$((rss/1048576))MB"
  [ $rc -eq 0 ] || { grep -v 'resident\|real\|context\|instructions\|cycles\|footprint\|page\|block\|messages\|signals\|swaps' log.$f.txt | head -20; exit 1; }
done
mkdir -p ml new_ml && find new_ml -type f -delete && mv ./*.ml ./*.mli new_ml/ 2>/dev/null
sed -i '' "s/ 'a Parray\.t/ Parray.t/g" new_ml/*.ml new_ml/*.mli   # ExtrOCamlPArray's type-parameter bug (Coq 8.18)
cp $H2/coq/driver.ml new_ml/
# incremental: a module is recompiled if its source changed or a module it depends on was
for f in new_ml/*; do cmp -s $f ml/${f:t} || cp $f ml/${f:t}; done
cd ml
order=($(ocamlfind ocamldep -sort *.ml *.mli))
typeset -A deps; typeset -A redo
while IFS= read -r line; do tgt=${line%%:*}; deps[$tgt]=${line#*:}; done < <(ocamlfind ocamldep -modules *.ml *.mli)
maxrss=0; t1=$(date +%s); nre=0
for f in $order; do
  base=${f%.*}; out=$base.cmx; [ ${f:e} = mli ] && out=$base.cmi
  need=0
  [ ! -e $out ] && need=1
  [ -e $out ] && [ $f -nt $out ] && need=1
  for m in ${=deps[$f]}; do [ -n "${redo[$m]:-}" ] && need=1; done
  if [ $need -eq 1 ]; then
    redo[${(C)base}]=1; redo[$base]=1; nre=$((nre+1))
    /usr/bin/time -l ocamlfind ocamlopt -package zarith,coq-core.kernel,unix -c $f > ../ocaml.$f.log 2>&1 || { echo "ocamlopt $f FAILED"; head -30 ../ocaml.$f.log; exit 1; }
    rss=$(grep 'maximum resident' ../ocaml.$f.log | awk '{print $1}'); [ $rss -gt $maxrss ] && maxrss=$rss
  fi
done
cmx=($(for f in $order; do case $f in *.ml) echo ${f%.ml}.cmx;; esac; done))
ocamlfind ocamlopt -package zarith,coq-core.kernel,unix -linkpkg $cmx -o ../ps.exe > ../ocaml.link.log 2>&1; rc=$?
echo "recompiled $nre of ${#order} OCaml files"
echo "ocamlopt rc=$rc real=$(( $(date +%s)-t1 ))s maxrss(per module)=$((maxrss/1048576))MB ml=$(cat *.ml | wc -c) bytes"
cd ..
python3 -c "import json;print('\n'.join(json.load(open('$OUT/gen/manifest.json'))['proc_names']))" > $OUT/procnames.txt
echo "TOTAL $(( $(date +%s)-t0 ))s"

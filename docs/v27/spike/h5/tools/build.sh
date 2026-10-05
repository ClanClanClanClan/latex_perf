#!/bin/zsh
# Spike H.5 stage 1. build.sh MLDIR OUTEXE: compile an extracted tree (plus driver) in dependency order, as pipeline.sh does
export PATH=$HOME/.opam/l0-testing/bin:$PATH
eval $(opam env --switch=l0-testing 2>/dev/null)
cd $1 || exit 1
rm -f *.cmx *.cmi *.o
order=($(ocamlfind ocamldep -sort *.ml *.mli))
for f in $order; do
  ocamlfind ocamlopt ${=OCFLAGS:-} -package zarith,coq-core.kernel,unix -c $f > /dev/null 2> build.$f.err || { echo "FAIL $f"; head -20 build.$f.err; exit 1; }
done
cmx=($(for f in $order; do case $f in *.ml) echo ${f%.ml}.cmx;; esac; done))
ocamlfind ocamlopt ${=OCFLAGS:-} -package zarith,coq-core.kernel,unix -linkpkg $cmx -o $2 || exit 1
rm -f build.*.err
echo built $2

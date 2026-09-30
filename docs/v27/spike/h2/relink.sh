#!/bin/zsh
# recompile only the driver and relink (after pipeline.sh built the modules)
OUT=${OUT:-$HOME/.cache/lp-spike-h1/h2/run}
eval $(opam env --switch=l0-testing 2>/dev/null)
H2=${0:a:h}; cd $OUT/build/ml && cp $H2/coq/driver.ml . || exit 1
order=($(ocamlfind ocamldep -sort *.ml *.mli))
ocamlfind ocamlopt -package zarith,coq-core.kernel,unix -c driver.ml || exit 1
cmx=($(for f in $order; do case $f in *.ml) echo ${f%.ml}.cmx;; esac; done))
ocamlfind ocamlopt -package zarith,coq-core.kernel,unix -linkpkg $cmx -o ../ps.exe && echo LINKED

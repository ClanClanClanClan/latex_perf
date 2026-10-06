#!/bin/zsh
# Single-member reverts against the DYNAMIC half (review hardening, 2026-10-06). For each of the
# ten fuelled members, a copy of the B2 tree (dbace323...) whose successor closure reads its state
# after its body's call (b2static_kill.py's mutation K-<member>: `let r__k = NAME_body ... in
# ignore (Sys.opaque_identity st); r__k`), so that closure holds the state across the call, as
# before B2, for that member only. retention_probe.sh on 250 names; the static half fails on every one by design;
# the question is which ones the GC probe sees.
R=~/.cache/lp-spike-h1/h5/retprobe2/reverts
export TOOLS=${0:a:h}/../../../../tools
mkdir -p $R
for m in evale evall evalargs evalx callp0 exec for_loop exec_list goto_in write_items; do
  python3 - $m $R/$m-ml <<'PY'
import shutil, sys
from pathlib import Path
sys.path.insert(0, __import__("os").environ["TOOLS"])
import b2static_kill as K
m, d = sys.argv[1], Path(sys.argv[2])
shutil.rmtree(d, ignore_errors=True); d.mkdir(parents=True)
src = Path.home() / ".cache/lp-spike-h1/h5/b2model/build/ml"
for f in list(src.glob("*.ml")) + list(src.glob("*.mli")):
    shutil.copy(f, d / f.name)
K.member_revert(m)(d)
print("mutated", m)
PY
  zsh $TOOLS/retention_probe.sh $R/$m-ml $R/$m $HOME/.cache/lp-spike-h1/h5/in/p250 4000 3600 > $R/$m.log 2>&1; echo "RC=$?" >> $R/$m.log
  rm -rf $R/$m-ml $R/$m/ml $R/$m/probe.exe
done
echo ALLDONE > $R/ALLDONE

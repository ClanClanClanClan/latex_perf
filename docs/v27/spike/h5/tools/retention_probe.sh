#!/bin/zsh
# retention_probe.sh ML_DIR OUT_DIR INPUT_DIR [CAP_MB [TIMEOUT_S [PERIOD_S]]]
#
# The STANDING retention check of B2 (spike H.5 stage 2; H5-heap-design.md §5 B, §6). Two halves:
#   1. static: b2static.py ML_DIR (every fuel-realizer closure is a single call, or allowed);
#      it is recorded, not a stop: the dynamic half runs either way;
#   2. dynamic: a copy of ML_DIR with retprobe.ml around the C boundary (one line of Main0.ml and
#      one of driver.ml, each asserted to match once; nothing else changed, coq-core's Parray
#      unchanged) is built and run on INPUT_DIR (a meaning-dump prefix: spec + stdin-meanings,
#      h5/README.md) under h3/tools/capped.sh. Every PERIOD_S s of CPU a forced full GC measures
#      the words live but not reachable from the current state (retprobe.ml).
# Verdicts (last line, and the exit status):
#   PASS (0)          static OK; the run finished; >= 3 probes; every probe under the limit
#   FAIL (1)          a static failure, or a probe over the limit (the run stops at that probe)
#   INCONCLUSIVE (2)  anything else (killed by the cap or the timeout, too few probes, build failed)
# ML_DIR is an extracted tree (pipeline.sh's build/ml, or build/new_ml). driver.ml is taken from it
# when present, else from h2/coq/driver.ml.
set -u
ml=$1 out=$2 in=$3 cap=${4:-4000} to=${5:-3600} per=${6:-5}
T=${0:a:h}; SPIKE=$T/../..
export PATH=$HOME/.opam/l0-testing/bin:$PATH
eval $(opam env --switch=l0-testing 2>/dev/null)
rm -rf $out; mkdir -p $out/ml $out/run
verdict() { print -r -- "$1"; print -r -- "$1" > $out/VERDICT; exit $2 }
# both halves always run, so that a failing tree shows each half's own verdict
python3 $T/b2static.py $ml > $out/b2static.txt 2>&1; srv=$?
static=$(tail -1 $out/b2static.txt); print -r -- "static: $static"
cp $ml/*.ml $ml/*.mli $out/ml/ 2>/dev/null
[ -e $out/ml/driver.ml ] || cp $SPIKE/h2/coq/driver.ml $out/ml/
cp $T/retprobe.ml $out/ml/
python3 - $out/ml <<'EOF' || verdict "INCONCLUSIVE: the probe could not be inserted" 2
import sys
from pathlib import Path
d = Path(sys.argv[1])
def rep(name, a, b):
    p = d / name; s = p.read_text(); c = s.count(a)
    assert c == 1, (name, a, c)
    p.write_text(s.replace(a, b))
rep("Main0.ml", "callp procs_array nglobals ext fuel", "callp procs_array nglobals Retprobe.ext fuel")
rep("driver.ml", "  let t0 = Unix.gettimeofday () in\n",
    "  Retprobe.static_words := Obj.reachable_words (Obj.repr Main0.procs_array);\n"
    "  let t0 = Unix.gettimeofday () in\n")
rep("driver.ml", '  Printf.printf "TIME: %.2f s\\n" (t1 -. t0)',
    "  (let st = match r with Interp.EOk (_, s) | Interp.EHalt (_, s) | Interp.EStk (_, s) -> s in"
    " Retprobe.probe ~final:true st);\n"
    '  Printf.printf "TIME: %.2f s\\n" (t1 -. t0)')
print("probe inserted: Main0.ml 1 line, driver.ml 2 lines")
EOF
zsh $T/build.sh $out/ml $out/probe.exe > $out/build.txt 2>&1 || { cat $out/build.txt; verdict "INCONCLUSIVE: build failed" 2 }
shasum -a 256 $out/probe.exe > $out/probe.sha256
sysctl -n vm.loadavg > $out/run/load.txt 2>/dev/null || cat /proc/loadavg > $out/run/load.txt
mkdir -p $out/run/dump
PS_RETPROBE_CPU=$per PS_DUMPDIR=$out/run/dump zsh $SPIKE/h3/tools/capped.sh $cap $to $out/run \
  $out/probe.exe 4000000000 $in/spec $in/stdin-meanings
sysctl -n vm.loadavg >> $out/run/load.txt 2>/dev/null || cat /proc/loadavg >> $out/run/load.txt
grep '^RETPROBE' $out/run/stderr > $out/probes.txt
cat $out/probes.txt
v=$(cat $out/run/verdict); n=$(grep -c '^RETPROBE run' $out/probes.txt)
print -r -- "run: $v; $n probes"
grep -q '^RETPROBE FAIL' $out/probes.txt && verdict "FAIL: retention over the limit ($v)$( [ $srv -ne 0 ] && echo '; static FAIL')" 1
[ $srv -eq 0 ] || verdict "FAIL: static ($static); dynamic: $v, $n probes, none over the limit" 1
[[ $v == "finished rc"* ]] || verdict "INCONCLUSIVE: the run did not finish ($v)" 2
[ $n -ge 3 ] || verdict "INCONCLUSIVE: only $n probes" 2
verdict "PASS: $n probes, every one under the limit ($v)" 0

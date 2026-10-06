#!/bin/zsh
# retention_probe.sh ML_DIR OUT_DIR INPUT_DIR [CAP_MB [TIMEOUT_S]]
#
# The STANDING retention check of B2 (spike H.5 stage 2; H5-heap-design.md §5 B, §8.2). Two
# halves, both REQUIRED for a PASS; neither can be skipped, and the dynamic half alone never
# passes:
#   1. static: b2static.py ML_DIR (every continuation closure of every realizer in the tree,
#      typed: it cannot hold a state across a call that can re-enter the interpreter, or it is
#      allowed by a checked argument; and B2's ten members have their structure). It is recorded,
#      not a stop: the dynamic half runs either way, so a failing tree shows both verdicts. If it
#      cannot run (its summary line is missing), the check is INCONCLUSIVE.
#   2. dynamic: a copy of ML_DIR with retprobe.ml around the C boundary (one line of Main0.ml and
#      two of driver.ml, each asserted to match once; nothing else changed, coq-core's Parray
#      unchanged) is built and run on INPUT_DIR (a meaning-dump prefix: spec + stdin-meanings,
#      h5/README.md) under h3/tools/capped.sh. A forced full GC measures the words live but not
#      reachable from the current state at external calls chosen from the program's own call
#      sequence (retprobe.ml: phases init, load, dump; ordinals 1, 4, 16, ... in each; the end of
#      the load): the probes are the same program points on every machine.
# Verdicts (last line, and the exit status):
#   PASS (0)          static PASS; the run finished; the load and the dump each got >= 3 probes;
#                     every probe under the limit
#   FAIL (1)          a static failure, or a probe over the limit (the run stops at that probe)
#   INCONCLUSIVE (2)  anything else (the static half did not run, killed by the cap or the
#                     timeout, a phase not reached or with too few probes, build failed)
# ML_DIR is an extracted tree (pipeline.sh's build/ml, or build/new_ml). driver.ml is taken from it
# when present, else from h2/coq/driver.ml.
set -u
[ $# -ge 3 ] && [ $# -le 5 ] || { print -r -- "usage: retention_probe.sh ML_DIR OUT_DIR INPUT_DIR [CAP_MB [TIMEOUT_S]]"; exit 2 }
ml=$1 out=$2 in=$3 cap=${4:-4000} to=${5:-3600}
MIN=3   # probes required in each of the load and the dump
T=${0:a:h}; SPIKE=$T/../..
export PATH=$HOME/.opam/l0-testing/bin:$PATH
eval $(opam env --switch=l0-testing 2>/dev/null)
rm -rf $out; mkdir -p $out/ml $out/run
verdict() { print -r -- "$1"; print -r -- "$1" > $out/VERDICT; exit $2 }
# both halves always run, so that a failing tree shows each half's own verdict
python3 $T/b2static.py $ml > $out/b2static.txt 2>&1; srv=$?
static=$(tail -1 $out/b2static.txt); print -r -- "static: $static (rc $srv)"
if [[ $static != "b2static: "* ]] || [ $srv -gt 1 ]; then
  verdict "INCONCLUSIVE: the static half did not run (rc $srv): $static" 2
fi
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
PS_RETPROBE=1 PS_DUMPDIR=$out/run/dump zsh $SPIKE/h3/tools/capped.sh $cap $to $out/run \
  $out/probe.exe 4000000000 $in/spec $in/stdin-meanings
sysctl -n vm.loadavg >> $out/run/load.txt 2>/dev/null || cat /proc/loadavg >> $out/run/load.txt
grep '^RETPROBE' $out/run/stderr > $out/probes.txt
cat $out/probes.txt
v=$(cat $out/run/verdict); n=$(grep -c '^RETPROBE run' $out/probes.txt)
ni=$(grep -c '^RETPROBE run .* phase init ' $out/probes.txt)
nl=$(grep -c '^RETPROBE run .* phase load ' $out/probes.txt)
nd=$(grep -c '^RETPROBE run .* phase dump ' $out/probes.txt)
eol=$(grep -c ' end-of-load ' $out/probes.txt)
counts="$n probes: init $ni, load $nl (end of load: $eol), dump $nd"
print -r -- "run: $v; $counts"
grep -q '^RETPROBE FAIL' $out/probes.txt && verdict "FAIL: retention over the limit ($v; $counts)$( [ $srv -ne 0 ] && echo "; static FAIL: $static")" 1
[ $srv -eq 0 ] || verdict "FAIL: static ($static); dynamic: $v, $counts, none over the limit" 1
[[ $v == "finished rc 0 "* ]] || verdict "INCONCLUSIVE: the run did not finish with rc 0 ($v; $counts)" 2
grep -q '^RETPROBE final ' $out/probes.txt || verdict "INCONCLUSIVE: no final probe ($counts)" 2
[ $eol -eq 1 ] && [ $nl -ge $MIN ] && [ $nd -ge $MIN ] || verdict "INCONCLUSIVE: $counts (need the end of the load and >= $MIN probes in each of the load and the dump)" 2
verdict "PASS: static ($static); dynamic: $counts, every one under the limit ($v)" 0

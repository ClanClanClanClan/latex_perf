#!/bin/zsh
# stage-1 correction queue (after the fair rounds): B2 deep probes, B1 at 1,000 names, GC sensitivity, profiles
perl -e 'alarm 7200; until (open(F, "<", "~/.cache/lp-spike-h1/h5/fair/fr/load.log") && grep { /FAIRTIME DONE/ } <F>) { sleep 15 }' || { echo "fair rounds not done"; exit 1; }
echo "START $(date)"
zsh docs/v27/spike/h5/tools/run.sh dB2-pall ~/.cache/lp-spike-h1/h5/b2sim/ps-b2sim.exe pall 4000 2400 PS_PROBE=30 PS_PROBE_DEEP=1 OCAMLRUNPARAM=v=0x400 < /dev/null
zsh docs/v27/spike/h5/tools/run.sh b1o3-p1000 ~/.cache/lp-spike-h1/h5/b1o3/ps-b1o3.exe p1000 4000 900 PS_PROBE=10 OCAMLRUNPARAM=v=0x400 < /dev/null
for r in 1 2 3; do
  zsh docs/v27/spike/h5/tools/run.sh gc${r}-AB2def-p1000 ~/.cache/lp-spike-h1/h5/b2sim/ps-b2sim.exe p1000 4000 900 PS_PROBE=30 PS_PARRAY=linear OCAMLRUNPARAM=v=0x400 < /dev/null
  zsh docs/v27/spike/h5/tools/run.sh gc${r}-AB2s4M-p1000 ~/.cache/lp-spike-h1/h5/b2sim/ps-b2sim.exe p1000 4000 900 PS_PROBE=30 PS_PARRAY=linear OCAMLRUNPARAM=v=0x400,s=4M < /dev/null
  zsh docs/v27/spike/h5/tools/run.sh gc${r}-AB2s4Mo200-p1000 ~/.cache/lp-spike-h1/h5/b2sim/ps-b2sim.exe p1000 4000 900 PS_PROBE=30 PS_PARRAY=linear OCAMLRUNPARAM=v=0x400,s=4M,o=200 < /dev/null
done
zsh docs/v27/spike/h5/tools/profrun.sh prof-AB2-p1000 ~/.cache/lp-spike-h1/h5/b2sim/ps-b2sim.exe p1000 "1" 12 PS_PROBE=30 PS_PARRAY=linear
zsh docs/v27/spike/h5/tools/profrun.sh prof-AB2-pall ~/.cache/lp-spike-h1/h5/b2sim/ps-b2sim.exe pall "20 80 140" 20 PS_PROBE=30 PS_PARRAY=linear
echo "QUEUE4 DONE $(date)"

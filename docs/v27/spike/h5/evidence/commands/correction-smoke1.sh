#!/bin/zsh
zsh docs/v27/spike/h5/tools/run.sh sm-b2-p250 ~/.cache/lp-spike-h1/h5/b2sim/ps-b2sim.exe p250 4000 900 PS_PROBE=10 OCAMLRUNPARAM=v=0x400
zsh docs/v27/spike/h5/tools/run.sh sm-b1o3-p250 ~/.cache/lp-spike-h1/h5/b1o3/ps-b1o3.exe p250 4000 900 PS_PROBE=10 OCAMLRUNPARAM=v=0x400
echo SMOKE DONE

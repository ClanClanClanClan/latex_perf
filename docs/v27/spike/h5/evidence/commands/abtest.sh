#!/bin/zsh
# interleaved A/B rounds: the same inputs, the variants in turn, so that the machine's load affects each alike
H5=~/.cache/lp-spike-h1/h5; cd $H5
for round in 1 2 3; do
  zsh tools/run.sh ab$round-pers-p250 $H5/prof/ps-prof.exe p250 6000 1500 PS_PROBE=30
  zsh tools/run.sh ab$round-lin-p250 $H5/prof/ps-prof.exe p250 6000 1500 PS_PROBE=30 PS_PARRAY=linear
  zsh tools/run.sh ab$round-t1-p250 $H5/prof-t1/ps-t1.exe p250 6000 1500 PS_PROBE=30
  zsh tools/run.sh ab$round-t1lin-p250 $H5/prof-t1/ps-t1.exe p250 6000 1500 PS_PROBE=30 PS_PARRAY=linear
  zsh tools/run.sh ab$round-t2lin-p250 $H5/prof-t2/ps-t2.exe p250 6000 1500 PS_PROBE=30 PS_PARRAY=linear
done
for round in 1 2; do
  for p in p0 p1000; do
    zsh tools/run.sh ab$round-pers-$p $H5/prof/ps-prof.exe $p 9000 2400 PS_PROBE=30
    zsh tools/run.sh ab$round-t2lin-$p $H5/prof-t2/ps-t2.exe $p 6000 2400 PS_PROBE=30 PS_PARRAY=linear
  done
done
echo ABTEST DONE

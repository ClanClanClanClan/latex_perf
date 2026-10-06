#!/bin/zsh
H5=~/.cache/lp-spike-h1/h5; cd $H5
zsh tools/run.sh t2lin-p250-check $H5/prof-t2/ps-t2.exe p250 6000 1500 PS_PROBE=20 PS_PARRAY=linear PS_T1CHECK=1 OCAMLRUNPARAM=v=0x400
zsh tools/run.sh t2lin-p0 $H5/prof-t2/ps-t2.exe p0 6000 1500 PS_PROBE=20 PS_PARRAY=linear OCAMLRUNPARAM=v=0x400
zsh tools/run.sh t2lin-p250 $H5/prof-t2/ps-t2.exe p250 6000 1500 PS_PROBE=20 PS_PARRAY=linear OCAMLRUNPARAM=v=0x400
zsh tools/run.sh t2lin-p1000 $H5/prof-t2/ps-t2.exe p1000 6000 2400 PS_PROBE=20 PS_PARRAY=linear OCAMLRUNPARAM=v=0x400
for r in t2lin-p250-check t2lin-p250; do zsh tools/cmp.sh $r p250; done; zsh tools/cmp.sh t2lin-p1000 p1000
echo QUEUE2 DONE

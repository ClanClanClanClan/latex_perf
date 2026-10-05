#!/bin/zsh
H5=~/.cache/lp-spike-h1/h5; cd $H5
zsh tools/run.sh t2lin-pall-deep $H5/prof-t2/ps-t2.exe pall 4500 3600 PS_PROBE=60 PS_PROBE_DEEP=1 PS_PARRAY=linear OCAMLRUNPARAM=v=0x400
zsh tools/run.sh prof-p0-pers $H5/prof/ps-prof.exe p0 6000 1500 PS_PROBE=20 OCAMLRUNPARAM=v=0x400
zsh tools/run.sh prof-p1000-pers $H5/prof/ps-prof.exe p1000 9000 2400 PS_PROBE=20 OCAMLRUNPARAM=v=0x400
zsh tools/cmp.sh prof-p1000-pers p1000
echo QUEUE3 DONE

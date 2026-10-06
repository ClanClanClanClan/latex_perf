#!/bin/zsh
H5=~/.cache/lp-spike-h1/h5; cd $H5
zsh tools/run.sh t1lin-p250-check $H5/prof-t1/ps-t1.exe p250 6000 1500 PS_PROBE=20 PS_PARRAY=linear PS_T1CHECK=1 OCAMLRUNPARAM=v=0x400
zsh tools/run.sh t1lin-p250 $H5/prof-t1/ps-t1.exe p250 6000 1500 PS_PROBE=20 PS_PARRAY=linear OCAMLRUNPARAM=v=0x400
zsh tools/run.sh t1-p250 $H5/prof-t1/ps-t1.exe p250 6000 1500 PS_PROBE=20 OCAMLRUNPARAM=v=0x400
zsh tools/run.sh lin-p1000-deep $H5/prof/ps-prof.exe p1000 6000 2400 PS_PROBE=60 PS_PROBE_DEEP=1 PS_PARRAY=linear OCAMLRUNPARAM=v=0x400
zsh tools/run.sh t1lin-p1000 $H5/prof-t1/ps-t1.exe p1000 6000 2400 PS_PROBE=20 PS_PARRAY=linear OCAMLRUNPARAM=v=0x400
zsh tools/run.sh t1lin-p0 $H5/prof-t1/ps-t1.exe p0 6000 1500 PS_PROBE=20 PS_PARRAY=linear OCAMLRUNPARAM=v=0x400
for r in t1lin-p250-check t1lin-p250 t1-p250; do echo "== $r"; diff -r runs/base-p250/dump runs/$r/dump && echo DUMP-IDENTICAL; diff <(grep -av '^TIME' runs/base-p250/stdout) <(grep -av '^TIME' runs/$r/stdout) > /dev/null && echo STDOUT-IDENTICAL; done
echo QUEUE1 DONE

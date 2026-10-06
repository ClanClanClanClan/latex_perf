The command lines of every run in H5-heap-design.md, as executed (paths under ~/.cache/lp-spike-h1/h5).
Runs started one at a time by hand (same run.sh):
  run.sh prof-p50-deep  prof/ps-prof.exe p50 7000 1200 PS_PROBE=5  PS_PROBE_DEEP=1   (stopped by hand: probe-bound; kept as prof-p50-deep-probe5-aborted)
  run.sh prof-p50-deep  prof/ps-prof.exe p50 7000 1500 PS_PROBE=15 PS_PROBE_DEEP=1   (stopped by hand: probe-bound; kept as prof-p50-deep-probe15-aborted)
  run.sh base-p250      ~/.cache/lp-spike-h1/h3/cp2/build/ps.exe p250 8000 1200 OCAMLRUNPARAM=v=0x400
  run.sh prof-p250-pers prof/ps-prof.exe p250 8000 1500 PS_PROBE=20 OCAMLRUNPARAM=v=0x400
  run.sh prof-p250-lin  prof/ps-prof.exe p250 8000 1500 PS_PROBE=20 PS_PARRAY=linear OCAMLRUNPARAM=v=0x400
  run.sh t2lin-pall     prof-t2/ps-t2.exe pall 4000 3600 PS_PROBE=30 PS_PARRAY=linear OCAMLRUNPARAM=v=0x400
  run.sh t2lin-p250-memdiag prof-t2/ps-t2.exe p250 3000 900 PS_PARRAY=linear PS_MEMDIAG=1
The others: queue1.sh, queue2.sh, queue3.sh, abtest.sh (this directory). The first p50 run (probe5) used run.sh's
first version, which wrapped the model in /usr/bin/time -l (C-144); every other run used the committed run.sh,
whose direct child is the model, so the cap watched the model even before capped.sh learned to watch the tree.
Profiles: `sample PID 15|20 -file F` on base-p250 (load at t~20 s; later at t~110 s), t1lin-p1000 (t~5 s),
t2lin-pall (t~40 s); grouped with selfprof.py and callers.py.
queue1.log: "Only in runs/base-p250/dump: driver.out" and the TIME-line diff are artefacts of cmp.sh having
copied ps.exe's stdout into base-p250's dump directory between the runs; the handle files themselves compared
equal (no other diff line), and stdout compared equal apart from its TIME line.
queue2.log's first line ("capped.sh:23: parse error near `fi'") was printed while the first run of queue2
(t2lin-p250-check) was in progress: I replaced ~/.cache/lp-spike-h1/h5/tools/capped.sh with the tree-capping
version during that run, and zsh reads a script incrementally. The run's verdict and footprint trace were still
written (probes/t2lin-p250-check/), its output compares IDENTICAL (compare/t2lin-p250-check.json), and every later
run used the new capped.sh from its start.

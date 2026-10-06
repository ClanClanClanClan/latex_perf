The 2026-10-06 correction (C-145, C-146), in the order run (H5 = ~/.cache/lp-spike-h1/h5; paths relative to the repository):
1. B1 build:  OCFLAGS=-O3 zsh docs/v27/spike/h3/tools/capped.sh 4000 2400 $H5/b1o3/buildrun zsh docs/v27/spike/h5/tools/build.sh $H5/b1o3/ml $H5/b1o3/ps-b1o3.exe   ($H5/b1o3/ml = a copy of the *.ml, *.mli of $H5/prof-t2/ml)
2. B2 build:  python3 docs/v27/spike/h5/tools/b2sim.py $H5/prof-t2/ml $H5/b2sim/ml; zsh docs/v27/spike/h3/tools/capped.sh 4000 2400 $H5/b2sim/buildrun zsh docs/v27/spike/h5/tools/build.sh $H5/b2sim/ml $H5/b2sim/ps-b2sim.exe
3. correction-smoke1.sh (B2 and B1 at 250 names), then zsh docs/v27/spike/h5/tools/cmp.sh sm-b2-p250 p250 (and sm-b1o3-p250)
4. The fair rounds:  zsh docs/v27/spike/h5/tools/fairtime.sh fr 3 3 $H5/fair/fr.variants p0 p250 p1000 pall   (variants: ../fair/fr.variants)
5. correction-queue4.sh (B2 deep probes, B1 at 1,000 names, GC sensitivity, the AB2 profiles), correction-queue5.sh (B2 deep probes with o=40)
6. meancompare: zsh docs/v27/spike/h5/tools/cmp.sh fr1-{A,B2,AB2}-{p1000,pall} {p1000,pall}
7. Tables: python3 docs/v27/spike/h5/tools/fairtable.py docs/v27/spike/h5/evidence/fair docs/v27/spike/h5/evidence/fair/runs fr; python3 docs/v27/spike/h5/tools/costclass.py $H5/sample/prof-AB2-*.txt
8. zbench: ocamlfind ocamlopt -package zarith -linkpkg docs/v27/spike/h5/tools/zbench.ml -o zbench.exe; ./zbench.exe (3 runs: ../zbench.txt)

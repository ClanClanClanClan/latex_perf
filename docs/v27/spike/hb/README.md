# Boundary step: measurements on the reference build

Report: [`../H-boundary-report.md`](../H-boundary-report.md). The model's code is in `../h2/`
(`../h2/coq/KTypes.v`, `../h2/coq/Kpse.v`, `../h2/coq/Boundary.v`, `../h2/translate/evalorder.py`), the differential in
`../h2/diff/`.

Every gdb measurement here runs the unstripped reference build (sha256 `b23c26d6…`, whose
stripped form is the pinned arm64 binary; `../h2/evidence/cmain/README.md`) in the pinned image
plus Debian's gdb (`lp-spike-gdb:arm64`). It starts the engine outside `_oracle.py`, which this
repository's `check_oracle_pin.py` allows only there, so each recipe is documentation, quoted
below, not a committed script.

| file | what it is |
|---|---|
| `kpse-measure.gdb`, `kpse-measure.out` | at `mainbody` of `pdftex -ini`: `kpathsea_var_value` of the variables the file search reads, then `kpathsea_init_format` and `kpse_format_info` for formats 3 (tfm), 9 (ls-R), 10 (fmt), 11 (map), 26 (tex), 33 (vf). Checkpoint 1's `kfmt` lines and three `kpse` lines of `../h2/diff/base.spec` are this output. `kpsewhich -show-path` in the image gives the same six paths, and the same output on the amd64 image |
| `kpse-trace.gdb`, `kpse-trace.stdin`, `kpse-trace.out` | the binary's own kpathsea calls (`kpathsea_find_file_generic`, `kpathsea_path_search_list_generic`, `kpathsea_db_search_list`, `kpathsea_readable_file`, `kpathsea_dir_p`, `opendir`) on an INITEX run: `\input foo`, `\openin1=bar`, `\font\f=cmr10`, `\input nofile`. The model makes the same searches. It is a record of what C does, not an input of the model |
| `case-sensitivity.txt` | the container's tmpfs is case-sensitive, a macOS bind mount is not (C-161) |

**Recipes** (REF: the reference build's directory; W: this directory's files):

```sh
# kpse-measure.out
docker run --rm --platform linux/arm64 --network none -v REF:/usr/local/texlive/2026/bin/ref:ro -v W:/in \
  lp-spike-gdb:arm64 sh -c 'mkdir -p /tmp/w && cd /tmp/w && SOURCE_DATE_EPOCH=1788076260 FORCE_SOURCE_DATE=1 \
  gdb -batch -nx -x /in/kpse-measure.gdb --args /usr/local/texlive/2026/bin/ref/pdftex -ini < /dev/null'
# kpse-trace.out (foo.tex: "hello from foo\n\message{FOO}\n", bar.tex: "bar line one\nbar line two\n")
docker run --rm --platform linux/arm64 --network none -v REF:/usr/local/texlive/2026/bin/ref:ro -v W:/in \
  lp-spike-gdb:arm64 sh -c 'mkdir -p /tmp/w && cp /in/foo.tex /in/bar.tex /tmp/w/ && cd /tmp/w && \
  SOURCE_DATE_EPOCH=1788076260 FORCE_SOURCE_DATE=1 gdb -batch -nx -x /in/kpse-trace.gdb \
  --args /usr/local/texlive/2026/bin/ref/pdftex -ini < /in/kpse-trace.stdin'
```

**Checkpoint 3: C main on seven command lines** (`dump3.py`; output summarised in `cmain-seven.txt`; the six `kpse_var_value`/`kpse_format_info` readings for `pdftex -ini` and the graded `pdflatex` command line in `kpse-pdftex.txt`, `kpse-pdflatex.txt`, by `kpse-measure2.py`). The run script, `cmain-run.sh` (mount REF and this directory at /m):

```sh
# measure C main for several command lines (spike boundary step, checkpoint 3)
set -u
mkdir -p /tmp/b && ln -sf /usr/local/texlive/2026/bin/ref/pdftex /tmp/b/pdftex && ln -sf /usr/local/texlive/2026/bin/ref/pdftex /tmp/b/pdflatex
printf '\\documentclass{article}\n\\begin{document}\nHello.\n\\end{document}\n' > /m/doc.tex
run() { # name, then argv
  n=$1; shift
  rm -rf /tmp/w && mkdir -p /tmp/w && cp /m/doc.tex /tmp/w/ && cd /tmp/w
  DUMPOUT=/m/out-$n.json SOURCE_DATE_EPOCH=1788076260 FORCE_SOURCE_DATE=1 gdb -batch -nx -x /m/dump3.py --args "$@" < /dev/null > /m/gdb-$n.out 2>&1
  echo "$n: $(tail -2 /m/gdb-$n.out | head -1)"
}
run ini /tmp/b/pdftex -ini
run graded /tmp/b/pdflatex -interaction=nonstopmode -halt-on-error doc.tex
run graded2 /tmp/b/pdflatex -interaction=batchmode -file-line-error -draftmode doc.tex
run jobname /tmp/b/pdftex -ini -jobname=foo
run etex /tmp/b/pdftex -ini -etex
run iniamp /tmp/b/pdftex -ini '&pdflatex' doc.tex
run progname /tmp/b/pdftex -ini -progname=pdflatex
```

**Checkpoint 4: the functions one article runs** (`funcs2.py`: a temporary breakpoint on each of the 4,168 text symbols in `nm.txt`; `funcs2.json.gz`, every first hit with its caller; `entry.txt`, the 61 C functions the translated program calls directly; `counts.py`, `counts.json`: their calls before and after the first `pdfshipoutbegin`). The run script, `cp4-run.sh` (for `counts.py`, the same with `counts.py` and `counts.json`):

```sh
set -u
mkdir -p /tmp/b && ln -sf /usr/local/texlive/2026/bin/ref/pdftex /tmp/b/pdflatex
rm -rf /tmp/w && mkdir -p /tmp/w && cp /m/doc.tex /tmp/w/ && cd /tmp/w
FOUT=/m/funcs2.json SOURCE_DATE_EPOCH=1788076260 FORCE_SOURCE_DATE=1 gdb -batch -nx -x /m/funcs2.py --args /tmp/b/pdflatex -interaction=nonstopmode -halt-on-error doc.tex < /dev/null > /m/gdb-funcs2.out 2>&1
ls -la /tmp/w > /m/w.ls
```

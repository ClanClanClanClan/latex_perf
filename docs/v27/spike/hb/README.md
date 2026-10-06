# Boundary step: measurements on the reference build

Report: [`../H-boundary-report.md`](../H-boundary-report.md). The model's code is in `../h2/`
(`coq/KTypes.v`, `coq/Kpse.v`, `coq/Boundary.v`, `translate/evalorder.py`), the differential in
`../h2/diff/`.

Every gdb measurement here runs the unstripped reference build (sha256 `b23c26d6…`, whose
stripped form is the pinned arm64 binary; H.2 `evidence/cmain/README.md`) in the pinned image
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

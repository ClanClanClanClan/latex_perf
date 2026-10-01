# The C-main measurement

What TeX Live's C `main` (texmfmp.c: `main`, `maininit`, `parse_options`) writes into the
program's globals before it calls `mainbody`, MEASURED rather than modelled: the unstripped
reference build (sha256 `b23c26d6…`; stripped, it is the pinned arm64 binary, H.1 report §2)
stopped at `mainbody` under gdb, in the pinned image plus Debian's gdb (`lp-spike-gdb:arm64`),
for the command line `pdftex -ini` and `SOURCE_DATE_EPOCH=1788076260 FORCE_SOURCE_DATE=1`.
`../../translate/gen_cmain.py` turns the three JSON files into `CMain.v`.

| file | what it is |
|---|---|
| `globals.txt`, `dump.py` → `cmain_globals.json` | every global the program declares (697), its bytes at `mainbody`; for a non-NULL `char *`, the string |
| `globals2.txt`, `dump2.py` → `cmain_globals2.json` | 5 names web2c `#define`s to another C name (`dump_name` for `dumpname`, ...) |
| `cmain_globals3.json` | `p kpse_def->make_tex_discard_errors` at `mainbody` (= 0), the one value read through a struct |

**Recipe** (it starts the engine under gdb, which `check_oracle_pin.py` allows only inside
`_oracle.py`, so it is documentation, not an executable). With the reference build in REFDIR
and a directory W holding `dump.py`, `dump2.py`, `globals.txt`, `globals2.txt`:

```sh
docker run --rm --platform linux/arm64 --network none -v REFDIR:/usr/local/texlive/2026/bin/ref:ro \
  -v W:/w -v $PWD/run_cmain.sh:/run_cmain.sh:ro lp-spike-gdb:arm64 sh /run_cmain.sh
```

where `run_cmain.sh` is:

```sh
cd /tmp
SOURCE_DATE_EPOCH=1788076260 FORCE_SOURCE_DATE=1 gdb -batch -nx -x /w/dump.py --args /usr/local/texlive/2026/bin/ref/pdftex -ini < /dev/null > /w/gdb.out 2>&1
SOURCE_DATE_EPOCH=1788076260 FORCE_SOURCE_DATE=1 gdb -batch -nx -x /w/dump2.py --args /usr/local/texlive/2026/bin/ref/pdftex -ini < /dev/null > /w/gdb2.out 2>&1
SOURCE_DATE_EPOCH=1788076260 FORCE_SOURCE_DATE=1 gdb -batch -nx -ex 'set pagination off' -ex 'break mainbody' -ex run -ex 'p kpse_def->make_tex_discard_errors' -ex kill --args /usr/local/texlive/2026/bin/ref/pdftex -ini < /dev/null > /w/gdb3.out 2>&1
```

**Reproduced 2026-10-01** (spike H.2 checkpoint 3, review B MEDIUM-1): a fresh run of this
recipe gave JSON files that differ from the committed ones only in the two pointer values
(`TEXformatdefault`, `versionstring`: gdb cannot disable address-space randomisation in the
container), the same strings, and `gen_cmain.py` on them gives a `CMain.v` byte-identical to the
measured build's; the third command printed `$1 = 0`.

The measurement holds for this command line and an environment that sets no kpathsea variable;
`Boundary.v` is Stuck on any other command line.

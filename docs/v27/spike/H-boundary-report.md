# Foundation spike, boundary step: pdfTeX's C boundary for file input, fonts and C main

**Spike:** [ADR-015](../adr/ADR-015-static-proven-tier-on-translated-engine.md) (ledger OPEN-123).
**Why this step:** the re-audit of 2026-10-07 found that H.4, H.5's documents and H.6 are all
blocked on the C boundary. Every L_S0 document is `\documentclass{article}`, which needs file
input, TFM loading and the PDF back end, and all three were unmodelled. Code: `h2/coq/Kpse.v`,
`h2/coq/KTypes.v`, `h2/coq/Boundary.v`, `h2/translate/evalorder.py`, `h2/coq/driver.ml`,
`h2/diff/`.
**Owner standard:** every external is modelled from its C source, justified line by line, or it
is Stuck. Environment-dependent inputs (file contents, the kpathsea database, directory
listings) become explicit inputs of the run, part of its identity, as C-107 did for the clock.
Owner decision E14 holds: this step adds no realizer row (`Extract.v` gains only
`Extraction NoInline` directives for named constants, which choose how Coq prints a constant,
not what it means).

Evidence tags: **[M]** measured, **[R]** read from a source, **[I]** inferred.

## Checkpoints

| # | what | result |
|---|---|---|
| 1 | kpathsea file input: `\input`, `\openin`/`\read`, a missing file, `\openout` and its paranoia check | CHECKPOINT1 |
| 2 | TFM loading: `\font`, `\showbox` of a typeset `\hbox` | CHECKPOINT2 |
| 3 | the general C-main command line; `pdflatex.fmt` and a one-line `\documentclass{article}` run up to PDF output | CHECKPOINT3 |
| 4 | the PDF back end: scope only | measured: 137 C functions (61,720 bytes of machine code) first run after PDF output starts on the one-line article; deflate, MD5, the 5.6 MB map file, Type 1 subsetting; no libpng, no xpdf |

## Checkpoint 1: kpathsea file input

### The run's file system is an explicit input

`Values.io` gains the file-system snapshot (`KTypes.fsent`): a list of canonical absolute paths,
each with what `stat(2)`, `access(2)`, `opendir(3)`/`readdir(3)` and `fopen(3)` find there:

- `FsFile c`: a file kpathsea's `READABLE` accepts (readable.c: `access (R_OK) == 0 &&
  stat == 0 && !S_ISDIR`), with its bytes, or without them;
- `FsDir l`: a directory, with its complete listing (`readdir`'s names besides `.` and `..`),
  or without one;
- `FsAbsent`: `stat` fails.

A question the snapshot does not decide is **Stuck**. A path is decided by its own entry, or as
absent by an ancestor's (an ancestor that is absent or a file, or a listed directory without the
next component). The working directory (`cwd`, a canonical path) is also an input; the files the
run creates there are added to what `stat` and `readdir` see.

The snapshot is measured, never assumed: `h2/diff/snapshot.py` runs `test -d`, `test -e` and
GNU `find -maxdepth 1` in the pinned image and copies out the bytes it records (the
`@sha256:` lines of `h2/diff/base.spec`). It never starts a TeX engine. Each differential input
adds its working directory: `inputs/NAME.files/` holds the files, `diff.py prepare` lists them
and gives their bytes.

### kpathsea's configuration is an explicit input

`io_kfmt` gives, per format, what `kpse_init_format` computes: the search path after variable,
brace and default expansion, the suffix and alt-suffix lists, `suffix_search_only`, and whether
`kpse_make_tex` would run a program. These values come from texmf.cnf, the environment and the
program name. Like `kpse_var_value`'s values (`io_kpse`, H.2), they are measured, not modelled.
They were read under gdb on the reference build at `mainbody` (`hb/kpse-measure.out`). The values
`kpse_var_value` gives for `texmf_casefold_search` (1), `try_std_extension_first` (t) and
`log_openout` (t) were read the same way. `TEXMFLOG` and `TEXMFOUTPUT` are NULL.

### What is modelled (Kpse.v), from the C source of r78081 [R]

`find_file` follows `tex-file.c kpathsea_find_file_generic`:
- the name's `$` and `~` expansion (expand.c): Stuck when either occurs;
- `has_any_suffix` and `has_potential_suffix` against the suffix and alt-suffix lists;
- the targets in the order `try_std_extension_first` gives, with the fontmap's names for the
  tfm, gf, pk and ofm formats;
- the search without, then with, `must_exist`. The second search uses the names
  `suffix_search_only` allows;
- then `kpse_make_tex`. When the format's program is enabled and the name has only the bytes
  tex-make.c allows, it would run a script, which is Stuck. Otherwise it returns NULL.

`generic` follows `pathsearch.c kpathsea_path_search_list_generic`:
- absolute and explicitly relative names (`absolute_search`, with the case-folding fallback);
- then path element by element (path-elt.c, braces and both separators). `!!` forbids the disk.
  `normalize_path` collapses leading slashes;
- the ls-R database first (db.c `kpathsea_db_search_list`, with `match` and `elt_in_db`
  ported character by character, a hit checked on disk). The disk is searched when the database
  does not cover the element, or under `must_exist` when it found nothing;
- the disk search (`dir_list_search_list` over `element_dirs`), then the case-folded one when
  `texmf_casefold_search` is set;
- `str_list_uniqify`, and `log_search`, which is Stuck when `$TEXMFLOG` is set.

`search1` follows `pathsearch.c search` (the one-name search used for the fontmap and the alias
files). The ls-R database follows db.c `kpathsea_init_db`:
- the `ls-r`/`ls-R` files along the db path, found with no database;
- deduplication of names equal under strcasecmp;
- each file through `db_build` and line.c `read_line`: directory lines, `ignore_dir_p`, the
  `./` prefix rule, and `.`/`..` skipped;
- the alias files, which must be absent.

C builds the database in C main (cnf.c `kpathsea_cnf_get` calls `kpathsea_init_db`). The model
builds it on first use from the snapshot as it was before the run, which gives the same value.

The fontmap follows fontmap.c: `read_all_maps`, `map_file_parse` (the comment at the last `%` or
the first `@c`, `token`, `include`) and `kpathsea_fontmap_lookup` (the key, then the key without
its suffix, then `extend_filename`).

| C behaviour | model | why |
|---|---|---|
| absolute names, `./`, `../` | modelled; a `..` component is Stuck | the kernel resolves `..` after symbolic links, which the snapshot does not record |
| `$VAR`, `~` in a name | Stuck | the expansion reads variables and the password database |
| a `//` element on disk (`do_subdir`) | modelled when its directory does not exist; Stuck when it does | the result depends on readdir order and `st_nlink`; every `//` element of the TeX tree is `!!` (database only) |
| the case-folding fallback | modelled when at most one entry qualifies; Stuck when several do | the first entry in readdir order wins in C |
| `mktex*` | Stuck when kpathsea would run it | a program |
| alias databases, `$TEXMFLOG`, an ls-R with no usable entry, a fontmap warning | Stuck | not in the pinned tree, or a message on stderr during C main |
| the element-directory cache, `str_llist_float`, the dir-links table | not kept | no result depends on them: the directories do not change during a run, and every directory list the model forms has at most one element |
| `ENAMETOOLONG` truncation (readable.c) | Stuck | a component longer than 255 bytes, or a path of 4,096 bytes or more |
| `temp_str` freed twice (db.c, a name without `/` after one with `/`) | Stuck | undefined behaviour in C |

### The externals of file input (Boundary.v), each from its C source [R]

| external | C source | model |
|---|---|---|
| `kpseinnameok` | tex-file.c `kpathsea_name_ok`, `ok_reading` | returns true before reading `openin_any` (r78081: "As of 2026, if ACTION is ok_reading, we simply return true") |
| `kpsetexformat` | texmfmp.h | `kpse_tex_format` = 26 (types.h) |
| `aopenin` | texmfmp.h `open_in_or_pipe` | a `|` name with shell escape is Stuck (a pipe); otherwise `open_input` |
| `bopenin` | texmfmp.h | `open_input (&f, kpse_tfm_format, "rb")`; `tfmtemp = getc (f)` |
| `wopenin` | texmfmp.h | `open_input (&f, DUMP_FORMAT, "rb")` and `gzdopen`. The stream is the decompressed one the run gives (TB-7, as H.3). H.3's `kpsefind` table input is retired: the format file is now found by the modelled search |
| (`open_input`) | openclose.c | as C: NULL; free `fullnameoffile`; `must_exist` from `texinputtype`; `kpse_find_file`; `xstrdup`; the `./` rule; `xfopen` (the snapshot must hold the bytes); `nameoffile` and `namelength` re-made. No `-output-directory`, no recorder: the measured command line, else Stuck |
| `inputln` | texmfmp.c `input_line` | now for any stream, not only the terminal. It sets `last = first` at the end of the file: H.2's terminal-only model did not write `last` there, which the differential found (`kp-openin`, below) |
| `aclose`, `bclose` | texmfmp.h `close_file_or_pipe` | releases an input stream and its end-of-file indicator |
| `getc`, `feof`, `eof` | stdio; lib/eofeoln.c `eof` | the next byte or EOF (which sets the indicator); the indicator; `eof`'s peek, which sets the indicator at the end |
| `makefullnamestring` | texmfmp.c | `maketexstring (fullnameoffile)`; NULL gives `getnullstr ()` |
| `synctexstartinput` | synctex.c | the option is read once. The tag counter goes into `curinput.synctextagfield`. With `\synctex` = 0, `synctex_dot_open` returns NULL. Non-zero is Stuck (a .synctex file) |
| `kpseoutnameok` | tex-file.c `kpathsea_name_ok`, `ok_writing` | `openout_any` (default `p`): the dot-file check, `r`, the absolute-path check against `TEXMF_OUTPUT_DIRECTORY` and `TEXMFOUTPUT`, `../` and `/../`. A refusal writes C's message on stderr |
| `texmfyesno` | texmfmp.c `texmf_yesno` | `kpse_var_value` starts with `t`, `y` or `1` |
| `pdfassert` | pdftex.h `#define pdfassert assert` | NDEBUG is not defined (the binary calls `__assert_fail`): a false condition is Stuck (abort) |
| `promptfilenamehelpmsg`, `printcstring` | cpascal.h | the string literal; `printchar` on each byte |
| `synctexterminate` | synctex.c | removes `<log>.synctex(.gz)`: Stuck when the working directory has such an entry, otherwise nothing |
| `aopenout`, `wopenout` (changed) | openclose.c `open_output` | a new name must be absent from the snapshot's working directory. H.2's class was an empty one |

### The evaluation order: one refinement (translate/evalorder.py) [R]

Modelling `makefullnamestring` turned `fullsourcefilenamestack[inopen] := makefullnamestring`
(`startinput`) into an unsequenced conflict. The callee `makestring` can call `overflow`,
whose effects include `inopen`. The analysis is path-insensitive. The source declares four
procedures `noreturn` (`jumpout`, `overflow`, `fatalerror`, `confusion`). evalorder.py now
verifies each: its body has no return, goto or label, and every branch ends in `uexit` or in a
call to one of the four. It then computes a second effect summary per procedure, for the paths
that return, in which those calls and `uexit` contribute nothing.

Rule (b) uses that summary. A part that writes nothing commutes with a part whose returning
paths write nothing it reads. If the other part returns, both orders reach the same state and
values. If it never returns, the part that wrote nothing left no trace either way. The rule only
removes conflicts:
- 25 conflicts before (H.3);
- 26 with the new externals;
- 19 after rule (b).

The ones removed are in `startinput`, `appendbead` (2; the H.2 report's own example of a false
conflict), `scanimage` and `doextension` (3, the `\openout` path).

### Results

RESULTS1

## Checkpoint 2: TFM loading

TFM reading is Pascal (`read_font_info`). Its C boundary is checkpoint 1's: `bopenin` (with the
first `getc` into `tfmtemp`), `getc`, `eof`, `bclose`, the tfm format's search with the fontmap
(`texfonts.map`, read once at the first lookup) and `mktextfm` (Stuck when a font is missing).
No further external was needed.

RESULTS2

## Checkpoint 3: the general C-main command line, and a `\documentclass{article}` run

### C main is modelled for the oracle's allow-listed command lines

H.2 measured what TeX Live's C main writes before `mainbody` for one command line, `pdftex -ini`
(`CMain.v`, gdb at `mainbody`). That measurement stays. What depends on the command line is now a
Coq function of the run's argv (`Boundary.cmain_model`, applied in `Main.initial_state`), from
texmfmp.c `maininit`, `parse_options`, `get_input_file_name`, `parse_first_line` and
`init_shell_escape`:
- the options `getopt_long_only` accepts in the forms `-NAME`, `--NAME`, `-NAME=VALUE` and
  `--NAME=VALUE`. These are the oracle's allow-lists (`_oracle.py`: a graded run's
  `-interaction=MODE`, `-halt-on-error`, `-file-line-error`, `-draftmode`; run_engine's `-ini`,
  `-etex`, `-jobname=NAME`, `-progname=pdflatex`). Parsing stops at the first non-option (the
  `+` in the option string);
- the program name, from `-progname` or `basename (argv[0])`: `pdftex` or `pdflatex`;
- the main input file, `kpse_find_file (name, kpse_tex_format, false)`. This is checkpoint 1's
  search, run at C main on the snapshot;
- `parse_first_line`: the first line of that file must not start with `%&`;
- `dump_name`: argv[1] after `&` when no main input file was found, else the program name. It
  gives `TEXformatdefault` (" NAME.fmt") and `formatdefaultlength`;
- `file_line_error_style`, `parse_first_line` and `shell_escape` through `texmf_yesno` and
  `kpse_var_value`;
- `c_job_name`, which `getjobname` now reads;
- `topenin`, which copies the arguments after the options into `buffer`. It trims trailing
  space, CR and LF and maps through `xord`, and copies only once (`argc = 0`).

A command line outside this class is Stuck before anything observable happens. That covers
another option, an abbreviation, `--`, `-recorder`, `-translate-file`, another program name, a
`%&` first line, or a warning C main would write. The first statement of `mainbody` that is not
an assignment is `setupboundvariable`, the first external call, and `ext` reports it there.

**Evidence that the measured part does not depend on the command line within the class.** gdb
at `mainbody` on seven command lines (`hb/cmain-seven.txt`):
- `pdftex -ini`;
- `pdflatex -interaction=nonstopmode -halt-on-error doc.tex`;
- `pdflatex -interaction=batchmode -file-line-error -draftmode doc.tex`;
- `pdftex -ini -jobname=foo`;
- `pdftex -ini -etex`;
- `pdftex -ini &pdflatex doc.tex`;
- `pdftex -ini -progname=pdflatex`.

The only globals that differ from `pdftex -ini` are those `cmain_model` writes:
`TEXformatdefault`, `formatdefaultlength`, `haltonerrorp`, `iniversion`, `interactionoption`,
`filelineerrorstylep`, `pdfdraftmodeoption`, `pdfdraftmodevalue` and `etexp`. The C statics
`dump_name`, `c_job_name` and `user_progname`, kpathsea's program name and `optind` also differ.
kpathsea's values are the same for both program names. Its format table differs in two
formats, the fontmap and the tex paths (`hb/kpse-pdflatex.txt`). These are explicit inputs,
measured per program name.

CM3RESULTS

### A one-line `\documentclass{article}` document, up to PDF output

The document is `hb/article/doc.tex`:
`\documentclass{article}\begin{document}Hello.\end{document}`. It runs with the graded
command line `pdflatex -interaction=nonstopmode -halt-on-error doc.tex` (`argv0 pdflatex`).

**The run's identity** (`hb/article/spec.base`):
- base.spec's kpathsea values;
- the format table measured for program name `pdflatex` (`hb/kpse-pdflatex.txt`);
- the TeX-tree snapshot;
- the working directory with `doc.tex`;
- `pdflatex.fmt` found by the modelled search, its decompressed stream given (TB-7, as H.3).

The rest of the snapshot was grown from the model's own questions by `h2/diff/snapgrow.py`. Each
time the model is Stuck on a path the snapshot does not decide, the tool measures that one path
in the image and runs again. It took three iterations, one per file the preamble reads:
`article.cls`, `size10.clo`, `l3backend-pdftex.def` (`hb/article/snapgrow.log`,
`hb/article/snapshot.grown`). The binary's own `-recorder` list names the same three
(`hb/article/fls.txt`). Two earlier iterations, on an intermediate build, were Stuck on
`getfilesize` (LaTeX's `\pdffilesize` of the class), now modelled from texmfmp.c (below).

**Result [M].** The model, under `h3/tools/capped.sh` at 4,000 MB (finished rc 0 peak 2490MB in 2036s), loads the format and runs
the preamble and `\begin{document}`:
- it reads the three files and finds no `doc.aux` (`No file doc.aux.`);
- it opens `doc.aux` for writing and typesets the page;
- it reaches the first `\shipout`: `shipout > pdfshipout > checkpdfversion > ensurepdfopen`;
- there it is Stuck on **`bopenout`**, which opens `doc.pdf`.

Up to that point its terminal output (503 bytes), `doc.log` (1,849 bytes) and `doc.aux`
(8 bytes, `\relax`) are each an exact byte prefix of the binary's (749, 2,764 and 32 bytes;
`hb/article/`). It used 1 clock reading, and its standard input was empty and fully read.

**The externals hit next.** These are the PDF back end. They are listed from the binary's run of
the same command line (checkpoint 4, `hb/counts.json`), with the number of calls after the first
`pdfshipoutbegin`. They come after `bopenout`, which `ensurepdfopen` calls once [R]:
`zround` 13, `avlputobj` 10, `isscalable` 9, `close_file_or_pipe` 5, `writestreamlength` 5, `writezip` 5, `synctexhlist` 4, `synctexhorizontalruleorglue` 4, `synctextsilh` 4, `synctextsilv` 4, `synctexvlist` 4, `initstarttime` 3, `input_line` 3, `open_input` 3, `synctexcurrent` 2, `synctexvoidhlist` 2, `checkimageb` 1, `checkimagec` 1, `checkimagei` 1, `colorstackskippagestart` 1, `colorstackused` 1, `dopdffont` 1, `flushjbig2page0objects` 1, `hasspacechar` 1, `kpse_in_name_ok` 1, `libpdffinish` 1, `makefullnamestring` 1, `open_in_or_pipe` 1, `pdfshipoutbegin` 1, `pdfshipoutend` 1, `printID` 1, `printcreationdate` 1, `printmoddate` 1, `synctexstartinput` 1, `synctexteehs` 1, `synctexterminate` 1, `uexit` 1, `writefontstuff` 1.

Of these, 28 are unmodelled and would each be Stuck, after `bopenout`: `zround`, `avlputobj`, `isscalable`, `writestreamlength`, `writezip`, `synctexhlist`, `synctexhorizontalruleorglue`, `synctextsilh`, `synctextsilv`, `synctexvlist`, `synctexcurrent`, `synctexvoidhlist`, `checkimageb`, `checkimagec`, `checkimagei`, `colorstackskippagestart`, `colorstackused`, `dopdffont`, `flushjbig2page0objects`, `hasspacechar`, `libpdffinish`, `pdfshipoutbegin`, `pdfshipoutend`, `printID`, `printcreationdate`, `printmoddate`, `synctexteehs`, `writefontstuff`. The others are the file-input externals of checkpoint 1 and the `\\end{document}` re-reading of `doc.aux`. That re-read is Stuck too: it reads a file this run wrote, which the model does not hold yet.

Externals newly modelled at checkpoint 3, each from its C source:
- `getfilesize` (texmfmp.c: `find_input_file`, then `kpse_find_file (name, kpse_tex_format,
  true)` and `stat`'s `st_size` printed `%lu` onto the pool; `makecfilename` removes the double
  quotes);
- `removepdffile` (utils.c: nothing until the PDF file is opened, or in draft mode; otherwise
  Stuck);
- `synctexabort` (synctex.c: with no SyncTeX file, it only turns SyncTeX off, which
  `synctexstartinput` then respects).

These three bring the modelled externals to 61 of 188.


## Checkpoint 4: the PDF back end, scope only [M]

**What was measured.** The pinned reference build (`b23c26d6…`, the unstripped twin of the pinned
arm64 binary) ran under gdb as `pdflatex -interaction=nonstopmode -halt-on-error doc.tex`, in the
pinned image plus gdb. `doc.tex` is the one-line article
`\documentclass{article}\begin{document}Hello.\end{document}`. The run had a temporary
breakpoint on each of the binary's 4,168 text symbols (`nm -S`), which records every function that
runs, in the order it first runs (`hb/funcs2.py`, `hb/funcs2.json.gz`). A second run counted the
calls of each C function the translated program calls directly, before and after the first
`pdfshipoutbegin` (`hb/counts.py`, `hb/counts.json`). The run wrote a 1-page, 11,928-byte PDF.

522 distinct functions run: 210 translated (`pdftex0.c`, `pdftexini.c`) and 312 C. Of the C
functions, 137 first run after PDF output starts. Their sizes are below, as machine code of
those functions (from `nm -S`) and as the line count of their source file (r78081):

| source file | functions first run after PDF output starts | of which | machine code (bytes, those functions) | file lines |
|---|---|---|---|---|
| `-` | 1 | `epdf_check_mem` | 112 | - |
| `zlib/adler32.c` | 2 | `adler32`, `adler32_z` | 964 | 164 |
| `zlib/deflate.c` | 12 | `deflateInit_`, `deflateInit2_`, `deflateReset`, `deflateResetKeep`, `deflateStateCheck`, `deflate`, `flush_pending`, `deflate_slow`, `fill_window`, `read_buf`, `longest_match`, `deflateEnd` | 8,796 | 2185 |
| `zlib/trees.c` | 9 | `_tr_init`, `bi_flush`, `_tr_flush_block`, `build_tree`, `pqdownheap`, `scan_tree`, `compress_block`, `bi_windup`, `send_tree` | 6,068 | 1119 |
| `texk/kpathsea/xfseeko.c` | 1 | `xfseeko` | 92 | 26 |
| `lib/texmfmp.c` | 2 | `convertStringToHexString`, `gettexstring` | 272 | 4214 |
| `lib/uexit.c` | 1 | `uexit` | 12 | 20 |
| `lib/zround.c` | 1 | `zround` | 92 | 42 |
| `libmd5/md5.c` | 4 | `md5_init`, `md5_append`, `md5_finish`, `md5_process` | 3,148 | 381 |
| `pdftexdir/avl.c` | 5 | `avl_find`, `avl_t_init`, `avl_t_first`, `avl_t_next`, `avl_destroy` | 928 | 796 |
| `pdftexdir/avlstuff.c` | 3 | `comp_string_entry`, `comp_int_entry`, `avl_xfree` | 88 | 172 |
| `pdftexdir/epdf.c` | 1 | `epdf_free` | 4 | 111 |
| `pdftexdir/mapfile.c` | 16 | `isscalable`, `hasfmentry`, `fm_read_info`, `fm_scan_line`, `new_fm_entry`, `check_std_t1font`, `avl_do_entry`, `comp_fm_entry_tfm`, `comp_fm_entry_ps`, `hasspacechar`, `check_ff_exist`, `fm_free`, `destroy_fm_entry_tfm`, `delete_fm_entry`, `destroy_fm_entry_ps`, `destroy_ff_entry` | 6,048 | 957 |
| `pdftexdir/subfont.c` | 2 | `handle_subfont_fm`, `sfd_free` | 1,456 | 228 |
| `pdftexdir/tounicode.c` | 5 | `write_tounicode`, `set_glyph_unicode`, `utf16be_str`, `glyph_unicode_free`, `destroy_glyph_unicode_entry` | 2,876 | 556 |
| `pdftexdir/utils.c` | 19 | `pdfshipoutbegin`, `colorstackused`, `colstacks_first_init`, `colorstackskippagestart`, `tex_printf`, `xgetc`, `pdfshipoutend`, `xfwrite`, `writestreamlength`, `pdf_puts`, `pdf_printf`, `fb_putchar`, `fb_offset`, `make_subset_tag`, `fb_flush`, `printcreationdate`, `printmoddate`, `printID`, `libpdffinish` | 2,948 | 1558 |
| `pdftexdir/vfpacket.c` | 1 | `vf_free` | 212 | 107 |
| `pdftexdir/writeenc.c` | 2 | `write_fontencodings`, `enc_free` | 512 | 180 |
| `pdftexdir/writefont.c` | 14 | `dopdffont`, `lookup_fd_entry`, `create_fontdescriptor`, `new_fd_entry`, `register_fd_entry`, `create_charwidth_array`, `write_charwidth_array`, `mark_chars`, `writefontstuff`, `write_fontdescriptors`, `write_fontdescriptor`, `write_fontname`, `write_fontdictionaries`, `write_fontdictionary` | 6,416 | 722 |
| `pdftexdir/writeimg.c` | 4 | `checkimageb`, `checkimagec`, `checkimagei`, `img_free` | 68 | 549 |
| `pdftexdir/writejbig2.c` | 1 | `flushjbig2page0objects` | 96 | 834 |
| `pdftexdir/writet1.c` | 19 | `writet1`, `t1_open_fontfile`, `t1_subset_ascii_part`, `t1_getline`, `t1_getbyte`, `t1_scan_param`, `t1_putline`, `t1_scan_num`, `str_suffix`, `comp_t1_glyphs`, `t1_printf`, `t1_start_eexec`, `edecrypt`, `cs_store`, `t1_mark_glyphs`, `cs_mark`, `t1_flush_cs`, `t1_stop_eexec`, `t1_free` | 15,420 | 1727 |
| `pdftexdir/writettf.c` | 1 | `ttf_free` | 28 | 1463 |
| `pdftexdir/writezip.c` | 2 | `writezip`, `zip_free` | 884 | 95 |
| `synctexdir/synctex.c` | 9 | `synctexvlist`, `synctexhlist`, `synctexvoidhlist`, `synctextsilh`, `synctextsilv`, `synctexcurrent`, `synctexhorizontalruleorglue`, `synctexteehs`, `synctexterminate` | 4,180 | 2177 |
| **total** | **137** | | **61,720** | |

Not reached by the minimal article (no image, no included PDF, no TrueType, OpenType or PK font,
no `\pdfmapfile`):
- `writejpg.c` (404 lines);
- `writepng.c` (677 lines), with libpng (38,279 lines of C);
- `pdftoepdf.cc` (1,078 lines), with xpdf (120,528 lines of C++);
- most of `writettf.c` (1,463), `writet3.c` (429) and `pkin.c` (425);
- `writejbig2.c` (834), of which only `flushjbig2page0objects` runs.

**What the minimal article needs,** by function:
- the page and object stream writer: utils.c `pdf_puts`, `pdf_printf`, `fb_*`, `writestreamlength`,
  `printID` (an MD5 of the time and file name: libmd5), `printcreationdate`, `printmoddate`;
- stream compression: writezip.c, calling zlib's deflate (`deflate.c`, `trees.c`, `adler32.c`), at
  pdfTeX's default `\pdfcompresslevel` 9;
- the map file: mapfile.c `fm_read_info` reads and parses all of
  `texmf-var/fonts/map/pdftex/updmap/pdftex.map` (5,609,353 bytes, 46,659 lines) into AVL trees
  (avl.c) at the first shipout. Then `hasfmentry` and `isscalable` look up each font;
- Type 1 embedding: writet1.c reads `cmr10.pfb` (35,752 bytes), decrypts eexec and charstrings
  (`edecrypt`, `cs_store`), marks and subsets the used glyphs (`t1_mark_glyphs`, `cs_mark`,
  `t1_flush_cs`) and writes the subset with a tag (`make_subset_tag`: the MD5 of the glyph
  list);
- font dictionaries and descriptors: writefont.c, writeenc.c, tounicode.c;
- synctex.c's node hooks, which return early with SyncTeX off (9 functions, all no-ops on this
  class).

Per the externals the translated program calls, after the first `pdfshipoutbegin`:
- one call each: `pdfshipoutbegin`, `pdfshipoutend`, `dopdffont`, `writefontstuff`, `printID`,
  `printcreationdate`, `printmoddate`, `libpdffinish`, the three `checkimage*`, `colorstackused`,
  `colorstackskippagestart`, `flushjbig2page0objects`, `hasspacechar`;
- `isscalable` (9), `avlputobj` (10), `writezip` (5), `writestreamlength` (5), `zround` (13).

The sizes say where the work is. deflate is about 3,300 lines of zlib, of which the model needs
only the compressing half; with `\pdfcompresslevel=0`, writezip would not run. The Type 1 path is
about 1,700 lines of writet1.c. The map-file parser is about 950 lines, with a 5.6 MB input that
has the same scale problem the ls-R database had. The output layer is about 1,500 lines of
utils.c. libpng and xpdf, 158,000 lines, are not on the minimal article's path at all.

## Trusted-base changes

None beyond modelling:
- TB-3 (the translator): the evaluation-order refinement above, which only removes conflicts and
  verifies its own premise;
- TB-5 (the C boundary): the externals above;
- TB-8 (the environment class): it widens from "an empty working directory" to "the snapshot
  the run's identity gives". The snapshot is measured by a committed tool in the pinned image,
  and every question it does not decide is Stuck. The format table `io_kfmt` is measured like
  `io_kpse`.

- TB-5 (C main): H.2's gdb measurement for `pdftex -ini` stays. What depends on the command line
  is now modelled (`cmain_model`), and seven measured command lines show that this is all of
  it, within the class. The program name (`argv0`) becomes an explicit input: kpathsea reads it,
  and `kpse_out_name_ok` prints it.

There is no new realizer and no new primitive. `Extract.v` gains only `Extraction NoInline`
directives for named byte constants.

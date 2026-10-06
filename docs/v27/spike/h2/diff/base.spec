# The run identity every differential input shares (diff.py, driver.ml SPEC).
# The command line C main was measured with (evidence/cmain/).
argv0 pdftex
argv -ini
# The environment variables the modelled externals read (Boundary.v environment audit).
env SOURCE_DATE_EPOCH=1788076260
env FORCE_SOURCE_DATE=1
# kpse_var_value in the pinned image with this environment: evidence/inirun/kpsevars.txt,
# the pdftex column (kpathsea program name of pdftex -ini); an empty [] there is NULL.
kpse main_memory=5000000
kpse extra_mem_top=0
kpse extra_mem_bot=0
kpse pool_size=6250000
kpse string_vacancies=90000
kpse pool_free=47500
kpse max_strings=500000
kpse strings_free=100
kpse font_mem_size=8000000
kpse font_max=9000
kpse trie_size=1100000
kpse hyph_size=8191
kpse buf_size=200000
kpse nest_size=1000
kpse max_in_open=15
kpse param_size=20000
kpse save_size=200000
kpse stack_size=10000
kpse dvi_buf_size=16384
kpse error_line=79
kpse half_error_line=50
kpse max_print_line=79
kpse hash_extra=600000
kpse file_line_error_style=f
kpse parse_first_line=t
kpse shell_escape=p
kpse shell_escape_commands=bibtex,bibtex8,extractbb,gregorio,kpsewhich,l3sys-query,latexminted,makeindex,memoize-extract.pl,memoize-extract.py,repstopdf,r-mpost,texosquery-jre8,
kpse openout_any=p
kpse openin_any=a
kpse command_line_encoding=utf-8
# kpathsea values the file search reads (Kpse.v), kpathsea_var_value on the reference build
# under gdb at mainbody (H-boundary-report.md, evidence ../../hb/kpse-measure.out); TEXMFLOG
# and TEXMFOUTPUT are NULL there, so absent here
kpse texmf_casefold_search=1
kpse try_std_extension_first=t
kpse log_openout=t
# the working directory (its listing and files are each input's: inputs/NAME.files/)
cwd /w
# kpse_format_info after kpse_init_format, on the reference build under gdb (same evidence):
# kfmt FORMAT suffix_search_only make_tex-runs-a-program suffixes alt_suffixes path
kfmt 3 1 1 .tfm - .:/root/.texlive2026/texmf-config/fonts/tfm//:/root/.texlive2026/texmf-var/fonts/tfm//:/root/texmf/fonts/tfm//:!!/usr/local/texlive/texmf-local/fonts/tfm//:!!/usr/local/texlive/2026/texmf-config/fonts/tfm//:!!/usr/local/texlive/2026/texmf-var/fonts/tfm//:!!/usr/local/texlive/2026/texmf-dist/fonts/tfm//:/root/.texlive2026/texmf-var/fonts/tfm//
kfmt 9 0 0 ls-R,ls-r - /usr/local/texlive/texmf-local:/usr/local/texlive/2026/texmf-config:/usr/local/texlive/2026/texmf-var:/usr/local/texlive/2026/texmf-dist
kfmt 10 0 1 .fmt - .:/root/.texlive2026/texmf-config/web2c/pdftex:/root/.texlive2026/texmf-var/web2c/pdftex:/root/texmf/web2c/pdftex:!!/usr/local/texlive/texmf-local/web2c/pdftex:!!/usr/local/texlive/2026/texmf-config/web2c/pdftex:!!/usr/local/texlive/2026/texmf-var/web2c/pdftex:!!/usr/local/texlive/2026/texmf-dist/web2c/pdftex:/root/.texlive2026/texmf-config/web2c:/root/.texlive2026/texmf-var/web2c:/root/texmf/web2c:!!/usr/local/texlive/texmf-local/web2c:!!/usr/local/texlive/2026/texmf-config/web2c:!!/usr/local/texlive/2026/texmf-var/web2c:!!/usr/local/texlive/2026/texmf-dist/web2c
kfmt 11 0 0 .map - .:/root/.texlive2026/texmf-config/fonts/map/pdftex//:/root/.texlive2026/texmf-var/fonts/map/pdftex//:/root/texmf/fonts/map/pdftex//:!!/usr/local/texlive/texmf-local/fonts/map/pdftex//:!!/usr/local/texlive/2026/texmf-config/fonts/map/pdftex//:!!/usr/local/texlive/2026/texmf-var/fonts/map/pdftex//:!!/usr/local/texlive/2026/texmf-dist/fonts/map/pdftex//:/root/.texlive2026/texmf-config/fonts/map/pdftex//:/root/.texlive2026/texmf-var/fonts/map/pdftex//:/root/texmf/fonts/map/pdftex//:!!/usr/local/texlive/texmf-local/fonts/map/pdftex//:!!/usr/local/texlive/2026/texmf-config/fonts/map/pdftex//:!!/usr/local/texlive/2026/texmf-var/fonts/map/pdftex//:!!/usr/local/texlive/2026/texmf-dist/fonts/map/pdftex//:/root/.texlive2026/texmf-config/fonts/map/dvips//:/root/.texlive2026/texmf-var/fonts/map/dvips//:/root/texmf/fonts/map/dvips//:!!/usr/local/texlive/texmf-local/fonts/map/dvips//:!!/usr/local/texlive/2026/texmf-config/fonts/map/dvips//:!!/usr/local/texlive/2026/texmf-var/fonts/map/dvips//:!!/usr/local/texlive/2026/texmf-dist/fonts/map/dvips//:/root/.texlive2026/texmf-config/fonts/map///:/root/.texlive2026/texmf-var/fonts/map///:/root/texmf/fonts/map///:!!/usr/local/texlive/texmf-local/fonts/map///:!!/usr/local/texlive/2026/texmf-config/fonts/map///:!!/usr/local/texlive/2026/texmf-var/fonts/map///:!!/usr/local/texlive/2026/texmf-dist/fonts/map///
kfmt 26 0 0 .tex .sty,.cls,.fd,.aux,.bbl,.def,.clo,.ldf .:/root/.texlive2026/texmf-config/tex/plain//:/root/.texlive2026/texmf-var/tex/plain//:/root/texmf/tex/plain//:!!/usr/local/texlive/texmf-local/tex/plain//:!!/usr/local/texlive/2026/texmf-config/tex/plain//:!!/usr/local/texlive/2026/texmf-var/tex/plain//:!!/usr/local/texlive/2026/texmf-dist/tex/plain//:/root/.texlive2026/texmf-config/tex/generic//:/root/.texlive2026/texmf-var/tex/generic//:/root/texmf/tex/generic//:!!/usr/local/texlive/texmf-local/tex/generic//:!!/usr/local/texlive/2026/texmf-config/tex/generic//:!!/usr/local/texlive/2026/texmf-var/tex/generic//:!!/usr/local/texlive/2026/texmf-dist/tex/generic//:/root/.texlive2026/texmf-config/tex/latex//:/root/.texlive2026/texmf-var/tex/latex//:/root/texmf/tex/latex//:!!/usr/local/texlive/texmf-local/tex/latex//:!!/usr/local/texlive/2026/texmf-config/tex/latex//:!!/usr/local/texlive/2026/texmf-var/tex/latex//:!!/usr/local/texlive/2026/texmf-dist/tex/latex//:/root/.texlive2026/texmf-config/tex///:/root/.texlive2026/texmf-var/tex///:/root/texmf/tex///:!!/usr/local/texlive/texmf-local/tex///:!!/usr/local/texlive/2026/texmf-config/tex///:!!/usr/local/texlive/2026/texmf-var/tex///:!!/usr/local/texlive/2026/texmf-dist/tex///
kfmt 33 1 0 .vf - .:/root/.texlive2026/texmf-config/fonts/vf//:/root/.texlive2026/texmf-var/fonts/vf//:/root/texmf/fonts/vf//:!!/usr/local/texlive/texmf-local/fonts/vf//:!!/usr/local/texlive/2026/texmf-config/fonts/vf//:!!/usr/local/texlive/2026/texmf-var/fonts/vf//:!!/usr/local/texlive/2026/texmf-dist/fonts/vf//
# the file-system snapshot of the TeX tree the searches reach (snapshot.py measure, in the
# pinned image; @sha256: bytes copied out of the image, fetched again by diff.py prepare; an
# ARCH: prefix marks a line of one architecture's image: measured with snapshot.py --arch, the
# two images agree on every entry here except texmf-var/ls-R's order)
fslist /root=.bashrc/.profile/.ssh
fslist /usr/local/texlive/texmf-local=bibtex/doc/dvips/fonts/metapost/tex/tlpkg/web2c
fslist /usr/local/texlive/2026/texmf-config=ls-R
fslist /usr/local/texlive/2026/texmf-var=fonts/ls-R/luametatex-cache/luatex-cache/tex/web2c/xdvi
fslist /usr/local/texlive/2026/texmf-dist=asymptote/bibtex/chktex/doc/dvipdfmx/dvips/fonts/hbf2gf/ls-R/makeindex/metafont/metapost/mft/omega/pbibtex/psutils/scripts/source/tex/tex4ht/texconfig/texdoc/texdoctk/ttf2pk/web2c/xdvi/xindy
fsfile /usr/local/texlive/2026/texmf-config/ls-R=@sha256:418d569540155c83d3e01fb88cf8ecbf5870deedc3844f86d38df2f9b4d4f5b2
arm64:fsfile /usr/local/texlive/2026/texmf-var/ls-R=@sha256:4f37062f1d9cc50f4cc6c7e3124f83be392e116678e2902ef78dd61639f00323
amd64:fsfile /usr/local/texlive/2026/texmf-var/ls-R=@sha256:af3ce41c0a8a7be40c03c50dea2ec5461aefe08e8106a92b1e85c04e2fbda113
fsfile /usr/local/texlive/2026/texmf-dist/ls-R=@sha256:fd6d012967e7eb1702f3475cfd336dffac1d7f01d701b34c13a1e47dcc52f548
fsfile /usr/local/texlive/2026/texmf-dist/tex/plain/knuth-lib/story.tex=@sha256:592939f339e78d7faca19c75017ec338db7c9efdea085c4374e5b13909cc8ec6
fsfile /usr/local/texlive/2026/texmf-dist/fonts/map/fontname/texfonts.map=@sha256:d9693993efdc7d0b9ab3df777589995d43e24eeae95f12b6a230a19caadeaa42
fsfile /usr/local/texlive/2026/texmf-dist/fonts/tfm/public/cm/cmr10.tfm=@sha256:87f2d8981927644cbecaf3d639e96e348ea4e7be49d8804468bd8ba9ff3f5244
fsfile /usr/local/texlive/2026/texmf-dist/fonts/tfm/public/cm/cmbx10.tfm=@sha256:ae296e8e41b2b0f73e9a17fdc42c743b9ddcc58d23c30acaa3411206f7824780
fsfile /usr/local/texlive/2026/texmf-dist/fonts/tfm/public/cm/cmti10.tfm=@sha256:46a66e937f809c4fbe317947b583a14b408aca41ecb835eca3be46391190432a
fsfile /usr/local/texlive/2026/texmf-dist/fonts/tfm/public/cm/cmsy10.tfm=@sha256:0ca13d421ac7133271aed7c935099ecf3d1d08ac9e15f81acb34a16564ab8a46
fsfile /usr/local/texlive/2026/texmf-dist/fonts/tfm/public/cm/cmtt10.tfm=@sha256:11f3331c958b696fd484fe45c28285622617a2593d7a34511a1d6b279e1578a2
fsfile /usr/local/texlive/2026/texmf-dist/fonts/tfm/public/cm/cmmi10.tfm=@sha256:e442c5487f84df70218ff37f775c87060856f5b6e04c011b6cadbbadfcf46645
# gettimeofday readings, in call order (the clock shim gives the binary the same).
clock 1788076260 123456
clock 1788076261 373456
clock 1788076262 623456
clock 1788076263 873456
clock 1788076264 123456
clock 1788076265 373456
clock 1788076266 623456
clock 1788076267 873456

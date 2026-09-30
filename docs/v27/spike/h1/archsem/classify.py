#!/usr/bin/env python3
"""Write classification.tsv: one verdict per site of census_sites.tsv.
Verdicts:
  SAFE-CONST      divisor is a nonzero constant (or a table of them)
  SAFE-GUARD      a test before the division excludes 0, and INT_MIN / -1
  SAFE-SIGN       cannot trap: the divisor is made positive first (negation); the
                  only non-positive value it can then have is INT_MIN, which never
                  traps. NOT a claim about signed overflow: negating an INT_MIN
                  operand (reachable, \\advance does not check overflow) is C UB
                  that the two compilers may compile differently (x_over_n does);
                  for these sites probe nh-intmin measured equal results
  SAFE-CALLERS    every call site passes a positive constant or a checked value
  SAFE-RANGE      the converted value is finite and inside int range (bound given)
  DIVERGES        an adversarial document gives different results (probe named)
  OUTPUT-ONLY     the result reaches only PDF bytes (never TeX state, log or rc);
                  arch-dependent values there change the PDF only
  NOT-REACHED     not reached by a pdfTeX run of a document (statistics, API unused)
  OPEN            not settled; the channel it could reach is stated
Every census site must have exactly one row (verify_h1.py checks it)."""
import csv
V = {}
def s(site, cls, verdict, why):
    assert (cls, site) not in V, site
    V[(cls, site)] = (verdict, why)
D, F = 'DIV', 'F2I'
# ---------------- kpathsea / zlib
s('hash.c:44', D, 'SAFE-CONST', 'modulo table.size, fixed positive per hash table')
s('hash.c:245', D, 'NOT-REACHED', 'hash_print statistics, debug output only')
for l in ('57', '58', '65', '68'):
    s(f'tex-make.c:{l}', D, 'OPEN', 'mktex magnification string dpi/bdpi; bdpi is the base resolution kpathsea was initialised with (pdfTeX: \\pdfpkresolution, fix_int-ed); not traced to a nonzero proof. Reaches the mktexpk command line, so a generated font and the log')
for l in ('458', '464'):
    s(f'gzread.c:{l}', D, 'NOT-REACHED', 'gzfread: pdfTeX never calls it (SyncTeX writes with gzprintf); also guarded by len != 0')
for l in ('297', '303'):
    s(f'gzwrite.c:{l}', D, 'NOT-REACHED', 'gzfwrite: pdfTeX never calls it; also guarded by len != 0')
s('magstep.c:60', F, 'SAFE-RANGE', 'dpi and bdpi are small positive resolutions; bdpi*t or bdpi/t with t a magstep factor stays far inside int range')
for l in ('132', '354', '355', '356'):
    s(f'tex-glyph.c:{l}', F, 'SAFE-RANGE', 'KPSE_BITMAP_TOLERANCE(dpi) = dpi/500.0 + 1 for an unsigned dpi: < 2^23')
# ---------------- the TeX program (pdftex0.c / pdftexini.c, from pdftex.web)
s('pdftex0.c:1176', D, 'SAFE-CONST', 'print_roman_int: divisor is a digit of the constant string "m2d5c2l5x2v5i" minus 48: 2 or 5')
s('pdftex0.c:1180', D, 'SAFE-CONST', 'print_roman_int, as line 1176')
s('pdftex0.c:12698', D, 'SAFE-GUARD', 'scan_dimen "true": divisor \\mag, after prepare_mag forces 1 <= mag <= 32768 and only when mag <> 1000')
s('pdftex0.c:12776', D, 'SAFE-CONST', 'scan_dimen: denom from the unit table (constants)')
s('pdftex0.c:12918', D, 'SAFE-SIGN', 'e-TeX quotient: d = 0 is an error first, then d is negated to positive')
for l in ('12961', '12962', '12968', '12969'):
    s(f'pdftex0.c:{l}', D, 'SAFE-SIGN', 'e-TeX fract: d = 0 goes to too_big, x = 0 and n = 0 exit before their divisions, all three are negated to positive first')
for l in ('1333', '1334'):
    s(f'pdftex0.c:{l}', D, 'SAFE-SIGN', 'mult_and_add (nx_plus_y): n = 0 returns 0, n < 0 is negated before (max_answer -/+ y) div n')
for l in ('1363', '1365', '1370', '1371'):
    s(f'pdftex0.c:{l}', D, 'DIVERGES', 'x_over_n: the division itself cannot trap (n = 0 is an error first, n is negated), but negating x = INT_MIN is C signed overflow (UB) and the two compilers exploit it differently: aarch64 gcc 10 emits udiv for (-x) div n, x86_64 gcc 11 emits idiv of x by n. \\divide of INT_MIN by INT_MIN gives -1 on aarch64 and 1 on x86_64 (probe nh-intmin, divself)')
for l in ('1393', '1395', '1396', '1400'):
    s(f'pdftex0.c:{l}', D, 'SAFE-CALLERS', 'xn_over_d: every call site passes d = 65536, 1000, a unit-table denominator, or \\mag after prepare_mag (1..32768)')
for l in ('1421', '1423'):
    s(f'pdftex0.c:{l}', D, 'SAFE-GUARD', 'badness: s <= 0 returns inf_bad first; s div 297 >= 5601 in the branch that divides by it')
s('pdftex0.c:1456', D, 'SAFE-CALLERS', 'make_frac: its only caller (norm_rand) loops until u <> 0 before make_frac(x, u); a zero q would reach p div 0 (the q = 0 test is TEXMF_DEBUG only)')
s('pdftex0.c:1515', D, 'SAFE-GUARD', 'take_frac: n = f div 2^28 >= 1 in the branch that divides 2147483647 by it')
s('pdftex0.c:1589', D, 'SAFE-CONST', 'm_log: divisor two_to_the[k], a power of two')
for l in ('16157', '16470'):
    s(f'pdftex0.c:{l}', D, 'SAFE-CONST', 'read_font_info: tfm_temp div 16')
for l in ('16279', '16293', '16389', '16482', '16590', '16613'):
    s(f'pdftex0.c:{l}', D, 'SAFE-GUARD', 'store_scaled: alpha = 16 doubled while z >= 2^23, and z < 2^27 (an at-size >= 2048pt is refused), so alpha <= 256 and beta = 256 div alpha >= 1')
for l in ('1675', '1676'):
    s(f'pdftex0.c:{l}', D, 'SAFE-GUARD', "ab_vs_cd (METAFONT's): zero and negative b, d are handled before the loop; in the loop all four are positive")
for l in ('18127', '18134', '18140', '18498', '18505', '18511', '24298', '24305', '24311', '24726', '24733', '24739'):
    s(f'pdftex0.c:{l}', D, 'SAFE-GUARD', 'leaders in (pdf_)hlist_out/vlist_out: guarded by leader_wd > 0 (leader_ht > 0); lq + 1 >= 1 because rule_wd <= 2^30 + 10^9 (vet_glue clamps the glue) < INT_MAX')
for l in ('19565', '19566'):
    s(f'pdftex0.c:{l}', D, 'SAFE-CONST', 'pdf_print_real: ten_pow[d] for a digit count d in 0..9')
s('pdftex0.c:21230', D, 'SAFE-GUARD', 'fix_expand_value: e = 0 returns first; step = pdf_font_step[f] >= 1, set only by read_expand_font after fix_int(.,0,100) and a zero test that is a pdf_error')
for l in ('21329', '21332'):
    s(f'pdftex0.c:{l}', D, 'SAFE-GUARD', 'read_expand_font: font_step = fix_int(cur_val, 0, 100) and font_step = 0 is a pdf_error before the modulo')
for l in ('21430', '21441', '21442', '21449', '21457'):
    s(f'pdftex0.c:{l}', D, 'SAFE-GUARD', 'letter_space_font: the store_scaled idiom (beta >= 1) and vf_z = font_size[f] > 0 (a non-positive at-size is refused by TeX)')
s('pdftex0.c:23709', D, 'DIVERGES', 'gap_amount divides by the \\pdfsnapy glue width, which new_snap_node only requires to be >= 0: \\pdfsnapy 0pt makes x86_64 die with SIGFPE (rc 136) while aarch64 divides to 0 and exits 0 (probe snapy0)')
for l in ('2838', '2839', '2842', '2851'):
    s(f'pdftex0.c:{l}', D, 'SAFE-GUARD', 'divide_scaled: m = 0 and m >= 2^31/10 are pdf_error (fatal) before the division; m is negated to positive first; ten_pow[dd] constant')
for l in ('2870', '2873', '2874', '2875'):
    s(f'pdftex0.c:{l}', D, 'SAFE-CALLERS', 'round_xn_over_d: every call site passes d = 1000, 10000, 2000, 1000 + pdf_cur_Tm_a (>= 500: the expansion ratio is fix_int-ed to -500..1000), or a font step (>= 1)')
s('pdftex0.c:2891', D, 'SAFE-CONST', 'is_bit_set: m = 2^(s-1), its only caller passes s = 1')
for l in ('30424', '30425', '30435'):
    s(f'pdftex0.c:{l}', D, 'OPEN', 'try_break with font expansion: max_stretch_ratio div cur_font_step is >= 1 when a stretch font exists (ratio is a multiple of the step, both checked equal across fonts by check_expand_pars), and the branch needs a positive stretch sum; not machine-checked. A zero divisor would trap on x86_64 only (rc)')
for l in ('9032', '9044', '91'):
    s(f'pdftex0.c:{l}', D, 'SAFE-CONST', 'modulo error_line, a positive texmf.cnf constant fixed for the run')
s('pdftexini.c:2334', D, 'SAFE-CONST', 'prefixed_command: cur_chr is a prefix code 1, 2, 4 or 8')
for l in ('2569', '2571'):
    s(f'pdftexini.c:{l}', D, 'SAFE-CONST', 'encTeX mubyte table: modulo 128')
s('pdftexini.c:5661', D, 'SAFE-CONST', 'random_seed: epoch_seconds mod 1000000')
s('pdftexini.c:793', D, 'SAFE-CONST', 'trie_node hash: modulo trie_size, a positive texmf.cnf constant')
for l in ('1295', '1299', '1703', '1707', '1732', '1840', '1848', '1878', '1886', '1922', '1930', '1954', '1962', '2043',
          '2063', '2069', '2090', '2096', '2117', '2122', '2142', '2145', '2163', '2167'):
    s(f'synctex.c:{l}', D, 'OPEN', 'SyncTeX records divide positions by synctex_ctxt.unit, derived from \\mag at the first record; not traced to a nonzero proof. Reaches only the .synctex(.gz) file, and rc if it traps')
for l in ('347', '348'):
    s(f'utils.c:{l}', D, 'SAFE-CONST', 'getresnameprefix: modulo a constant base')
for l in ('218', '222'):
    s(f'writejpg.c:{l}', D, 'DIVERGES', 'read_APP1_Exif: num / den of an Exif RATIONAL, den = 0 guarded but INT_MIN / -1 is not: x86_64 SIGFPE (rc 136), aarch64 INT_MIN then "invalid image dimensions" (rc 1) (probe jpgdiv; review round 2)')
for l in ('209', '211', '441', '445'):
    s(f'writettf.c:{l}', D, 'OPEN', "ttf_funit divides by the font's unitsPerEm (head table), not checked for 0: a TrueType font file supplied with the document can make x86_64 trap (rc) where aarch64 gets 0; no probe built")
# ---------------- float -> int
for l in ('37', '39'):
    s(f'zround.c:{l}', F, 'SAFE-RANGE', "TeX's round(): r > INT_MAX and r < -INT_MAX are clamped; only NaN reaches the conversion out of range. Every TeX-program argument is a sum of products of finite doubles of magnitude < 2^62 (glue ratios are int/int with a nonzero divisor), so never NaN. C callers: bp2int of an included PDF's box (a NaN width makes both architectures refuse the image: probe pdfboxnan, rc 1 on both)")
s('texmfmp.c:3499', F, 'SAFE-RANGE', 'makecstring: 0.2 * a buffer size < 2^31')
for l in ('19110', '2525', '2903', '2922'):
    s(f'pdftex0.c:{l}', F, 'SAFE-RANGE', '0.2 * an array size < 2^31 (growth increments)')
for l in ('20230', '20255'):
    s(f'pdftex0.c:{l}', F, 'SAFE-RANGE', 'pdf_set_rule: (h + 1) / 2.0 of a rule dimension |h| < 2^30')
for l in ('3523', '3525'):
    s(f'pdftex0.c:{l}', F, 'SAFE-RANGE', 'get_micro_interval (\\pdfelapsedtime): elapsed seconds > 32767 return INT_MAX first, so the value is < 2^31. Clock-dependent anyway (R-CLOCK)')
for l in ('1496', '1497'):
    s(f'utils.c:{l}', F, 'DIVERGES', 'do_matrixtransform: DO_ROUND of a NaN or out-of-range coordinate from \\pdfsetmatrix; link /Rect [0 0 0 0] on aarch64, [32645.579 ...] on x86_64 (probe matnan; review round 2). OUTPUT-ONLY: the rectangle is written to the PDF and read by nothing in TeX')
for l in ('405', '406'):
    s(f'utils.c:{l}', F, 'DIVERGES', 'ext_xn_over_d only WARNS "number too big" and converts anyway: a 40000x8 px JPEG with no resolution gets width INT_MAX on aarch64 ("Huge page cannot be shipped out", rc 1) and INT_MIN on x86_64 (\\wd = -32768pt, rc 0) (probe imgwide)')
s('mapfile.c:487', F, 'DIVERGES', 'SlantFont * 1000 from a map line (\\pdfmapline or a .map file) converted to integer, then abs(slant) > 1000 rejects it; INT_MIN passes that test (abs(INT_MIN) = INT_MIN). See probes slanthuge, slantnan')
s('mapfile.c:491', F, 'OPEN', 'ExtendFont * 1000, as SlantFont (mapfile.c:487): same conversion, not probed separately')
s('writefont.c:114', F, 'OUTPUT-ONLY', 'the font descriptor ItalicAngle, from the slant')
s('writeimg.c:322', F, 'SAFE-RANGE', 'epdf_rotate (xpdf page rotation, an int multiple of 90 read from /Rotate; the conversion is xpdf-side)')
for l in ('798', '799'):
    s(f'writejbig2.c:{l}', F, 'SAFE-RANGE', 'xres * 0.0254 + 0.5 for an unsigned 32-bit xres: < 1.1e8 (and exhaustively FMA-safe: fma/jbig2_exhaustive.py)')
for l in ('236', '237'):
    s(f'writejpg.c:{l}', F, 'DIVERGES', 'read_APP1_Exif: (int)(xres * res_unit) with xres up to 2^31 and res_unit 2.54: XResolution 2000000000/1 cm gives INT_MAX on aarch64 (warning, rc 0) and INT_MIN on x86_64 ("invalid image dimensions", rc 1) (probe jpgconv; review round 2)')
for l in ('274', '275'):
    s(f'writejpg.c:{l}', F, 'SAFE-RANGE', 'JFIF density (16-bit) * 2.54 < 2^18')
for l in ('436', '681', '728', '734', '744', '970', '1427', '1643'):
    s(f'writet1.c:{l}', F, 'OPEN', "t1_scan_num returns a float parsed from the Type 1 font file (charstring and subr lengths, lenIV, font dimensions); a font file shipped with the document can make it out of range. Lengths steer the font parser (errors reach rc); dimensions reach the PDF only. No probe built")
for l in ('137', '169', '170', '225', '375', '379'):
    s(f'writet3.c:{l}', F, 'OUTPUT-ONLY', 'Type 3 (PK) font: glyph widths and bounding boxes written to the PDF')
s('writettf.c:484', F, 'OUTPUT-ONLY', 'TrueType ItalicAngle into the font descriptor')
# ---------------- libraries, grouped
LIBPNG = ('OPEN', 'libpng: pixel, gamma and text-chunk arithmetic. pdfTeX reads the header with png_read_info (dimensions and resolution are computed by pdfTeX itself, writepng.c) and the pixels at shipout; these sites are on the pixel/gamma path (PDF bytes) or error paths (rc if one traps). Not traced one by one')
XPDF = ('OPEN', 'xpdf (C++, no line table): pdfTeX uses it to parse and copy included PDFs. A trap in parsing reaches rc; values reach TeX state only through the page box, rotation and page count (bp2int clamps the box, see zround.c). Not traced one by one')
rows = list(csv.DictReader(open('census_sites.tsv'), delimiter='\t'))
with open('classification.tsv', 'w') as o:
    o.write('class\tgroup\tsite\tverdict\treason\n')
    missing = []
    for r in rows:
        k = (r['class'], r['site'])
        if r['group'] == 'libpng':
            v = LIBPNG
        elif r['group'] == 'xpdf':
            v = XPDF
        else:
            v = V.pop(k, None)
        if v is None:
            missing.append(k); continue
        o.write(f"{r['class']}\t{r['group']}\t{r['site']}\t{v[0]}\t{v[1]}\n")
assert not missing, missing
assert not V, sorted(V)
import collections
c = collections.Counter()
for r in csv.DictReader(open('classification.tsv'), delimiter='\t'):
    c[(r['group'] in ('libpng', 'xpdf') and r['group'] or 'pdfTeX+kpathsea+zlib', r['verdict'])] += 1
for k in sorted(c): print(*k, c[k])

"""Adversarial probes for architecture-dependent C semantics in pdfTeX r78081.
Each probe is a plain-pdfTeX document (the `pdftex` format of the pinned image);
run.sh runs every *.tex with -halt-on-error and records rc + key log lines."""
import io, struct, zlib
from PIL import Image
w = lambda n, s: open(n, 'w').write(s)
# --- image dimension: ext_xn_over_d (utils.c:396-405) warns on overflow and converts anyway
b = io.BytesIO(); Image.new('L', (40000, 8), 128).save(b, 'JPEG'); j = b.getvalue()
# PIL writes JFIF density units 0 (aspect only) -> writejpg.c sets xres=yres=0 -> 7200 path
assert j[:4] == b'\xff\xd8\xff\xe0' and j[13] == 0, j[:20]
open('wide.jpg', 'wb').write(j)
w('imgwide.tex', r'\pdfoutput=1 \pdfximage{wide.jpg}\setbox0\hbox{\pdfrefximage\pdflastximage}'
  r'\message{[WD=\the\wd0][HT=\the\ht0]}\shipout\box0 \end' + '\n')
# --- NaN in a PDF page box: bp2int = zround(NaN); inf-inf from a 400-digit numeral
big = '9' * 400
def pdf(box):
    objs = [b'<< /Type /Catalog /Pages 2 0 R >>',
            b'<< /Type /Pages /Kids [3 0 R] /Count 1 >>',
            ('<< /Type /Page /Parent 2 0 R /MediaBox %s /Contents 4 0 R /Resources << >> >>' % box).encode(),
            b'<< /Length 0 >>\nstream\n\nendstream']
    out = b'%PDF-1.4\n'; offs = []
    for i, o in enumerate(objs, 1):
        offs.append(len(out)); out += b'%d 0 obj\n' % i + o + b'\nendobj\n'
    x = len(out)
    out += b'xref\n0 %d\n0000000000 65535 f \n' % (len(objs) + 1)
    for o in offs: out += b'%010d 00000 n \n' % o
    out += b'trailer\n<< /Size %d /Root 1 0 R >>\nstartxref\n%d\n%%%%EOF\n' % (len(objs) + 1, x)
    return out
open('boxnan.pdf', 'wb').write(pdf('[%s 0 %s 100]' % (big, big)))   # width = inf - inf
open('boxinf.pdf', 'wb').write(pdf('[0 0 %s 100]' % big))            # width = inf (clamped by zround)
for n in ('boxnan', 'boxinf'):
    w(f'pdf{n}.tex', r'\pdfoutput=1 \pdfximage{%s.pdf}\setbox0\hbox{\pdfrefximage\pdflastximage}'
      r'\message{[WD=\the\wd0][HT=\the\ht0]}\shipout\box0 \end' % n + '\n')
# --- \pdfsnapy with a zero-width snap glue: gap_amount divides by snap_unit (pdftex0.c:23709)
w('snapy0.tex', r'\pdfoutput=1 \pdfsnaprefpoint \shipout\vbox{\hbox{a}\pdfsnapy 0pt\hbox{b}}\end' + '\n')
w('snapy1.tex', r'\pdfoutput=1 \pdfsnaprefpoint \shipout\vbox{\hbox{a}\pdfsnapy 1pt\hbox{b}}\end' + '\n')
# --- INT_MIN in an integer register (\advance does not check overflow), then every divider
w('nh-intmin.tex', r'''\catcode`\{=1 \catcode`\}=2 \pdfoutput=1
\count1=-2147483647 \advance\count1 by -1 \message{[c1=\the\count1]}
\count2=\count1 \divide\count2 by -1 \message{[div-1=\the\count2]}
\count3=\count1 \divide\count3 by \count1 \message{[divself=\the\count3]}
\dimen0=1sp \multiply\dimen0 by \count1 \message{[dmul=\the\dimen0]}
\dimen1=1pt \divide\dimen1 by \count1 \message{[ddiv=\the\dimen1]}
\message{[ne1=\the\numexpr\count1/-1\relax]}
\message{[ne2=\the\numexpr\count1*-1/1\relax]}
\message{[ne3=\the\numexpr\count1*3/7\relax]}
\message{[ne4=\the\numexpr 7*3/\count1\relax]}
\message{[de1=\the\dimexpr 1pt*\count1/-1\relax]}
\message{[de2=\the\dimexpr 1sp*-1/\count1\relax]}
\message{[rom=\romannumeral\count1 x]}
\message{[num=\number\count1]}
\count5=-2147483647 \advance\count5 by -2 \message{[wrap=\the\count5]}
\count6=\count1 \divide\count6 by 2 \message{[div2=\the\count6]}
\count7=\count1 \divide\count7 by 7 \message{[div7=\the\count7]}
\dimen2=16383.99998pt \divide\dimen2 by \count1 \message{[dd2=\the\dimen2]}
\message{[ne5=\the\numexpr\count1/\count1\relax]}
\message{[ne6=\the\numexpr\count1/2\relax]}
\message{[ne7=\the\numexpr(\count1)\relax]}
\count8=\count1 \multiply\count8 by -1 \message{[mul-1=\the\count8]}
\shipout\hbox{x}\end
''')
# --- plain char is unsigned on aarch64, signed on x86_64: every string primitive whose
#     C code changed under -fsigned-char (utils.c escapestring/escapehex/escapename,
#     \pdfstrcmp, \pdfmdfivesum), swept over all 255 non-null bytes
L = [r'\catcode`\{=1 \catcode`\}=2 \catcode`\#=6 \pdfoutput=1 \newlinechar=-1']
for c in range(1, 256):
    h = '%02X' % c
    L.append(r'\edef\x{\pdfunescapehex{%s}}\message{[%s:s=\pdfescapestring{\x}:n=\pdfescapename{\x}'
             r':h=\pdfescapehex{\x}:c=\pdfstrcmp{\x}{A}\pdfstrcmp{\x}{\pdfunescapehex{80}}\pdfstrcmp{\x}{\pdfunescapehex{FF}}'
             r':m=\pdfmdfivesum{\x}]}' % (h, h))
L.append(r'\shipout\hbox{}\end')
w('nh-strings.tex', '\n'.join(L) + '\n')
# --- map-file SlantFont: mapfile.c:487 converts float*1000 to integer, then
#     `abs(fm->slant) > 1000` rejects it (abs(INT_MIN) is INT_MIN on both, so a
#     conversion that yields INT_MIN passes the check)
for n, v in (('ctl', '0.167'), ('huge', '1e30'), ('nan', 'nan')):
    w(f'slant{n}.tex', r'\pdfoutput=1 \pdfmapline{=cmr10 CMR10 " %s SlantFont " <cmr10.pfb}'
      r'\font\x=cmr10 \shipout\hbox{\x Hello}\end' % v + '\n')

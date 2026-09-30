"""Independent generator (not the reviewer's mk.py): JPEGs whose Exif APP1 carries
XResolution = num/den and ResolutionUnit = unit, little-endian ('II') TIFF.
Cases target writejpg.c read_APP1_Exif (r78081 lines 216-237):
  xres = num / den      (int / int: x86 idiv traps on INT_MIN / -1)
  *xx  = (int)(xres * res_unit)   (double -> int: out of range differs by ISA)"""
import io, struct, hashlib
from PIL import Image
b = io.BytesIO(); Image.new('L', (4, 4), 128).save(b, 'JPEG'); j = b.getvalue()
assert j[:4] == b'\xff\xd8\xff\xe0'
body = j[4 + struct.unpack('>H', j[4:6])[0]:]          # drop the JFIF APP0 segment
def app1(num, den, unit):
    n = 2
    ifd = struct.pack('<H', n)
    off_rat = 8 + 2 + 12 * n + 4
    ifd += struct.pack('<HHII', 282, 5, 1, off_rat)      # XResolution, RATIONAL
    ifd += struct.pack('<HHIHH', 296, 3, 1, unit, 0)     # ResolutionUnit, SHORT
    ifd += struct.pack('<I', 0)
    tiff = b'II' + struct.pack('<HI', 42, 8) + ifd + struct.pack('<II', num & 0xffffffff, den & 0xffffffff)
    seg = b'Exif\x00\x00' + tiff
    return b'\xff\xe1' + struct.pack('>H', len(seg) + 2) + seg
cases = {
  'ctrl':   (300, 1, 2),                 # 300 dpi: in range everywhere
  'big':    (100000, 1, 2),              # > 65535, in int range: warning on both
  'conv':   (2000000000, 1, 3),          # 2e9 px/cm * 2.54 = 5.08e9 > INT_MAX
  'convneg':(-2000000000, 1, 3),         # -5.08e9 < INT_MIN: both negative
  'div':    (-2**31, -1, 2),             # INT_MIN / -1
}
for name, (n, d, u) in cases.items():
    data = b'\xff\xd8' + app1(n, d, u) + body
    open(name + '.jpg', 'wb').write(data)
    open(name + '.tex', 'w').write('\\pdfoutput=1 \\pdfximage{%s.jpg}\\setbox0\\hbox{\\pdfrefximage\\pdflastximage}'
        '\\message{[WD=\\the\\wd0]}\\shipout\\box0 \\end\n' % name)
    print(name, hashlib.sha256(data).hexdigest()[:16])

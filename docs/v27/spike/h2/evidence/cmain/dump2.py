# gdb -batch -x dump.py: at mainbody entry, every web2c global's bytes
import gdb, json
names = [l.strip() for l in open('/w/globals2.txt') if l.strip()]
gdb.execute('set pagination off')
gdb.execute('break mainbody')
gdb.execute('run')
inf = gdb.selected_inferior()
out = {}
for n in names:
    try:
        v = gdb.parse_and_eval(n)
    except gdb.error as e:
        out[n] = {'error': str(e)}
        continue
    t = v.type.strip_typedefs()
    size = t.sizeof
    try:
        addr = int(v.address)
        raw = bytes(inf.read_memory(addr, size))
    except Exception as e:
        out[n] = {'error': 'read: ' + str(e), 'type': str(v.type)}
        continue
    rec = {'type': str(v.type), 'code': int(t.code), 'size': size, 'nonzero': any(raw)}
    if any(raw):
        rec['hex'] = raw.hex() if size <= 64 else None
        if t.code == gdb.TYPE_CODE_PTR:
            p = int(v)
            rec['ptr'] = p
            if p:
                try:
                    tt = t.target().strip_typedefs()
                    if tt.sizeof == 1:
                        s = inf.read_memory(p, 4096).tobytes()
                        rec['cstring'] = s.split(b'\0')[0].decode('latin-1')
                except Exception as e:
                    rec['cstring_err'] = str(e)
        elif size > 64:
            nz = [i for i, b in enumerate(raw) if b]
            rec['nonzero_bytes'] = len(nz)
            rec['first_nonzero'] = nz[:16]
    out[n] = rec
json.dump(out, open('/w/cmain_globals2.json', 'w'), indent=1)
print('dumped', len(out))
gdb.execute('kill')

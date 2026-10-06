# gdb -batch -x dump3.py: at mainbody entry, every web2c global's bytes (globals.txt), the
# C-main statics of texmfmp.c/openclose.c the boundary reads, and kpathsea's program name
import gdb, json, os
names = [l.strip() for l in open('/m/globals.txt') if l.strip()]
statics = ["dump_name", "translate_filename", "'texmfmp.c'::c_job_name", "'texmfmp.c'::user_progname",
           "output_directory", "recorder_enabled", "kpse_def->program_name", "kpse_def->invocation_name",
           "optind", "'texmfmp.c'::argc", "fullnameoffile", "'texmfmp.c'::srcspecialsoption",
           "'texmfmp.c'::user_cnf_nlines", "outputcomment", "'texmfmp.c'::default_translate_filename"]
gdb.execute('set pagination off')
gdb.execute('break mainbody')
gdb.execute('run')
inf = gdb.selected_inferior()
def rec_of(n):
    try:
        v = gdb.parse_and_eval(n)
    except gdb.error as e:
        return {'error': str(e)}
    t = v.type.strip_typedefs()
    size = t.sizeof
    try:
        raw = bytes(inf.read_memory(int(v.address), size)) if v.address is not None else None
    except Exception as e:
        raw = None
    rec = {'type': str(v.type), 'size': size}
    if raw is not None:
        rec['nonzero'] = any(raw)
        if size <= 64:
            rec['hex'] = raw.hex()
        else:
            rec['nonzero_bytes'] = sum(1 for b in raw if b)
    try:
      if t.code == gdb.TYPE_CODE_PTR:
        p = int(v)
        rec['ptr_null'] = (p == 0)
        if p and t.target().strip_typedefs().sizeof == 1:
            rec['cstring'] = inf.read_memory(p, 4096).tobytes().split(b'\0')[0].decode('latin-1')
      elif t.code == gdb.TYPE_CODE_INT:
        rec['int'] = int(v)
    except gdb.error as e:
        rec['value_error'] = str(e)
    return rec
out = {n: rec_of(n) for n in names}
out['__statics__'] = {n: rec_of(n) for n in statics}
try:
    ac = int(gdb.parse_and_eval("'texmfmp.c'::argc"))
    out['__argv__'] = [gdb.parse_and_eval(f"'texmfmp.c'::argv[{i}]").string() for i in range(ac)]
except gdb.error as e:
    out['__argv__'] = 'error: ' + str(e)
json.dump(out, open(os.environ['DUMPOUT'], 'w'), indent=1, sort_keys=True)
print('dumped', len(out))
gdb.execute('kill')

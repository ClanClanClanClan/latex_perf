# gdb -batch -x measure.py: at mainbody, kpse_var_value of every name in /m/vars.txt and
# kpse_format_info of formats 3 9 10 11 26 33 after kpathsea_init_format
import gdb, os
gdb.execute('set pagination off')
gdb.execute('set print elements 0')
gdb.execute('break mainbody')
gdb.execute('run')
out = open(os.environ['MOUT'], 'w')
out.write('PROGNAME %s\n' % gdb.parse_and_eval('kpse_def->program_name').string())
out.write('INVOCATION %s\n' % gdb.parse_and_eval('kpse_def->invocation_name').string())
for n in [l.strip() for l in open('/m/vars.txt') if l.strip()]:
    v = gdb.parse_and_eval('(char*) kpathsea_var_value(kpse_def, "%s")' % n)
    out.write(('kpse %s=%s\n' % (n, v.string())) if int(v) != 0 else ('# %s is NULL\n' % n))
for f in (3, 9, 10, 11, 26, 33):
    gdb.parse_and_eval('(char*) kpathsea_init_format(kpse_def, %d)' % f)
    fi = 'kpse_def->format_info[%d]' % f
    def lst(field):
        p = gdb.parse_and_eval(fi + '.' + field)
        r, i = [], 0
        if int(p) == 0:
            return '-'
        while int(p[i]) != 0:
            r.append(p[i].string()); i += 1
        return ','.join(r) if r else '-'
    prog = gdb.parse_and_eval(fi + '.program')
    mk = 1 if (int(prog) != 0 and int(gdb.parse_and_eval(fi + '.program_enabled_p')) != 0) else 0
    out.write('kfmt %d %d %d %s %s %s\n' % (f, int(gdb.parse_and_eval(fi + '.suffix_search_only')), mk,
              lst('suffix'), lst('alt_suffix'), gdb.parse_and_eval(fi + '.path').string()))
out.close()
gdb.execute('kill')

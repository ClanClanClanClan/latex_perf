# gdb -batch -x funcs2.py: which functions of the pinned pdfTeX (reference build) run on one
# document: a temporary breakpoint on every text symbol of the binary (nm -S), one record per
# first hit with the caller (for the externals the translated program calls)
import gdb, json, os
gdb.execute('set pagination off')
gdb.execute('set confirm off')
syms = []
for line in open('/m/nm.txt'):
    a, sz, t, name = line.split(None, 3)
    syms.append(name.strip())
n = 0
for s in syms:
    try:
        gdb.execute(f"tbreak *'{s}'", to_string=True); n += 1
    except gdb.error:
        pass
hits = []
def stop_handler(ev):
    if not isinstance(ev, gdb.BreakpointEvent):
        return
    fr = gdb.newest_frame()
    caller = fr.older()
    cs = caller.find_sal() if caller else None
    hits.append({'fn': fr.name(), 'pc': int(fr.pc()),
                 'file': (fr.find_sal().symtab.filename if fr.find_sal().symtab else None),
                 'caller': caller.name() if caller else None,
                 'caller_file': (cs.symtab.filename if (cs and cs.symtab) else None)})
gdb.events.stop.connect(stop_handler)
gdb.execute('run')
while True:
    try:
        gdb.execute('continue')
    except gdb.error:
        break
json.dump({'breakpoints': n, 'symbols': len(syms), 'hits': hits}, open(os.environ['FOUT'], 'w'), indent=0)

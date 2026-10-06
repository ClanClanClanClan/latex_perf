# gdb -batch -x counts.py: how often each C function the translated program calls directly
# (entry.txt, from funcs2.py's first hits) is entered, before and after the first
# pdfshipoutbegin (the start of PDF output)
import gdb, json, os
gdb.execute('set pagination off')
names = [l.strip() for l in open('/m/entry.txt') if l.strip()]
bps = {}
for n in names:
    bps[n] = gdb.Breakpoint(n, internal=False)
    bps[n].silent = True
counts = {n: [0, 0] for n in names}
phase = [0]
def stop(ev):
    if isinstance(ev, gdb.BreakpointEvent):
        for b in ev.breakpoints:
            n = b.location
            if n == 'pdfshipoutbegin' and phase[0] == 0:
                phase[0] = 1
            if n in counts:
                counts[n][phase[0]] += 1
gdb.events.stop.connect(stop)
gdb.execute('run')
while True:
    try:
        gdb.execute('continue')
    except gdb.error:
        break
json.dump(counts, open(os.environ['FOUT'], 'w'), indent=1, sort_keys=True)

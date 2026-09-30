#!/usr/bin/env python3
"""H.1 comparison of two engine runs recorded by h1cmp.py.

usage:
  h1diff.py SET ARCH                      pinned vs ref, same arch
  h1diff.py SET --cross A:ENG B:ENG       e.g. arm64:pinned amd64:pinned

Per document, per pass: rc, timed_out, the set of files written, and every
file's bytes, plus the terminal output. A difference is first sought RAW; only
if the raw bytes differ are the documented masks applied (log/stdout: the
banner line's date and time; PDF: /ID, /CreationDate, /ModDate) and the result
labelled EQUAL_MASKED with the mask that was needed. Anything else is DIFF,
with the first differing line/byte recorded. Nothing is dropped: a document
with an error on either side is counted as ERROR, never as agreement.
"""
import json
import re
import sys
from collections import Counter
from pathlib import Path

W = Path.home() / ".cache/lp-spike-h1"
SET = sys.argv[1]
SET_A = SET_B = SET
if sys.argv[2] == "--cross":
    # each side is ARCH:ENGINE, or SETDIR/ARCH:ENGINE to compare two run sets
    sides = []
    for x in sys.argv[3:5]:
        loc, eng = x.split(":")
        st, _, arch = loc.rpartition("/")
        sides.append((st or SET, arch, eng))
    (SET_A, a_arch, a_eng), (SET_B, b_arch, b_eng) = sides
else:
    a_arch = b_arch = sys.argv[2]
    a_eng, b_eng = "pinned", "ref"
RA = W / "runs" / SET_A / a_arch
RB = W / "runs" / SET_B / b_arch

BANNER = re.compile(rb"^(This is pdfTeX, Version [^\n]*?\))  \d{1,2} [A-Z]{3} \d{4} \d{2}:\d{2}", re.M)
PDF_MASKS = [re.compile(rb"/ID \[<[0-9A-Fa-f]+> <[0-9A-Fa-f]+>\]"),
             re.compile(rb"/CreationDate \([^)]*\)"), re.compile(rb"/ModDate \([^)]*\)")]


# The per-run work directory (the oracle's mkdtemp under the work root, which
# also holds the run's private TEXMFVAR where mktexpk/mktextfm write generated
# fonts) is printed in logs and terminal output. Its name is random per run and
# its root differs per architecture; both spellings have the same length, so
# line wrapping is unaffected. It is masked EXACTLY: the run's own directory,
# recorded as `td` in result.json, with a line break allowed between any two
# characters (TeX and the terminal wrap long paths).
def td_regex(td: str):
    return re.compile(b"\n?".join(re.escape(bytes([c])) for c in td.encode()))


# An emulated (qemu-user) architecture can crash a helper process. The shell
# that ran it prints this line on the terminal; it is counted, never hidden
# silently (mask "emulator-segv-line").
SEGV = re.compile(rb"^Segmentation fault \(core dumped\)\n", re.M)


# Run-dependent inputs outside pdfTeX's arithmetic, each masked only when
# needed and always counted:
#  * epstopdf logs the converted file's modification time, read through
#    \pdffilemoddate, which follows the real clock even with FORCE_SOURCE_DATE
#    (the #625 review): mask "pdffilemoddate-line".
#  * Ghostscript (repstopdf, restricted \write18) names each font subset with a
#    6-letter tag that differs from run to run; the tag sits inside Flate
#    streams, and pdfTeX copies the converted PDF into the document's PDF, so
#    the document's compressed streams, their /Length and the xref differ.
#    Mask "pdf-canonical-subset-tag": every Flate stream decompressed (a
#    stream with bytes after its zlib end, or a truncated one, keeps those
#    facts in the canonical form, so they still compare), /Length values
#    masked, the xref stream DECODED row by row with only the byte offset of a
#    type-1 entry dropped (entry types, generations, object-stream numbers and
#    indices are compared), classic xref entries' offsets and startxref (byte
#    offsets, which follow the compressed lengths) dropped, and ONLY the
#    /XXXXXX+ subset tags that occur in that side's own Ghostscript
#    intermediates (files named *-eps-converted-to.pdf written in the same run)
#    replaced. pdfTeX's own subset tags, /Size, /W and /Index are still
#    compared (review round 1 of the spike: the first version replaced every
#    tag and dropped /Size, /W and /Index, which would also have absorbed a
#    pdfTeX tag or object-count difference). Used only when the raw and the
#    id/date-masked bytes differ AND at least one side wrote a Ghostscript
#    intermediate: the mask's justification is Ghostscript, so without one it
#    is never engaged (review round 2: it had engaged on any PDF difference and
#    absorbed a zlib-level change, an xref entry-type change and trailing bytes
#    after a zlib end; kill-tests 6-11 of h1diff_selftest.py).
# The PDF's byte size printed by pdfTeX ("Output written on X (N pages, M
# bytes).") follows the compressed sizes; the PDF itself is compared on its
# own, so the size is masked when needed (mask "output-size"); pages are kept.
OUTSIZE = re.compile(rb"(Output written on [^\n]*?\(\d+ pages?, )\d+( bytes\))")
FILEMODDATE = re.compile(rb"(\(epstopdf\)\s+date: )\d{4}-\d\d-\d\d \d\d:\d\d:\d\d")
# epstopdf also logs the converted file's size (\pdffilesize of Ghostscript's
# output, whose compressed length follows the random subset tag): mask
# "converted-size-line".
CONVSIZE = re.compile(rb"(\(epstopdf\)\s+size: )\d+( bytes)")


GS_INTERMEDIATE = re.compile(r"-eps-converted-to\.pdf$")
TAG = re.compile(rb"/([A-Z]{6})\+")


def subset_tags(b: bytes) -> set:
    """Every /XXXXXX+ tag in a PDF, inside Flate streams included."""
    return {m.group(1) for m in TAG.finditer(pdf_canonical(b, frozenset()))}


def xref_rows(head: bytes, data: bytes) -> bytes:
    """Decode an XRef stream's rows (/W widths, optional PNG predictor with
    /Columns), keeping every field except the byte offset of a type-1 entry.
    Anything it cannot decode exactly is kept RAW, so it still compares."""
    w = re.search(rb"/W\s*\[\s*(\d+)\s+(\d+)\s+(\d+)\s*\]", head)
    if not w:
        return b"<xref-undecoded>" + data
    ws = [int(x) for x in w.groups()]
    n = sum(ws)
    pred = re.search(rb"/Predictor\s+(\d+)", head)
    if pred and int(pred.group(1)) >= 10:
        cols = re.search(rb"/Columns\s+(\d+)", head)
        if not cols or int(cols.group(1)) != n or len(data) % (n + 1):
            return b"<xref-undecoded>" + data
        rows, prev = [], bytes(n)
        for i in range(0, len(data), n + 1):
            f, r = data[i], bytearray(data[i + 1:i + 1 + n])
            if f == 2:
                r = bytearray((r[k] + prev[k]) & 0xFF for k in range(n))
            elif f != 0:
                return b"<xref-undecoded>" + data
            rows.append(bytes(r))
            prev = bytes(r)
    elif pred and int(pred.group(1)) != 1:
        return b"<xref-undecoded>" + data
    else:
        if n == 0 or len(data) % n:
            return b"<xref-undecoded>" + data
        rows = [data[i:i + n] for i in range(0, len(data), n)]
    out = []
    for r in rows:
        f = []
        k = 0
        for wd in ws:
            f.append(int.from_bytes(r[k:k + wd], "big") if wd else None)
            k += wd
        t = 1 if ws[0] == 0 else f[0]
        out.append(b"%d %s %d" % (t, b"<off>" if t == 1 else str(f[1]).encode(),
                                  -1 if f[2] is None else f[2]))
    return b"<xref-rows>" + b";".join(out)


def pdf_canonical(b: bytes, gs_tags=frozenset()) -> bytes:
    import zlib
    out = []
    pos = 0
    for m in re.finditer(rb"stream\r?\n", b):
        if m.start() < pos:
            continue
        end = b.find(b"endstream", m.end())
        if end < 0:
            break
        head = b[pos:m.start()]
        body = b[m.end():end]
        try:
            d = zlib.decompressobj()
            plain = d.decompress(body)
            tail = d.unused_data
            if tail in (b"\n", b"\r\n", b"\r"):
                tail = b""          # the EOL before `endstream`
            body = plain
            if not d.eof:
                body += b"<zlib-truncated>"
            if tail:
                body += b"<zlib-tail>" + tail
        except Exception:
            pass
        if b"/Type/XRef" in head[-400:] or b"/Type /XRef" in head[-400:]:
            dh = head[-400:]
            body = xref_rows(dh, body) if b"<zlib-" not in body else body
        out.append(head)
        out.append(b"stream\n" + body + b"\nendstream")
        pos = end + len(b"endstream")
    out.append(b[pos:])
    c = b"".join(out)
    c = re.sub(rb"/Length \d+", b"/Length <n>", c)
    c = re.sub(rb"startxref\s+\d+", b"startxref <n>", c)
    c = TAG.sub(lambda m: b"/<GS-SUBSET>+" if m.group(1) in gs_tags else m.group(0), c)
    c = re.sub(rb"\n\d{10} (\d{5} [nf]) ?", rb"\n<off> \1", c)
    return c


BIG = 20_000_000


def big_equal(name, bx, by, rxa, rxb):
    """Traced logs run to hundreds of MB. For two files of EQUAL length, find
    the differing byte positions (chunked), and require every one of them to
    vanish when a window around it (widened to whole lines, >= 400 bytes each
    side) is masked on both sides. Returns (equal, masks used, first bad line)."""
    if len(bx) != len(by):
        return None
    used = set()
    C = 1 << 16
    n = len(bx)
    i = 0
    while i < n:
        if bx[i:i + C] == by[i:i + C]:
            i += C
            continue
        j = i
        while j < min(n, i + C) and bx[j] == by[j]:
            j += 1
        lo = bx.rfind(b"\n", 0, max(0, j - 400)) + 1
        hi = bx.find(b"\n", min(n, j + 400))
        hi = n if hi < 0 else hi
        mx, hx = mask(name, bx[lo:hi], rxa)
        my, hy = mask(name, by[lo:hi], rxb)
        if mx != my:
            return (False, used, f"at byte {j} (file line {bx.count(b'\\n', 0, j) + 1}), window "
                    + first_diff(mx, my))
        used |= (set(hx.split("+")) | set(hy.split("+"))) - {"none"}
        i = hi
    return (True, used, "")


def needed_masks(name, bx, by, rxa, rxb, ga=frozenset(), gb=frozenset()) -> tuple[bool, list]:
    """Equal under all masks? And which masks were NEEDED: a mask is needed
    when switching it off alone makes the two sides differ."""
    on = frozenset()
    mx, hx = mask(name, bx, rxa)
    my, hy = mask(name, by, rxb)
    if mx != my and name.endswith(".pdf") and (ga or gb):
        on = frozenset({"pdf-canonical-subset-tag"})
        mx, hx = mask(name, bx, rxa, on=on, gs_tags=ga)
        my, hy = mask(name, by, rxb, on=on, gs_tags=gb)
    if mx != my:
        return False, []
    cand = sorted((set(hx.split("+")) | set(hy.split("+"))) - {"none", "pdf-canonical-subset-tag"})
    need = [m for m in cand
            if mask(name, bx, rxa, off={m}, on=on, gs_tags=ga)[0]
            != mask(name, by, rxb, off={m}, on=on, gs_tags=gb)[0]]
    return True, need + sorted(on)


def mask(name: str, b: bytes, td_rx, off=frozenset(), on=frozenset(),
         gs_tags=frozenset()) -> tuple[bytes, str]:
    hows = []
    if name.endswith(".gz") and "gunzip" not in off:
        # SyncTeX's .synctex.gz records the absolute work-directory path; the
        # comparison is made on the decompressed text (mask "gunzip").
        import gzip
        try:
            b = gzip.decompress(b)
            hows.append("gunzip")
        except Exception:
            pass
    b2 = td_rx.sub(b"<WORKDIR>", b) if "workdir-path" not in off else b
    if b2 != b:
        hows.append("workdir-path")
    b = b2
    if name == "__stdout" and "emulator-segv-line" not in off:
        b2 = SEGV.sub(b"", b)
        if b2 != b:
            hows.append("emulator-segv-line")
        b = b2
    if name.endswith(".pdf") and "pdf-id-dates" not in off:
        b2 = b
        for rx in PDF_MASKS:
            b2 = rx.sub(b"<masked>", b2)
        if b2 != b:
            hows.append("pdf-id-dates")
        b = b2
    if name.endswith(".pdf") and "pdf-canonical-subset-tag" in on:
        b = pdf_canonical(b, gs_tags)
        hows.append("pdf-canonical-subset-tag")
    if (name.endswith(".log") or name == "__stdout") and "pdffilemoddate-line" not in off:
        b2 = FILEMODDATE.sub(rb"\1<date>", b)
        if b2 != b:
            hows.append("pdffilemoddate-line")
        b = b2
    if (name.endswith(".log") or name == "__stdout") and "converted-size-line" not in off:
        b2 = CONVSIZE.sub(rb"\1<n>\2", b)
        if b2 != b:
            hows.append("converted-size-line")
        b = b2
    if (name.endswith(".log") or name == "__stdout") and "output-size" not in off:
        b2 = OUTSIZE.sub(rb"\1<M>\2", b)
        if b2 != b:
            hows.append("output-size")
        b = b2
    if (name.endswith(".log") or name == "__stdout") and "banner-date" not in off:
        b2 = BANNER.sub(rb"\1  <date>", b)
        if b2 != b:
            hows.append("banner-date")
        b = b2
    return b, "+".join(hows) or "none"


def first_diff(x: bytes, y: bytes) -> str:
    xl, yl = x.split(b"\n"), y.split(b"\n")
    for i, (p, q) in enumerate(zip(xl, yl)):
        if p != q:
            return f"line {i + 1}: {p[:120]!r} | {q[:120]!r}"
    return f"length {len(xl)} vs {len(yl)} lines"


def fname(rel: str) -> str:
    return rel.replace("/", "__")


def compare_doc(doc: str):
    ra = json.load(open(RA / doc / "result.json"))
    rb = json.load(open(RB / doc / "result.json"))
    a, b = ra.get(a_eng), rb.get(b_eng)
    if a is None or b is None or "error" in a or "error" in b:
        return "ERROR", [f"a={str(a)[:200]} b={str(b)[:200]}"], set()
    notes, masks = [], set()
    rxa, rxb = td_regex(a["td"]), td_regex(b["td"])
    pa, pb = a["passes"], b["passes"]

    def gs_tags_of(root, eng, passes):
        tags = set()
        for k, x in enumerate(passes, 1):
            for rel in x["files"]:
                if GS_INTERMEDIATE.search(rel):
                    tags |= subset_tags((root / doc / eng / f"p{k}" / fname(rel)).read_bytes())
        return frozenset(tags)
    ga, gb = gs_tags_of(RA, a_eng, pa), gs_tags_of(RB, b_eng, pb)
    if len(pa) != len(pb):
        notes.append(f"passes {len(pa)} vs {len(pb)}")
    for k, (x, y) in enumerate(zip(pa, pb), 1):
        if (x["rc"], x["timed_out"]) != (y["rc"], y["timed_out"]):
            notes.append(f"p{k} rc {x['rc']}/{x['timed_out']} vs {y['rc']}/{y['timed_out']}")
        fx, fy = set(x["files"]), set(y["files"])
        if fx != fy:
            notes.append(f"p{k} files differ: {sorted(fx ^ fy)[:6]}")
        for rel in sorted(fx & fy) + ["__stdout"]:
            if rel != "__stdout" and x["files"][rel] == y["files"][rel]:
                continue
            bx = (RA / doc / a_eng / f"p{k}" / fname(rel)).read_bytes()
            by = (RB / doc / b_eng / f"p{k}" / fname(rel)).read_bytes()
            if bx == by:
                continue
            if len(bx) > BIG or len(by) > BIG:
                r = big_equal(rel, bx, by, rxa, rxb)
                if r is None:
                    notes.append(f"p{k} {rel}: lengths {len(bx)} vs {len(by)}")
                elif r[0]:
                    for h in sorted(r[1]):
                        masks.add(f"{rel.rsplit('.', 1)[-1]}:{h}(applied)")
                else:
                    notes.append(f"p{k} {rel}: {r[2]}")
                continue
            eq, need = needed_masks(rel, bx, by, rxa, rxb, ga, gb)
            if eq:
                for h in need:
                    masks.add(f"{rel.rsplit('.', 1)[-1]}:{h}")
            else:
                mx, _ = mask(rel, bx, rxa)
                my, _ = mask(rel, by, rxb)
                notes.append(f"p{k} {rel}: {first_diff(mx, my)}")
    if notes:
        only_stdout = all(n.split(" ", 2)[1] == "__stdout:" for n in notes if n.startswith("p"))
        only_stdout = only_stdout and all(n.startswith("p") and " __stdout: " in n for n in notes)
        return ("DIFF_STDOUT_ONLY" if only_stdout else "DIFF"), notes, masks
    return ("EQUAL_MASKED" if masks else "IDENTICAL"), [], masks


def main():
    docs = sorted(p.name for p in RA.iterdir() if (p / "result.json").is_file())
    missing_b = [d for d in docs if not (RB / d / "result.json").is_file()]
    docs = [d for d in docs if d not in missing_b]
    verdicts, maskc, diffs = Counter(), Counter(), {}
    rcs = Counter()
    for d in docs:
        v, notes, masks = compare_doc(d)
        verdicts[v] += 1
        for m in masks:
            maskc[m] += 1
        if notes:
            diffs[d] = notes
        ra = json.load(open(RA / d / "result.json")).get(a_eng, {})
        if "passes" in ra:
            last = ra["passes"][-1]
            rcs["timeout" if last["timed_out"] else f"rc{last['rc']}"] += 1
    out = {"set": SET, "a": f"{SET_A}/{a_arch}:{a_eng}", "b": f"{SET_B}/{b_arch}:{b_eng}",
           "documents": len(docs), "missing_on_b": len(missing_b),
           "verdicts": dict(verdicts), "masks_needed": dict(maskc),
           "final_rc_of_a": dict(rcs), "diffs": diffs}
    tag = f"{SET_A}__{a_arch}-{a_eng}__vs__{SET_B}__{b_arch}-{b_eng}"
    import os
    outdir = Path(os.environ.get("H1_DIFF_DIR", str(W)))
    outdir.mkdir(parents=True, exist_ok=True)
    json.dump(out, open(outdir / f"diff_{tag}.json", "w"), indent=1)
    print(json.dumps({k: v for k, v in out.items() if k != "diffs"}, indent=1))
    for d, n in list(diffs.items())[:15]:
        print(d, n[:4])


if __name__ == "__main__":
    main()

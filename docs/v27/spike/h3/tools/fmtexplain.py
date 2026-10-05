#!/usr/bin/env python3
"""Explain, byte by byte, how the round trip's re-dumped format differs from the shipped one.

usage: fmtexplain.py SHIPPED ROUNDTRIP --contract KERNEL.json --log TEXPUT.LOG [--trace MEMTRACE[.gz]] [--out FILE.json]

SHIPPED is the decompressed pdflatex.fmt stream, ROUNDTRIP the decompressed texput.fmt that
`pdftex -ini` with the first line `&pdflatex \\dump` writes (H.3's round trip; the model and the
pinned binary write the same bytes). Both are decoded completely by fmtdecode.py (every byte to
one field; decode then encode is the identity) and compared ELEMENT BY ELEMENT: an element is a
piece of the stream keyed by what it holds (mem[a], eqtb[k], hash[p], pool byte i, ...), not by
its offset. Every element of either stream is then in exactly one class:
  unchanged   the same key holds the same bytes in both (possibly at another offset)
  changed     the same key, different bytes
  new         the key is only in ROUNDTRIP
  removed     the key is only in SHIPPED
and every changed, new or removed element must be attributed to a cause below whose check
holds; an element no cause claims is reported UNEXPLAINED (exit 1). The causes, each with the
check that makes it more than a label:
  S  new strings: SHIPPED's pool is an exact prefix; each new string is identified (the banner
     load_fmt_file makes, the names \\csname entered, the log name, the format identifier)
  F  the format identifier: built by §1508 from the job name and \\year.\\month.\\day of eqtb
  H  the hash: replaying id_lookup (pdftex.p, §259/§279 with web2c's hash_extra) for the new
     names, in string order, on SHIPPED's hash gives ROUNDTRIP's hash, hash_used and
     hash_high exactly; cs_count is §1318's formula in both streams
  E  eqtb: the entries that differ are exactly the control sequences the contract generator
     recorded as assigned by \\everyjob (its independent trace, `everyjob_names`); no other
     eqtb word differs
  R  the eqtb run-length headers (§1493/§1494) and words that moved between explicit and
     copied: a function of the eqtb array (the encoder reproduces both streams), and the
     array differs only at E's entries
  M  one-word memory (hi mem; lo mem must not differ): TeX's single-word allocator is a stack
     (get_avail pops, free_avail and flush_list push), so ROUNDTRIP's free list must be some
     pushed cells on top of a suffix of SHIPPED's; every differing word is then one of
       M-live     popped and now in a token list of a changed eqtb entry (set equality)
       M-freed    in a list of a changed entry's old meaning and free now (set equality);
                  only its link differs, and only for a list's last cell (flush_list)
       M-refcount the reference count of a list whose eqtb references changed, by exactly
                  that change
       M-scratch  the fixed scratch cells temp_head (mem_top-3) and garbage (mem_top-12):
                  their link points into the run's freed cells
       M-temp     popped and pushed back: a temporary of the run. Its link is the free-list
                  successor; its info field is the last token the run stored there, DEAD
                  data (get_avail overwrites it before any read). Its value is reproduced by
                  the model, which writes the same bytes as the binary, but is not derived
                  here: this report says so instead of calling it explained
     plus avail and dyn_used, which follow from the free list (dyn_used = mem_end + 1 -
     hi_mem_min - length of the free list)
Also checked: the counts the binary itself prints while dumping (ROUNDTRIP's log) equal the
decoded ones, and the naive comparison at equal offsets is decomposed into these classes."""
import gzip
import hashlib
import json
import struct
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import fmtdecode as D  # noqa: E402

CS_TOKEN_FLAG = 4095                  # pdftex.p: partoken := 4095 + parloc
CALL, LONG_OUTER_CALL = 114, 117      # undefined_cs = 104 (load_fmt_file) = max_command + 1; call = + 11
YEAR, MONTH, DAY = 29300, 29299, 29298   # §1508's eqtb[...].int in pdftex.p's store_fmt_file


def opt(name):
    return sys.argv[sys.argv.index(name) + 1] if name in sys.argv else None


def avail_list(f):
    out, p, seen = [], f.avail, set()
    while p != D.NULL:
        assert p not in seen, "the free list has a cycle"
        seen.add(p)
        out.append(p)
        p = f.mem[p][0]
    return out


def eq_type(w):
    return D.b0(w)


def cs_name(f, p):
    h = f.hash.get(p)
    return D.string(f, h[0]).decode("latin-1") if h and 0 < h[0] < f.strptr else None


def all_eqtb(f):
    """(location, word) of every eqtb entry, the hash_extra region included."""
    for k in range(1, D.EQTB_SIZE + 1):
        yield k, f.eqtb[k]
    for i, w in enumerate(f.eqtb_extra):
        yield D.EQTB_EXTRA + i, w


def token_list(f, h):
    out, p = [], h
    while p != D.NULL:
        out.append(p)
        p = f.mem[p][0]
        assert len(out) < 10 ** 6
    return out


def tok(f, t):
    if t >= CS_TOKEN_FLAG:
        return "\\" + (cs_name(f, t - CS_TOKEN_FLAG) or "?%d" % (t - CS_TOKEN_FLAG))
    return "%d:%s" % (t >> 8, chr(t & 255))


def meaning(f, w):
    t = eq_type(w)
    if CALL <= t <= LONG_OUTER_CALL and w[0] != D.NULL:
        body = [tok(f, f.mem[p][1]) for p in token_list(f, w[0])[1:]]
        return {"eq_type": t, "eq_level": D.b1(w), "token_list": w[0], "tokens": " ".join(body)[:400]}
    return {"eq_type": t, "eq_level": D.b1(w), "equiv": w[0]}


def id_lookup_insert(hash_, name_text, hashhigh, hashused, hash_extra, strings):
    """pdftex.p idlookup for a name not yet in the table: hash, walk the chain, insert."""
    buf = name_text
    h = buf[0]
    for c in buf[1:]:
        h = h + h + c
        while h >= D.HASH_PRIME:
            h -= D.HASH_PRIME
    p = h + D.HASH_BASE
    while True:
        rh, lh = hash_.get(p, (0, 0))
        if rh > 0 and strings(rh) == buf:
            raise AssertionError("name already present: %r" % buf)
        if lh == 0:
            break
        p = lh
    if hash_.get(p, (0, 0))[0] > 0:
        if hashhigh < hash_extra:
            hashhigh += 1
            hash_[p] = (hash_[p][0], hashhigh + D.EQTB_SIZE)
            p = hashhigh + D.EQTB_SIZE
        else:
            while True:
                hashused -= 1
                if hash_.get(hashused, (0, 0))[0] == 0:
                    break
            hash_[p] = (hash_[p][0], hashused)
            p = hashused
    return p, hashhigh, hashused


def main():
    a_path, b_path = sys.argv[1], sys.argv[2]
    A_bytes, B_bytes = Path(a_path).read_bytes(), Path(b_path).read_bytes()
    S, R = D.decode(A_bytes), D.decode(B_bytes)
    checks, unexplained = {}, []

    def check(name, ok, detail=None):
        checks[name] = {"ok": bool(ok), **({"detail": detail} if detail is not None else {})}

    check("decode+encode is the identity on both streams", D.encode(S) == A_bytes and D.encode(R) == B_bytes)
    ea, eb = D.elements(S), D.elements(R)
    ma, mb = dict(ea), dict(eb)
    assert len(ma) == len(ea) and len(mb) == len(eb), "duplicate element keys"

    # --- the binary's own dump statistics (ROUNDTRIP's log) against the decoded values
    log = Path(opt("--log")).read_text(encoding="latin-1")
    want = {
        "%d strings of total length %d" % (R.strptr, R.poolptr): True,
        "%d memory locations dumped; current usage is %d&%d" % (len(R.mem), R.varused, R.dynused): True,
        "%d multiletter control sequences" % R.cscount: True,
        "%d words of font info for %d preloaded fonts" % (R.fmemptr - 7, R.fontptr): True,
        "%d hyphenation exceptions" % R.hyphcount: True,
        "Hyphenation trie of length %d has %d ops out of" % (R.triemax, R.trieopptr): True,
    }
    check("the binary's dump statistics (texput.log) equal the decoded counts", all(s in log for s in want),
          [s for s in want if s not in log])

    # --- strings (S) and the format identifier (F)
    prefix = S.strstart == R.strstart[:S.strptr + 1] and R.strpool[:S.poolptr] == S.strpool
    new_strings = [D.string(R, s) for s in range(S.strptr, R.strptr)]
    new_cs_strings = list(range(S.strptr, R.strptr))
    ident = b" (preloaded format=texput %d.%d.%d)" % (R.eqtb[YEAR][0], R.eqtb[MONTH][0], R.eqtb[DAY][0])
    banner = D.string(R, S.strptr)
    check("S: the shipped string pool is an exact prefix of the round trip's", prefix)
    check("F: the format identifier is the last string, §1508's ' (preloaded format=JOB Y.M.D)' for job "
          "texput and the run's \\year.\\month.\\day", R.formatident == R.strptr - 1 and new_strings[-1] == ident,
          new_strings[-1].decode())
    check("S: the second-to-last new string is the log file's name (open_log_file)", new_strings[-2] == b"texput.log")
    check("S: the first new string is the banner load_fmt_file's makepdftexbanner makes",
          banner.startswith(b"This is pdfTeX, Version 3.141592653-2.6-1.40.29"), banner.decode())

    # --- the hash (H): replay id_lookup for the new names
    cs_strings = [s for s in new_cs_strings if s not in (S.strptr, R.strptr - 2, R.strptr - 1)]
    hsim = dict(S.hash)
    hh, hu = S.hashhigh, S.hashused
    strings_of = lambda s: D.string(R, s)
    placed = {}
    for s in cs_strings:
        p, hh, hu = id_lookup_insert(hsim, D.string(R, s), hh, hu, 600000, strings_of)
        hsim[p] = (s, 0)
        placed[p] = D.string(R, s).decode()
    rhash = {p: w for p, w in R.hash.items()}
    check("H: replaying id_lookup for the %d new names on the shipped hash gives the round trip's hash, "
          "hash_used and hash_high" % len(cs_strings),
          hsim == rhash and hh == R.hashhigh and hu == R.hashused,
          {"placed": {str(p): n for p, n in sorted(placed.items())}, "hash_high": [S.hashhigh, R.hashhigh]})
    for F, nm in ((S, "shipped"), (R, "round trip")):
        n = sum(1 for p in range(D.HASH_BASE, F.hashused + 1) if F.hash[p][0] != 0)
        check("H: cs_count is §1318's 15513 - hash_used + hash_high + (entries dumped sparsely), %s" % nm,
              F.cscount == 15513 - F.hashused + F.hashhigh + n)

    # --- eqtb (E)
    ext = max(len(S.eqtb_extra), len(R.eqtb_extra))
    sx = S.eqtb_extra + [None] * (ext - len(S.eqtb_extra))
    eq_changed = [k for k in range(1, D.EQTB_SIZE + 1) if S.eqtb[k] != R.eqtb[k]] + \
                 [D.EQTB_EXTRA + i for i in range(ext) if sx[i] != R.eqtb_extra[i]]
    contract = json.loads(Path(opt("--contract")).read_text())
    names = {k: cs_name(R, k) for k in eq_changed}
    check("E: the eqtb entries that differ are exactly the contract generator's \\everyjob names "
          "(its own trace of the \\everyjob replay)",
          sorted(names.values()) == sorted(contract["everyjob_names"]),
          {"differing": len(eq_changed), "everyjob_names": len(contract["everyjob_names"])})
    eqtb_detail = {}
    for k in eq_changed:
        old = S.eqtb[k] if k <= D.EQTB_SIZE else sx[k - D.EQTB_EXTRA]
        eqtb_detail[names[k]] = {"loc": k, "shipped": meaning(S, old) if old else "not present (a new entry)",
                                 "round_trip": meaning(R, R.eqtb[k] if k <= D.EQTB_SIZE else R.eqtb_extra[k - D.EQTB_EXTRA])}

    # --- one-word memory (M)
    lo_diff = [a for a in S.mem if a <= S.lomemmax and S.mem[a] != R.mem.get(a)]
    check("M: no word of variable-size (lo) memory differs, and lo_mem_max, rover, sa_root, hi_mem_min agree",
          not lo_diff and (S.lomemmax, S.rover, S.saroot, S.himemmin, S.chunks) ==
          (R.lomemmax, R.rover, R.saroot, R.himemmin, R.chunks))
    aS, aR = avail_list(S), avail_list(R)
    c = 0
    while c < min(len(aS), len(aR)) and aS[-1 - c] == aR[-1 - c]:
        c += 1
    popped, pushed = aS[:len(aS) - c], aR[:len(aR) - c]
    setS, setR, popped_s, pushed_s = set(aS), set(aR), set(popped), set(pushed)
    check("M: the round trip's free list is cells pushed on a suffix of the shipped one (a stack)",
          aS[len(aS) - c:] == aR[len(aR) - c:] and not (pushed_s & (setS - popped_s)),
          {"shipped_free": len(aS), "round_trip_free": len(aR), "common_suffix": c,
           "popped": len(popped), "pushed": len(pushed)})
    for F, a, nm in ((S, aS, "shipped"), (R, aR, "round trip")):
        check("M: dyn_used = mem_end + 1 - hi_mem_min - free cells (%s)" % nm,
              F.dynused == F.memtop + 1 - F.himemmin - len(a) and F.avail == (a[0] if a else D.NULL))
    # token lists of the changed entries
    def lists(F, words):
        return {w[0]: token_list(F, w[0]) for w in words if w and CALL <= eq_type(w) <= LONG_OUTER_CALL
                and w[0] != D.NULL}
    old_w = [S.eqtb[k] if k <= D.EQTB_SIZE else sx[k - D.EQTB_EXTRA] for k in eq_changed]
    new_w = [R.eqtb[k] if k <= D.EQTB_SIZE else R.eqtb_extra[k - D.EQTB_EXTRA] for k in eq_changed]
    old_lists, new_lists = lists(S, old_w), lists(R, new_w)
    live_new = {p for h, ns in new_lists.items() if h in popped_s for p in ns}
    freed_old = {p for h, ns in old_lists.items() if h in pushed_s for p in ns}
    m_live = popped_s - setR
    m_freed = pushed_s - setS
    check("M-live: the popped cells that are live now are exactly the cells of the new token lists",
          m_live == live_new, {"cells": len(m_live)})
    check("M-freed: the cells free now that were live are exactly the cells of the freed old lists",
          m_freed == freed_old, {"cells": len(m_freed)})

    def refs(F):
        n = {}
        for _, w in all_eqtb(F):
            if CALL <= eq_type(w) <= LONG_OUTER_CALL and w[0] != D.NULL:
                n[w[0]] = n.get(w[0], 0) + 1
        return n
    rS, rR = refs(S), refs(R)
    rc_ok, rc_detail = True, {}
    for h in set(old_lists) | set(new_lists):
        if h in setS and h in setR:
            continue
        if h not in setS and h not in setR:          # live in both: the count moves with the references
            ok = R.mem[h][1] - S.mem[h][1] == rR.get(h, 0) - rS.get(h, 0)
        elif h in setR:                               # freed: every reference was an eqtb one, and is gone
            ok = S.mem[h][1] - D.NULL + 1 == rS.get(h, 0) and rR.get(h, 0) == 0
        else:                                         # new: its count is its eqtb references
            ok = R.mem[h][1] - D.NULL + 1 == rR.get(h, 0)
        rc_ok &= ok
        rc_detail[str(h)] = [rS.get(h, 0), rR.get(h, 0), S.mem[h][1] - D.NULL, R.mem[h][1] - D.NULL, ok]
    check("M-refcount: every list the changed entries point to (or pointed to) has the reference count "
          "its eqtb references give (ref_count = null + references - 1), before and after", rc_ok, rc_detail)

    scratch = {S.memtop - 3: "temp_head", S.memtop - 12: "garbage"}
    m_diff = sorted(a for a in S.mem if S.mem[a] != R.mem[a])
    cls, tails_ok, temp_in_place = {}, True, []
    for a in m_diff:
        sw, rw = S.mem[a], R.mem[a]
        if a in m_live:
            cls[a] = "M-live"
        elif a in m_freed:
            cls[a] = "M-freed"
            tails_ok &= sw[1] == rw[1] and sw[0] == D.NULL
        elif a in popped_s and a in pushed_s:
            cls[a] = "M-temp"
        elif a in setS and a in setR and a not in popped_s and a not in pushed_s and sw[0] == rw[0]:
            # free in both, in the common suffix, the same link: popped and pushed back in place.
            # get_avail pops cells in free-list order and a list built from them is linked in
            # that order, so flush_list (link(tail) := avail; avail := head) restores the free
            # list exactly: only the info fields show that the cells were used
            cls[a] = "M-temp"
            temp_in_place.append(a)
        elif a in scratch:
            cls[a] = "M-scratch"
        elif a not in setS and a not in setR and str(a) in rc_detail and sw[0] == rw[0]:
            cls[a] = "M-refcount"
        else:
            cls[a] = None
    check("M-freed: a freed cell differs only in its link, and only if it was its list's last cell",
          tails_ok)
    # the_toks and str_toks start their list at temp_head and return its last cell, which is
    # temp_head itself for an empty list; ins_the_toks stores that in link(garbage)
    sc_ok = all(R.mem[a][0] in pushed_s or R.mem[a][0] in (D.NULL, S.memtop - 3)
                for a in scratch if cls.get(a) == "M-scratch") and all(S.mem[a][1] == R.mem[a][1] for a in scratch)
    check("M-scratch: temp_head's and garbage's links point to cells the run freed, to temp_head (the_toks "
          "of an empty list) or are null; their info fields are unchanged", sc_ok,
          {scratch[a]: [S.mem[a], R.mem[a]] for a in scratch if a in cls})

    # --- optional: the model's own record of every write into mem during the run (trace_build.sh)
    trace_out = None
    if opt("--trace"):
        last, nwrites = {}, 0
        tp = Path(opt("--trace"))
        ttext = gzip.decompress(tp.read_bytes()).decode() if tp.suffix == ".gz" else tp.read_text()
        for line in ttext.splitlines():
            f6 = line.split(" ", 7)
            if len(f6) < 8 or f6[4] != "W" or f6[2] != str(S.memtop + 2):
                continue        # mem is the block of mem_max - mem_min + 2 cells (web2c's xmallocarray)
            nwrites += 1
            last[int(f6[3])] = (int(f6[0]), int(f6[5], 16), int(f6[6], 16), f6[7])
        le = lambda w: ((w[0] & 0xFFFFFFFF) << 32) | (w[1] & 0xFFFFFFFF)
        replay_ok = all(m == 0xFF and bits == le(R.mem[a]) for a, (_, bits, m, _) in last.items() if a in R.mem)
        untouched_ok = all(a in last for a in m_diff)
        check("T: replaying the model's mem writes of the run (after load_fmt_file returns) on the shipped mem "
              "gives the round trip's mem: every written word ends with the dumped value", replay_ok,
              {"writes": nwrites, "words_written": len(last)})
        check("T: every differing mem word was written during the run", untouched_ok)
        by = {}
        for a in m_diff:
            c = cls.get(a)
            writer = last[a][3].split("<")[0] if a in last else "NOT WRITTEN"
            by.setdefault(c, {}).setdefault(writer, 0)
            by[c][writer] += 1
        trace_out = {"last_writer_by_class": by,
                     "m_temp_last_writes": {str(a): {"seq": last[a][0], "chain": last[a][3],
                                                     "info_token": tok(R, R.mem[a][1])}
                                            for a in m_diff if cls.get(a) == "M-temp" and a in last}}

    # --- element accounting
    def cause(key, kind):
        k0 = key[0]
        if k0 == "pool" or k0 == "str_start" or key in (("header", "pool_ptr"), ("header", "str_ptr")):
            return "S"
        if key == ("end", "format_ident"):
            return "F"
        if k0 in ("hash", "hash_index") or key == ("header", "hash_high"):
            return "H"
        if k0 == "eqtb" and isinstance(key[1], int):
            if key[1] in eq_changed:
                return "E"
            # present in both arrays with one value: only its representation moved
            vs = S.eqtb[key[1]] if key[1] <= D.EQTB_SIZE else None
            vr = R.eqtb[key[1]] if key[1] <= D.EQTB_SIZE else None
            return "R" if vs == vr and vs is not None else None
        if k0 == "eqtb_run":
            return "R"
        if k0 == "mem" and isinstance(key[1], int):
            return cls.get(key[1])
        if key in (("mem", "avail"), ("mem", "dyn_used")):
            return "M"
        return None

    tally = {}
    for kind, keys in (("changed", [k for k in mb if k in ma and ma[k] != mb[k]]),
                       ("new", [k for k in mb if k not in ma]),
                       ("removed", [k for k in ma if k not in mb])):
        for k in keys:
            cz = cause(k, kind)
            nbytes = len(mb[k]) if kind != "removed" else len(ma[k])
            if kind == "changed":     # count only the bytes that differ inside the element
                nbytes = sum(1 for x, y in zip(ma[k], mb[k]) if x != y)
            t = tally.setdefault(cz or "UNEXPLAINED", {}).setdefault(kind, [0, 0])
            t[0] += 1
            t[1] += nbytes
            if cz is None:
                unexplained.append([kind, repr(k)])
    # M-temp: which bytes are the link (structural) and which the info (dead data)
    temp_link = temp_info = 0
    for a, cz in cls.items():
        if cz == "M-temp":
            sb, rb = struct.pack(">ii", *S.mem[a]), struct.pack(">ii", *R.mem[a])
            temp_link += sum(1 for i in range(4) if sb[i] != rb[i])
            temp_info += sum(1 for i in range(4, 8) if sb[i] != rb[i])
    dead_tokens = [tok(R, R.mem[a][1]) for a in pushed if cls.get(a) == "M-temp"] + ["|in place:"] + \
        [tok(R, R.mem[a][1]) for a in temp_in_place]

    # --- the naive comparison at equal offsets, decomposed
    def owner_map(el):
        out, o = [], 0
        for k, b in el:
            out.append((o, o + len(b), k))
            o += len(b)
        return out
    ob = owner_map(eb)
    def naive_cmp(oa, ob0):
        """bytes differing when A from oa and B from ob0 are compared at equal relative offsets,
        each assigned to the element of B that holds it"""
        tot = moved = 0
        byc = {}
        n = min(len(A_bytes) - oa, len(B_bytes) - ob0)
        for lo, hi, k in ob:
            lo2, hi2 = max(lo, ob0), min(hi, ob0 + n)
            if lo2 >= hi2:
                continue
            d = sum(1 for x in range(lo2, hi2) if A_bytes[x - ob0 + oa] != B_bytes[x])
            if d:
                tot += d
                if k in ma and ma[k] == mb[k]:
                    moved += d
                else:
                    cz = cause(k, "changed" if k in ma else "new") or "UNEXPLAINED"
                    byc[cz] = byc.get(cz, 0) + d
        return {"differing_bytes": tot, "in_elements_unchanged_but_moved": moved,
                "in_changed_or_new_elements_by_cause": byc}
    pool_end = lambda el: sum(len(b) for k, b in el[:next(i for i, (k, _) in enumerate(el) if k == ("mem", "lo_mem_max"))])
    naive_whole = naive_cmp(0, 0)
    naive_after_pool = naive_cmp(pool_end(ea), pool_end(eb))
    result = {
        "streams": {"shipped": {"bytes": len(A_bytes), "sha256": hashlib.sha256(A_bytes).hexdigest()},
                    "round_trip": {"bytes": len(B_bytes), "sha256": hashlib.sha256(B_bytes).hexdigest()}},
        "elements": {"shipped": len(ea), "round_trip": len(eb),
                     "unchanged": sum(1 for k in mb if k in ma and ma[k] == mb[k])},
        "checks": checks,
        "by_cause": {k: {kk: {"elements": vv[0], "bytes": vv[1]} for kk, vv in v.items()} for k, v in sorted(tally.items())},
        "m_temp": {"cells": sum(1 for v in cls.values() if v == "M-temp"), "restored_in_place": len(temp_in_place),
                   "link_bytes": temp_link,
                   "info_bytes_dead_data": temp_info, "info_as_tokens_in_free_list_order": dead_tokens},
        "naive_equal_offset_comparison": {"whole_streams": naive_whole,
                                          "after_the_string_pool (fmtdiff.py's 1,881,851)": naive_after_pool},
        "new_strings": [s.decode("latin-1") for s in new_strings],
        "eqtb_changes": eqtb_detail,
        "trace": trace_out,
        "unexplained": unexplained,
    }
    js = json.dumps(result, indent=1, ensure_ascii=False)
    if opt("--out"):
        Path(opt("--out")).write_text(js + "\n")
    bad = [k for k, v in checks.items() if not v["ok"]]
    for k in bad:
        print("CHECK FAILED:", k)
    print(json.dumps({"by_cause": result["by_cause"], "m_temp": {k: v for k, v in result["m_temp"].items()
                                                                if k != "info_as_tokens_in_free_list_order"},
                      "naive": result["naive_equal_offset_comparison"], "unexplained": len(unexplained),
                      "checks_failed": bad}, indent=1))
    sys.exit(1 if bad or unexplained else 0)


if __name__ == "__main__":
    main()

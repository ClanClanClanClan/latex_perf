#!/usr/bin/env python3
"""AI-scoping (OPEN-129): the \\meaning of some names, and of every name their macro text
mentions, round by round, in format state of the pinned image (`pdftex -ini`, `&pdflatex`).

This script never starts an engine. Each round it writes the terminal input of one meaning
dump; the engine is run by the documented recipe of docs/v27/spike/AI-scoping.md §6.1 (the
H.3 README's binary-side recipe, with that input); then `absorb` reads its terminal output.

A crude regex walk, a screen and not a closure proof: control words of letters, @, _ and :,
plus the robust inner name "X " of every `\\protect \\X  `. It does not follow names built
by \\csname, active characters or expl3 variants built at run time (C-92 and C-96 are the
recorded failures of exactly this kind of walk; it is used here only to size the code).

  closure.py start STATE.json NAME[,NAME...]   # first round's input -> ./in.tex
  closure.py absorb STATE.json TERMINAL_OUT     # record meanings, write the next round's input
  closure.py dump STATE.json                    # every recorded name and meaning
"""
import json, os, re, sys


def block(names):
    lines = ["&pdflatex", "\\makeatletter\\catcode`\\_=11 \\catcode`\\:=11 "]
    for n in names:
        h = n.encode().hex()
        lines.append("\\ifcsname %s\\endcsname\\immediate\\write16{@@M %s \\expandafter\\meaning"
                     "\\csname %s\\endcsname}\\else\\immediate\\write16{@@M %s UNDEFINED}\\fi"
                     % (n, h, n, h))
    lines.append("\\csname @@end\\endcsname")
    return "\n".join(lines) + "\n"


def refs(m):
    s = set(re.findall(r"\\([A-Za-z@_:]+)", m))
    s |= {x + " " for x in re.findall(r"\\protect \\([A-Za-z@]+)  ", m)}
    return s


def main(argv):
    cmd, path = argv[1], argv[2]
    if cmd == "start":
        st = {"seen": {}, "pending": argv[3].split(",")}
    else:
        st = json.load(open(path))
    if cmd == "absorb":
        got = {}
        for line in open(argv[3], encoding="latin-1").read().splitlines():
            i = line.find("@@M ")
            if i >= 0:
                _, h, m = line[i:].split(" ", 2)
                got[bytes.fromhex(h).decode("latin-1")] = m
        st["seen"].update(got)
        nxt = set()
        for n, m in got.items():
            if "macro:" in m[:40]:
                nxt |= refs(m)
        st["pending"] = sorted(n for n in nxt if n not in st["seen"])
    if cmd == "dump":
        for k in sorted(st["seen"]):
            print(repr(k), "=>", st["seen"][k])
        return 0
    json.dump(st, open(path, "w"), indent=0, sort_keys=True)
    if st["pending"]:
        open("in.tex", "w").write(block(st["pending"]))
    print("recorded", len(st["seen"]), "pending", len(st["pending"]))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))

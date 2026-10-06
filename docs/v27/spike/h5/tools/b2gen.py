#!/usr/bin/env python3
"""b2gen.py PRE_INTERP_V OUT_DIR | b2gen.py --check PRE_INTERP_V H2_COQ_DIR
(PRE_INTERP_V = `git` reads it from the repository: python3 b2gen.py --check git ../../h2/coq)

Candidate B2 of H5-heap-design.md (spike H.5 stage 2): the interpreter's fuelled mutual block,
restructured at the SOURCE so that no extracted closure holds a state across a call.

From the pre-B2 Interp.v (git 9c3315be:docs/v27/spike/h2/coq/Interp.v, sha256 1ef36d75...) it
writes:
  Interp.v     lines 1-178 of the pre-B2 file unchanged (types, helpers, the Section header and
               truth_or); then, for each of the ten members of the mutual block, a Definition
               NAME_body whose text is that member's successor branch VERBATIM, abstracted over
               the recursive functions the branch calls and the fuel f; then the block itself,
               each member reduced to
                   match fuel with O => <the pre-B2 O branch> | S f => NAME_body <rec fns> f <args> end
  RefInterp.v  the pre-B2 Section (lines 169-707) VERBATIM, under `From PS Require Import ...
               Interp`, so that it shares the types and helpers of Interp.v: the reference term
               against which B2Equiv.v proves each new member equal, by reflexivity.
Every slice is asserted (the expected lines, the expected count). --check regenerates both files
into a temporary directory and compares them byte for byte with the committed ones.

Why this removes the retention (H5-heap-design.md §2.2): ExtrOcamlNatInt extracts the match on
the fuel as a closure for the successor branch. Before B2 that closure's environment held the
state AND was read again after each non-tail call of the branch. After B2 the closure's whole
body is one call to NAME_body, whose arguments are its own parameters: ocamlopt's per-call-site
liveness then frees each state after its last use. The guard checker accepts NAME_body applied
to the recursive functions because it unfolds a constant whose arguments fail the check.
"""
import re
import subprocess
import sys
import tempfile
from pathlib import Path

# member: (rec-function type, header line count). Order is the block's order.
REC = [
    ("evale", "nat -> expr -> state -> eres"),
    ("evall", "nat -> lexp -> state -> lres"),
    ("evalargs", "nat -> list pkind -> list arg -> state -> bres"),
    ("evalx", "nat -> list arg -> state -> xres"),
    ("callp", "nat -> Z -> list cell -> state -> eres"),
    ("exec", "nat -> stmt -> state -> sres"),
    ("for_loop", "nat -> loc -> ct -> ty -> bool -> Z -> stmt -> state -> sres"),
    ("exec_list", "nat -> list stmt -> list stmt -> state -> sres"),
    ("goto_in", "nat -> Z -> list stmt -> list stmt -> state -> sres"),
    ("write_items", "nat -> Z -> list witem -> bool -> state -> sres"),
]
NAMES = [n for n, _ in REC]
PRE_SHA = "1ef36d759c07f7babea0fad20a0b8576b37a5d4fca1fb29ce50cba1cfd3de00d"

HEAD = """
(* ---------------------------------------------------------------- B2 (spike H.5 stage 2)
   The members of the mutual block below are the pre-B2 members (RefInterp.v) with each
   successor branch moved, verbatim, into a Definition NAME_body that takes the recursive
   functions it calls and the fuel f as arguments. B2Equiv.v proves every member equal to its
   pre-B2 counterpart by reflexivity: the term is the same up to unfolding NAME_body.
   The reason is the extraction, not the semantics (H5-heap-design.md §2.2): ExtrOcamlNatInt
   extracts `match fuel with O => a | S f => b` with b as a closure; when b made non-tail calls
   and then read its environment, that environment kept the state the branch began with alive
   for the whole call, and through PArray's version chains every write made since. Here the
   closure's body is a single call of NAME_body on its own arguments, so no closure holds a
   state across a call (h5/tools/b2static.py checks the extracted code for exactly this). *)
"""

FIXHEAD = """
(* the fuelled block: one step of fuel, then the member's body *)
"""


def die(msg):
    sys.exit(f"b2gen: {msg}")


def generate(pre: str):
    L = pre.split("\n")
    if L[169] != "Section Interp." or L[168] != "(* ---------------------------------------------------------------- the interpreter *)":
        die("pre-B2 Section header not at lines 169-170")
    if L[178] != "Fixpoint evale (fuel : nat) (e : expr) (st : state) {struct fuel} : eres :=":
        die("pre-B2 evale not at line 179")
    if L[706] != "End Interp.":
        die("pre-B2 End Interp. not at line 707")
    prefix = L[:178]                     # lines 1-178
    block = L[178:706]                   # lines 179-706
    # split the block into members: a member starts at `Fixpoint NAME` or `with NAME`; a comment
    # line directly before a `with` belongs to the next member
    starts = []
    for i, l in enumerate(block):
        m = re.match(r"^(Fixpoint|with) (\w+) \(fuel : nat\)", l)
        if m:
            starts.append((i, m.group(2)))
    if [n for _, n in starts] != NAMES:
        die(f"members {[n for _, n in starts]}")
    bodies, wrappers, comment_prev = [], [], None
    for k, (i, name) in enumerate(starts):
        j = starts[k + 1][0] if k + 1 < len(starts) else len(block)
        seg = block[i:j]
        while seg and seg[-1] == "":
            seg.pop()
        if seg and seg[-1].startswith("(*"):
            comment_next = seg.pop()      # belongs to the next member
            while seg and seg[-1] == "":
                seg.pop()
        else:
            comment_next = None
        # header: up to the line ending ':='
        h = 0
        while not seg[h].rstrip().endswith(":="):
            h += 1
        header = " ".join(x.strip() for x in seg[:h + 1])
        mh = re.match(rf"^(?:Fixpoint|with) {name} \(fuel : nat\) (.*?) \{{struct fuel\}} : (\w+) :=$", header)
        if not mh:
            die(f"{name}: header {header!r}")
        params, ret = mh.group(1), mh.group(2)
        args = " ".join(a for grp in re.findall(r"\(([\w ]+?) :", params) for a in grp.split())
        if seg[h + 1] != "  match fuel with":
            die(f"{name}: no `match fuel with` after the header")
        o_line = seg[h + 2]
        if not re.match(r"^  \| O => \w+ StFuel st$", o_line):
            die(f"{name}: O branch {o_line!r}")
        if seg[h + 3] != "  | S f =>":
            die(f"{name}: S branch line {seg[h + 3]!r}")
        last = seg[-1]
        if last not in ("  end", "  end."):
            die(f"{name}: last line {last!r}")
        body = seg[h + 4:-1]
        text = "\n".join(body)
        used = [n for n in NAMES if re.search(rf"(?<![\w']){n}(?![\w'])", text)]
        recp = [f"    ({n} : {t})" for n, t in REC if n in used]
        cm = [comment_prev] if (k > 0 and comment_prev) else []
        bodies.append("\n".join(cm + [f"Definition {name}_body"] + recp + [f"    (f : nat) {params} : {ret} :="]
                                + body[:-1] + [body[-1] + "."]))
        wrappers.append("\n".join(seg[:h + 3] + [f"  | S f => {name}_body {' '.join(used)} f {args}", last]))
        comment_prev = comment_next
    interp = "\n".join(prefix) + HEAD + "\n" + "\n\n".join(bodies) + "\n" + FIXHEAD + "\n".join(
        wrappers[0:1]) + "\n\n" + "\n\n".join(wrappers[1:]) + "\n\nEnd Interp.\n"
    if L[707:] != [""]:
        die("text after End Interp.")
    ref = REF_HEAD + "\n".join(L[168:707]) + "\n"
    return interp, ref


REF_HEAD = """(* The interpreter's mutual block as it was before B2 (spike H.5 stage 2): lines 169-707 of
   git 9c3315be:docs/v27/spike/h2/coq/Interp.v (sha256 1ef36d75...), verbatim below this header.
   It shares Interp.v's types and helpers (Interp.v keeps lines 1-178 of that file unchanged),
   so B2Equiv.v can state each new member equal to its counterpart here. Not extracted: no
   model code depends on this file. Checked by h5/tools/b2gen.py --check. *)

From Coq Require Import ZArith List Bool String PArray Uint63 Sint63 Floats.
From PS Require Import Syntax Values Interp.
Import ListNotations.
Local Open Scope Z_scope.

"""


def main():
    import hashlib
    if sys.argv[1] == "--check":
        pre, coq = Path(sys.argv[2]), Path(sys.argv[3])
    else:
        pre, coq = Path(sys.argv[1]), None
    # PRE may be `git`: the pre-B2 file read from the repository's history
    raw = (subprocess.run(["git", "show", "9c3315be:docs/v27/spike/h2/coq/Interp.v"], capture_output=True,
                          check=True, cwd=Path(__file__).resolve().parent).stdout
           if str(pre) == "git" else pre.read_bytes())
    if hashlib.sha256(raw).hexdigest() != PRE_SHA:
        die(f"{pre} is not the pre-B2 Interp.v")
    interp, ref = generate(raw.decode())
    if coq is None:
        out = Path(sys.argv[2])
        (out / "Interp.v").write_text(interp)
        (out / "RefInterp.v").write_text(ref)
        print(f"b2gen: wrote {out}/Interp.v and {out}/RefInterp.v")
        return
    bad = [n for n, t in (("Interp.v", interp), ("RefInterp.v", ref)) if (coq / n).read_text() != t]
    print("b2gen --check:", "OK" if not bad else f"DIFFERS: {bad}")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()

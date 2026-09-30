"""web2c writes an expression's tokens in order, keeping the source's parentheses, and
the C compiler re-parses them with C's precedences. The two parses differ only where
Pascal's and C's precedence orders differ (web2c-parser.y vs C):

  Pascal: and at the multiplicative level, or at the additive level, both above the
          relational operators;  C: && and || below == != < > <= >=.
  unary minus/not: web2c's %prec '*' makes them apply to the next operand (up to a
          multiplicative operator), which is C's reading of a prefix operator too.
  + - * / div mod: same levels and left associativity in both.

So the parses differ exactly at an unparenthesised relational operand of and/or, or an
unparenthesised and/or operand of a relational operator. `check(ast)` lists every such
node. The parser groups by C's precedences (parser.py), so the IR is the compiled
reading; this module re-derives the Pascal reading's disagreements for the report, by
re-parsing with web2c's yacc precedences."""
REL = {"=", "<>", "<", ">", "<=", ">="}
LOG = {"and", "or"}


PASCAL_PREC = {"=": 1, "<>": 1, "<": 1, ">": 1, "<=": 1, ">=": 1, "+": 2, "-": 2, "or": 2,
               "*": 4, "/": 4, "div": 4, "mod": 4, "and": 4}


def pascal_parse(text):
    """Parse with web2c's yacc precedences (for the comparison only)."""
    import parser as P
    saved = dict(P.PREC), P.UNARY_PREC
    P.PREC.clear(); P.PREC.update(PASCAL_PREC); P.UNARY_PREC = 4
    try:
        return P.parse(text)
    finally:
        P.PREC.clear(); P.PREC.update(saved[0]); P.UNARY_PREC = saved[1]


def check(P):
    bad = []

    def walk(x, where):
        if isinstance(x, tuple):
            if x and x[0] == "bin":
                op, a, b = x[1], x[2], x[3]
                for c in (a, b):
                    if c[0] == "bin" and ((op in LOG and c[1] in REL) or (op in REL and c[1] in LOG)):
                        bad.append((where, op, c[1]))
            for y in x:
                walk(y, where)
        elif isinstance(x, list):
            for y in x:
                walk(y, where)
    for p in P["procs"]:
        walk(p["body"], p["name"])
    return bad

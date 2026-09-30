"""Static check of every goto in the lowered program (spike H.2).

PS resolves `goto n` by searching the enclosing statement lists, innermost first, for an
element that is `label n` or contains it; in the latter case it resumes inside that
element by continuation (a C goto may enter a sibling case arm or if branch, which
Pascal forbids but tangle's output does, twice). Resuming inside a `for` body is not
possible (web2c's for loop keeps its bound in a hidden temporary), so such a goto is
refused. `check(procs)` returns (unresolvable, into_structured, counts)."""


def contains(s, n):
    k = s[0]
    if k == "label":
        return s[1] == n
    if k == "seq":
        return any(contains(x, n) for x in s[1])
    if k == "if":
        return contains(s[2], n) or contains(s[3], n)
    if k == "while":
        return contains(s[2], n)
    if k == "repeat":
        return contains(s[1], n)
    if k == "for":
        return contains(s[6], n)
    if k == "case":
        return any(contains(b, n) for _, b in s[2]) or (s[3] is not None and contains(s[3], n))
    return False


def path_ok(s, n):
    k = s[0]
    if k == "label":
        return True
    if k == "seq":
        for x in s[1]:
            if contains(x, n):
                return path_ok(x, n)
    if k == "if":
        return path_ok(s[2], n) if contains(s[2], n) else path_ok(s[3], n)
    if k == "while":
        return path_ok(s[2], n)
    if k == "repeat":
        return path_ok(s[1], n)
    if k == "case":
        for _, b in s[2]:
            if contains(b, n):
                return path_ok(b, n)
        return path_ok(s[3], n)
    return False


def check(procs):
    bad, into, counts = [], [], {"goto": 0, "return": 0}

    def walk(s, scope, pname):
        k = s[0]
        if k == "seq":
            for x in s[1]:
                walk(x, scope + [s], pname)
        elif k == "return":
            counts["return"] += 1
        elif k == "goto":
            counts["goto"] += 1
            n = s[1]
            for sq in reversed(scope):
                hit = [x for x in sq[1] if contains(x, n)]
                if hit:
                    if hit[0][0] != "label":
                        into.append((pname, n))
                        if not path_ok(hit[0], n):
                            bad.append((pname, n, "through a for body"))
                    break
            else:
                bad.append((pname, n, "no enclosing label"))
        elif k == "if":
            walk(s[2], scope, pname)
            walk(s[3], scope, pname)
        elif k == "while":
            walk(s[2], scope, pname)
        elif k == "repeat":
            walk(s[1], scope, pname)
        elif k == "for":
            walk(s[6], scope, pname)
        elif k == "case":
            for _, b in s[2]:
                walk(b, scope, pname)
            if s[3]:
                walk(s[3], scope, pname)
    for p in procs:
        walk(p["body"], [], p["name"])
    return bad, into, counts

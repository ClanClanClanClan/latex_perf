"""Parser for web2c's Pascal (spike H.2, ADR-015).

The grammar is texk/web2c/web2c/web2c-parser.y of the pinned revision, including
its operator precedences, which decide how an expression groups (the C compiler
then re-parses web2c's flat token output with C's precedences; `cprec.py` checks
that the two agree on every expression):

  %nonassoc '=' '<>' '<' '>' '<=' '>='
  %left '+' '-' or
  %right unary_plus unary_minus
  %left '*' '/' div mod and
  %right not
  EXPRESS: UNARY_OP EXPRESS %prec '*'

So a unary operator applies to the operand that follows it up to the next binary
operator of precedence <= '*' (left-associative at '*'): `-a*b` is `(-a)*b`,
`not a and b` is `(not a) and b`.

AST (tuples):
  expr : ('num', int) | ('real', text) | ('str', text) | ('char', text)
         | ('id', name)                      an identifier (variable, constant,
                                             parameterless function, type name)
         | ('idx', expr, [expr, ...])        array indexing
         | ('fld', expr, name)               record field (hh, b0, rh, int, ...)
         | ('call', name, [arg, ...])        call with arguments; arg = expr or
                                             ('width', expr, [int, ...]) for write
         | ('un', op, expr) | ('bin', op, expr, expr)
  stmt : ('assign', expr, expr) | ('pcall', name, [arg]) | ('goto', int)
         | ('label', int, stmt) | ('seq', [stmt]) | ('if', expr, stmt, stmt|None)
         | ('case', expr, [([label], stmt)]) with label = int | 'others'
         | ('while', expr, stmt) | ('repeat', [stmt], expr)
         | ('for', name, expr, 'to'|'downto', expr, stmt) | ('break',) | ('empty',)
"""
from lexer import lex

# The binary is what the C COMPILER made of web2c's output, and web2c writes an
# expression's tokens in source order (keeping the source's parentheses; `/` becomes
# `/ ((double) R)` around its right operand, `div` `/`, `mod` `%`, `and` `&&`, `or` `||`,
# `=` `==`, `<>` `!=`). So expressions are grouped by C's precedences, not web2c's
# yacc ones: they differ at and/or next to a relational operator, where the Pascal
# reading of `fixedpdfdraftmodeset and fixedpdfdraftmode>0` would be
# `(set and mode) > 0` and the compiled one is `set && (mode > 0)` (cprec.py lists the
# eight such places). Unary - and not bind to the next operand in both (web2c's
# %prec '*', C's prefix operators).
PREC = {"or": 1, "and": 2, "=": 3, "<>": 3, "<": 4, ">": 4, "<=": 4, ">=": 4,
        "+": 5, "-": 5, "*": 6, "/": 6, "div": 6, "mod": 6}
UNARY_PREC = 6


class Parser:
    def __init__(self, toks):
        self.t = toks
        self.i = 0

    # -- token helpers -------------------------------------------------------
    def peek(self, k=0):
        return self.t[self.i + k]

    def at(self, *kinds):
        return self.t[self.i].kind in kinds

    def take(self, kind=None):
        tok = self.t[self.i]
        if kind is not None and tok.kind != kind:
            raise SyntaxError(f"line {tok.line}: expected {kind}, got {tok.kind} {tok.val!r}")
        self.i += 1
        return tok

    def opt(self, kind):
        if self.at(kind):
            return self.take()
        return None

    # -- defines -------------------------------------------------------------
    def defines(self):
        out = []
        while self.at("@define"):
            self.take()
            if self.opt("@field"):
                out.append(("field", self.take("id").val, None))
                self.take(";")
                continue
            kw = self.take()
            if kw.kind not in ("function", "const", "procedure", "type", "var"):
                raise SyntaxError(f"line {kw.line}: bad @define {kw.kind}")
            name = self.take("id").val
            args = False
            if self.opt("("):
                self.take(")")
                args = True
            if kw.kind == "type" and self.opt("="):
                lo = self.const_expr()
                self.take("..")
                hi = self.const_expr()
                out.append(("type", name, ("subrange", lo, hi)))
            else:
                out.append((kw.kind, name, args))
            self.take(";")
        return out

    # -- program -------------------------------------------------------------
    def program(self):
        defs = self.defines()
        self.take("program")
        name = self.take("id").val
        if self.opt("("):
            while not self.at(")"):
                self.take()
            self.take(")")
        self.take(";")
        blk = self.block(top=True)
        self.take("eof")
        return {"defines": defs, "name": name, **blk}

    def block(self, top=False):
        labels, consts, types, vars_, procs = [], [], [], [], []
        if self.opt("label"):
            labels.append(self.take("num").val)
            while self.opt(","):
                labels.append(self.take("num").val)
            self.take(";")
        if self.opt("const"):
            while self.at("id"):
                n = self.take("id").val
                self.take("=")
                consts.append((n, self.const_expr()))
                self.take(";")
        if self.opt("type"):
            while self.at("id", "cpp"):
                if self.opt("cpp"):
                    continue
                n = self.take("id").val
                self.take("=")
                types.append((n, self.type_()))
                self.take(";")
        if self.opt("var"):
            while self.at("id"):
                names = [self.take("id").val]
                while self.opt(","):
                    names.append(self.take("id").val)
                self.take(":")
                ty = self.type_()
                self.take(";")
                for n in names:
                    vars_.append((n, ty))
        while self.at("procedure", "function", "noreturn"):
            procs.append(self.proc())
            self.take(";")
        if top and self.at("eof"):  # web2c BODY: empty (TeX Live's main program is mainbody)
            body = None
        else:
            body = self.compound()
            if top:
                self.take(".")
        return {"labels": labels, "consts": consts, "types": types, "vars": vars_, "procs": procs, "body": body}

    def proc(self):
        noreturn = bool(self.opt("noreturn"))
        kind = self.take().kind
        if kind not in ("procedure", "function"):
            raise SyntaxError(f"line {self.peek().line}: expected procedure/function")
        name = self.take("id").val
        params = []
        if self.opt("("):
            while True:
                byref = bool(self.opt("var"))
                names = [self.take("id").val]
                while self.opt(","):
                    names.append(self.take("id").val)
                self.take(":")
                ty = self.type_()
                for n in names:
                    params.append((n, ty, byref))
                if not self.opt(";"):
                    break
            self.take(")")
        result = None
        if kind == "function":
            self.take(":")
            result = self.type_()
        self.take(";")
        blk = self.block()
        return {"kind": kind, "name": name, "params": params, "result": result, "noreturn": noreturn, **blk}

    # -- types ----------------------------------------------------------------
    def type_(self):
        if self.opt("^"):
            return ("ptr", self.type_())
        if self.opt("array"):
            self.take("[")
            idx = [self.index_type()]
            while self.opt(","):
                idx.append(self.index_type())
            self.take("]")
            self.take("of")
            return ("array", idx, self.type_())
        if self.opt("file"):
            self.take("of")
            return ("file", self.type_())
        if self.opt("record"):
            fields = []
            while not self.at("end"):
                if self.opt(";"):
                    continue
                names = [self.take("id").val]
                while self.opt(","):
                    names.append(self.take("id").val)
                self.take(":")
                ty = self.type_()
                for n in names:
                    fields.append((n, ty))
            self.take("end")
            return ("record", fields)
        # a named type or a subrange
        if self.at("id") and self.peek(1).kind != "..":
            return ("named", self.take("id").val)
        lo = self.sub_const()
        self.take("..")
        hi = self.sub_const()
        return ("subrange", lo, hi)

    def index_type(self):
        if self.at("id") and self.peek(1).kind != "..":
            return ("named", self.take("id").val)
        lo = self.sub_const()
        self.take("..")
        hi = self.sub_const()
        return ("subrange", lo, hi)

    def sub_const(self):
        # web2c SUBRANGE_CONSTANT: [+] number | constant or variable identifier
        self.opt("u+")
        if self.at("num"):
            return ("num", self.take().val)
        return ("id", self.take("id").val)

    def const_expr(self):
        return self.expr()

    # -- statements -----------------------------------------------------------
    def compound(self):
        self.take("begin")
        stmts = self.stat_list()
        self.take("end")
        return ("seq", stmts)

    def stat_list(self):
        stmts = [self.statement()]
        while self.opt(";"):
            stmts.append(self.statement())
        return stmts

    def statement(self):
        if self.at("num") and self.peek(1).kind == ":":
            n = self.take().val
            self.take(":")
            return ("label", n, self.statement())
        return self.unlab()

    def unlab(self):
        k = self.peek().kind
        if k == "begin":
            return self.compound()
        if k == "if":
            self.take()
            c = self.expr()
            self.take("then")
            s1 = self.unlab_or_empty()
            s2 = None
            if self.opt("else"):
                s2 = self.unlab_or_empty()
            return ("if", c, s1, s2)
        if k == "case":
            self.take()
            e = self.expr()
            self.take("of")
            arms = []
            while True:
                labs = [self.case_lab()]
                while self.opt(","):
                    labs.append(self.case_lab())
                self.take(":")
                arms.append((labs, self.unlab_or_empty()))
                if self.opt(";"):
                    if self.at("end"):
                        break
                    continue
                break
            self.take("end")
            return ("case", e, arms)
        if k == "while":
            self.take()
            c = self.expr()
            self.take("do")
            return ("while", c, self.unlab_or_empty())
        if k == "repeat":
            self.take()
            body = self.stat_list()
            self.take("until")
            return ("repeat", body, self.expr())
        if k == "for":
            self.take()
            v = self.take("id").val
            self.take(":=")
            a = self.expr()
            d = self.take().kind
            if d not in ("to", "downto"):
                raise SyntaxError(f"line {self.peek().line}: for without to/downto")
            b = self.expr()
            self.take("do")
            return ("for", v, a, d, b, self.unlab_or_empty())
        if k == "goto":
            self.take()
            return ("goto", self.take("num").val)
        if k == "break":
            self.take()
            return ("break",)
        if k == "id":
            target = self.variable()
            if self.opt(":="):
                return ("assign", target, self.expr())
            if target[0] == "id":
                return ("pcall", target[1], [])
            if target[0] == "call":
                return ("pcall", target[1], target[2])
            raise SyntaxError(f"line {self.peek().line}: statement {target}")
        return ("empty",)

    def unlab_or_empty(self):
        if self.at(";", "end", "else", "until"):
            return ("empty",)
        return self.statement()

    def case_lab(self):
        if self.opt("others"):
            return "others"
        return self.take("num").val

    # -- expressions ----------------------------------------------------------
    def variable(self):
        name = self.take("id").val
        e = ("id", name)
        if self.at("("):
            self.take("(")
            args = [self.actual()]
            while self.opt(","):
                args.append(self.actual())
            self.take(")")
            e = ("call", name, args)
        while True:
            if self.opt("["):
                idx = [self.expr()]
                while self.opt(","):
                    idx.append(self.expr())
                self.take("]")
                e = ("idx", e, idx)
            elif self.at(".") and self.peek(1).kind == "id":
                self.take(".")
                e = ("fld", e, self.take("id").val)
            elif self.at(".") and self.peek(1).kind == "num":
                raise SyntaxError(f"line {self.peek().line}: numeric field")
            else:
                return e

    def actual(self):
        e = self.expr()
        ws = []
        while self.opt(":"):
            ws.append(self.expr())
        return ("width", e, ws) if ws else e

    def expr(self, minprec=1):
        left = self.unary()
        while True:
            p = PREC.get(self.peek().kind)
            if p is None or p < minprec:
                return left
            op = self.take().kind
            left = ("bin", op, left, self.expr(p + 1))

    def unary(self):
        k = self.peek().kind
        if k in ("u-", "u+", "not"):
            self.take()
            op = {"u-": "neg", "u+": "pos", "not": "not"}[k]
            # UNARY_OP EXPRESS %prec '*': the operand extends over operators that bind
            # tighter than '*' only (none but the prefix operators themselves)
            return ("un", op, self.expr(UNARY_PREC + 1))
        return self.factor()

    def factor(self):
        tok = self.peek()
        if tok.kind == "(":
            self.take()
            e = self.expr()
            self.take(")")
            return ("paren", e)
        if tok.kind == "num":
            self.take()
            return ("num", tok.val)
        if tok.kind == "real":
            self.take()
            return ("real", tok.val)
        if tok.kind == "str":
            self.take()
            return ("str", tok.val)
        if tok.kind == "char":
            self.take()
            return ("char", tok.val)
        if tok.kind == "id":
            return self.variable()
        raise SyntaxError(f"line {tok.line}: unexpected {tok.kind} {tok.val!r} in expression")


def parse(text):
    return Parser(lex(text)).program()

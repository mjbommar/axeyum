"""Rewrite a nested-array benchmark into an array-free surrogate that is
**sound for `unsat`**, so the reach behind the parse refusal can be measured
BEFORE the IR change is built.

Why a surrogate at all
----------------------
`crates/axeyum-ir/src/sort.rs` refuses `(Array I (Array J E))` at parse, so not
one file of the blocked population has ever reached the solver.  Every number
published about that population so far has therefore been a count of files we
REFUSE, never a count of files we would DECIDE — and this repository has watched
that distinction collapse an estimate five times (143->6, 51->2, 173->10,
27,150->1,135, 19,620->0).  ADR-1955 sized the reach by transferring a
*family-matched control rate*; for AUFLIRA and AUFNIRA — 95% of the prize — ADR-
1955 itself records that **no family-matched control exists**, so that method
has nothing to say about exactly the part that matters.

This instrument answers the question directly instead.

The rewrite
-----------
For each distinct nested array sort `(Array I (Array J E))` in the file:

  * the sort is replaced by a fresh **uninterpreted** sort `NA_k`;
  * every `select` whose BASE has sort `NA_k` is replaced by a fresh
    uninterpreted function `na_sel_k : NA_k x I -> (Array J E)`.

So the outer level loses the array theory and keeps congruence; the inner level
keeps the array theory unchanged.

Soundness of the measurement
----------------------------
The rewrite DELETES axioms and adds none:

  * outer extensionality (`(forall i. a[i] = b[i]) -> a = b`) is lost, because
    `NA_k` is an uninterpreted carrier;
  * outer read-over-write is lost — which is why a file containing a `store`
    at the outer level is REFUSED by this script rather than rewritten (see
    `OuterStore`).  With no `store`, read-over-write has no instance.

`na_sel_k` is a function symbol, so `a = b -> a[i] = b[i]` (congruence) — the
only outer array axiom these files actually use — survives.

Deleting axioms weakens the formula: every model of the original is a model of
the surrogate.  Hence

    surrogate unsat  ==>  original unsat.

The converse does not hold, so a surrogate `sat` says NOTHING and is reported
as `sat-not-transferable`.  186 of AUFLIRA's 187 winnable files and 138 of
AUFNIRA's 139 carry `:status unsat`, so the sound direction is the one that
covers the population.

What the number means
---------------------
A surrogate `unsat` is a file whose refutation needs **no outer array theory at
all** — congruence through the nested read is enough.  That is a LOWER bound on
what an implementation that admits the sort can reach, and an upper bound on
nothing: a real implementation also has outer extensionality and read-over-write
available, so it can only do better.  Together with the census ceiling (20,399)
this brackets the build.

Usage
-----
    python3 nested_array_surrogate.py <in.smt2> <out.smt2>
    python3 nested_array_surrogate.py --self-test
"""

import re
import sys

# --------------------------------------------------------------------------
# s-expressions
# --------------------------------------------------------------------------

TOKEN = re.compile(r"""
      ;[^\n]*                 # line comment
    | \|[^|]*\|               # |quoted symbol|  (set-info bodies live here)
    | "(?:[^"]|"")*"          # string literal
    | [()]
    | [^\s()|";]+             # ordinary atom
""", re.VERBOSE)


class Refused(Exception):
    """The file is outside this surrogate's sound fragment."""


def tokenize(text):
    pos, out = 0, []
    n = len(text)
    while pos < n:
        if text[pos].isspace():
            pos += 1
            continue
        m = TOKEN.match(text, pos)
        if not m:
            raise Refused(f"lex error at offset {pos}: {text[pos:pos + 20]!r}")
        tok = m.group(0)
        pos = m.end()
        if tok.startswith(";"):
            continue
        out.append(tok)
    return out


def parse(tokens):
    """Returns a list of top-level forms; a form is a str or a list."""
    stack, forms = [], []
    for tok in tokens:
        if tok == "(":
            stack.append([])
        elif tok == ")":
            if not stack:
                raise Refused("unbalanced )")
            done = stack.pop()
            (stack[-1] if stack else forms).append(done)
        else:
            (stack[-1] if stack else forms).append(tok)
    if stack:
        raise Refused("unbalanced (")
    return forms


def render(form, out):
    if isinstance(form, str):
        out.append(form)
        return
    out.append("(")
    for i, sub in enumerate(form):
        if i:
            out.append(" ")
        render(sub, out)
    out.append(")")


def text_of(form):
    out = []
    render(form, out)
    return "".join(out)


# --------------------------------------------------------------------------
# sorts
# --------------------------------------------------------------------------

def is_nested_array(sort):
    """`(Array I (Array J E))` — an array whose ELEMENT is an array."""
    return (
        isinstance(sort, list)
        and len(sort) == 3
        and sort[0] == "Array"
        and isinstance(sort[2], list)
        and len(sort[2]) == 3
        and sort[2][0] == "Array"
    )


def deeper_nesting(sort):
    """Nesting the surrogate does not model: an array INDEX that is an array,
    or three levels of element nesting.  Refused rather than mis-rewritten."""
    if not isinstance(sort, list) or not sort or sort[0] != "Array":
        return False
    if len(sort) != 3:
        return True
    index, element = sort[1], sort[2]
    if isinstance(index, list) and index and index[0] == "Array":
        return True
    return is_nested_array(element)


class Surrogate:
    def __init__(self):
        # nested-sort text -> (carrier sort name, selector name, row sort)
        self.nested = {}
        # symbol -> its sort form, for 0-arity declarations
        self.const_sort = {}
        # function name -> result sort form
        self.result_sort = {}

    def carrier(self, sort):
        key = text_of(sort)
        if key not in self.nested:
            k = len(self.nested)
            self.nested[key] = (f"NA_{k}", f"na_sel_{k}", sort[1], sort[2])
        return self.nested[key]

    # -- sort rewriting ----------------------------------------------------

    def rw_sort(self, sort):
        if deeper_nesting(sort):
            raise Refused(f"nesting deeper than one level: {text_of(sort)}")
        if is_nested_array(sort):
            return self.carrier(sort)[0]
        if isinstance(sort, list):
            return [self.rw_sort(s) for s in sort]
        return sort

    def is_carrier(self, sort_name):
        return any(v[0] == sort_name for v in self.nested.values())

    # -- term sort inference (only "is it a carrier?" is needed) -----------

    def term_is_carrier(self, term, env):
        """`env` maps a bound/let name to True when it has carrier sort."""
        if isinstance(term, str):
            if term in env:
                return env[term]
            return self.const_sort.get(term) is True
        if not term:
            return False
        head = term[0]
        if head in ("forall", "exists", "let"):
            # handled by the caller's rewriter; a quantifier is Bool
            return False
        if isinstance(head, str):
            return self.result_sort.get(head) is True
        return False


# --------------------------------------------------------------------------
# the rewrite
# --------------------------------------------------------------------------

ARRAY_OPS_ON_OUTER = ("store",)


def rewrite(text):
    s = Surrogate()
    forms = parse(tokenize(text))
    out = []
    preamble_at = None

    for form in forms:
        if isinstance(form, str):
            out.append(form)
            continue
        head = form[0] if form else None

        if head == "set-logic":
            out.append(form)
            preamble_at = len(out)
            continue

        if head == "declare-sort":
            out.append(form)
            continue

        if head == "define-sort":
            raise Refused("define-sort alias: surrogate does not expand aliases")

        if head in ("declare-fun", "declare-const"):
            if head == "declare-const":
                name, params, result = form[1], [], form[2]
            else:
                name, params, result = form[1], form[2], form[3]
            new_params = [s.rw_sort(p) for p in params]
            new_result = s.rw_sort(result)
            is_carrier_result = isinstance(new_result, str) and s.is_carrier(new_result)
            if params:
                s.result_sort[name] = is_carrier_result
            else:
                s.const_sort[name] = is_carrier_result
                s.result_sort[name] = is_carrier_result
            out.append(["declare-fun", name, new_params, new_result])
            continue

        if head in ("define-fun", "define-fun-rec"):
            raise Refused("define-fun: surrogate does not inline definitions")

        if head == "assert":
            out.append(["assert", rw_term(s, form[1], {})])
            continue

        out.append(form)

    if not s.nested:
        raise Refused("no nested array sort in this file")

    decls = []
    for _, (carrier, sel, index_sort, row_sort) in sorted(
        s.nested.items(), key=lambda kv: kv[1][0]
    ):
        decls.append(["declare-sort", carrier, "0"])
        decls.append(["declare-fun", sel, [carrier, index_sort], row_sort])
    at = preamble_at if preamble_at is not None else 0
    out[at:at] = decls

    return "\n".join(text_of(f) for f in out) + "\n"


def rw_term(s, term, env):
    if isinstance(term, str):
        return term
    if not term:
        return term
    head = term[0]

    if head in ("forall", "exists"):
        binders, new_env = [], dict(env)
        for b in term[1]:
            sort = s.rw_sort(b[1])
            new_env[b[0]] = isinstance(sort, str) and s.is_carrier(sort)
            binders.append([b[0], sort])
        return [head, binders, rw_term(s, term[2], new_env)]

    if head == "let":
        bindings, new_env = [], dict(env)
        for b in term[1]:
            value = rw_term(s, b[1], env)
            # sort of the ORIGINAL value under the OUTER env (parallel let)
            new_env[b[0]] = s.term_is_carrier(b[1], env)
            bindings.append([b[0], value])
        return ["let", bindings, rw_term(s, term[2], new_env)]

    if head == "!":
        return ["!"] + [rw_term(s, term[1], env)] + term[2:]

    if head == "select" and len(term) == 3:
        base = term[1]
        if s.term_is_carrier(base, env):
            sel = None
            for _, v in s.nested.items():
                if v[0] == carrier_of(s, base, env):
                    sel = v[1]
                    break
            if sel is None:
                raise Refused("select on a carrier whose selector is unknown")
            return [sel, rw_term(s, base, env), rw_term(s, term[2], env)]
        return ["select", rw_term(s, base, env), rw_term(s, term[2], env)]

    if head in ARRAY_OPS_ON_OUTER and len(term) >= 2:
        if s.term_is_carrier(term[1], env):
            raise Refused(
                "outer-level `store`: read-over-write at the outer level is "
                "exactly the axiom this surrogate deletes, so a file using it "
                "is outside the sound fragment"
            )

    if head == "as" or (isinstance(head, list) and head and head[0] == "as"):
        # `((as const (Array I (Array J E))) v)` builds an outer array value.
        raise Refused("`as const` at the outer level is outside the fragment")

    return [rw_term(s, sub, env) if not isinstance(sub, str) else sub for sub in term]


def carrier_of(s, term, env):
    """Which carrier sort a carrier-sorted term has.  With a single nested
    sort in the file (every measured division has exactly one) this is the only
    one; more than one and the term's declaration decides."""
    names = sorted({v[0] for v in s.nested.values()})
    if len(names) == 1:
        return names[0]
    raise Refused("more than one distinct nested array sort in one file")


# --------------------------------------------------------------------------

SELF_TEST = """(set-logic AUFLIRA)
(declare-fun m () (Array Int (Array Int Real)))
(declare-fun r () (Array Int Real))
(declare-fun t ((Array Int (Array Int Real))) (Array Int (Array Int Real)))
(declare-fun i () Int)
(declare-fun j () Int)
(assert (forall ((?A (Array Int (Array Int Real))) (?I Int) (?J Int))
  (= (select (select (t ?A) ?I) ?J) (select (select ?A ?J) ?I))))
(assert (let ((?v (t m))) (not (= (select (select ?v i) j) (select (select m j) i)))))
(check-sat)
"""

STORE_TEST = """(set-logic AUFLIRA)
(declare-fun m () (Array Int (Array Int Real)))
(declare-fun r () (Array Int Real))
(declare-fun i () Int)
(assert (not (= (select (store m i r) i) r)))
(check-sat)
"""


def self_test():
    got = rewrite(SELF_TEST)
    checks = [
        ("carrier declared", "(declare-sort NA_0 0)" in got),
        ("selector declared", "(declare-fun na_sel_0 (NA_0 Int) (Array Int Real))" in got),
        ("no nested sort survives", "(Array Int (Array Int Real))" not in got),
        ("outer select rewritten", "(na_sel_0 " in got),
        ("inner select kept", "(select (na_sel_0 " in got),
        ("let-bound carrier tracked", "(na_sel_0 ?v i)" in got),
        ("binder carrier tracked", "(na_sel_0 (t ?A) ?I)" in got),
        ("flat row sort untouched", "(declare-fun r () (Array Int Real))" in got),
    ]
    ok = True
    for name, passed in checks:
        print(f"  {'ok  ' if passed else 'FAIL'} {name}")
        ok &= passed
    try:
        rewrite(STORE_TEST)
        print("  FAIL outer store is refused")
        ok = False
    except Refused as e:
        print(f"  ok   outer store is refused ({str(e)[:40]}...)")
    print(got)
    return 0 if ok else 1


def main(argv):
    if len(argv) == 2 and argv[1] == "--self-test":
        return self_test()
    if len(argv) != 3:
        print(__doc__)
        return 2
    try:
        with open(argv[1], "r", errors="replace") as fh:
            got = rewrite(fh.read())
    except Refused as e:
        print(f"REFUSED {argv[1]}: {e}", file=sys.stderr)
        return 3
    with open(argv[2], "w") as fh:
        fh.write(got)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))

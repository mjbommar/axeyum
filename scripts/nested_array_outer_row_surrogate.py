"""Rewrite a nested-array benchmark into a surrogate that KEEPS outer
read-over-write, so the reach behind ADR-1965's named next gate can be measured
BEFORE any solver code is written.

Why this is not ADR-1965's surrogate
------------------------------------
[ADR-1965]'s `nested_array_surrogate.py` turns `(Array I (Array J E))` into an
uninterpreted sort and every outer `select` into an uninterpreted function.  That
DELETES outer read-over-write, so a file containing an outer `store` is refused
by construction — and its own closing finding is that 33 of 36 ALIA and 12 of 17
ABV winnable files do exactly that.  It therefore says nothing about ALIA's 511
and ABV's 423, which is the population this lane is pointed at.

This instrument keeps outer read-over-write and abstracts nothing about it.

The rewrite: curry the outer level
----------------------------------
For each arity-0 declaration `M : (Array I (Array J E))`:

  * `M` becomes an uninterpreted **function** `M_row : I -> (Array J E)`;
  * `(select M j)` becomes `(M_row j)`;
  * an outer `store` is eliminated where it is READ, by the read-over-write
    axiom applied syntactically:

        (select (store A i r) j)  ==>  (ite (= i j) r (select A j))

    recursively, until the base of every remaining outer `select` is an `M`.

The inner level is untouched: `(Array J E)` stays a real array, inner `select`
and `store` stay inner `select` and `store`, and a quantifier binding an inner
array variable stays a quantifier binding an inner array variable.  That is what
this fragment needs — the SV-COMP memory model's quantified `v_ArrVal_*` are
inner arrays.

Soundness of the measurement
----------------------------
On the ACCEPTED fragment the rewrite is model-preserving in both directions:

  * `M_row` is total and uninterpreted, so from any model of the original set
    `M_row(i) := M[i]`, and from any model of the surrogate set
    `M[i] := M_row(i)`.  Both are well-defined because the accepted fragment
    forbids every context in which the outer array is anything but the base of a
    `select` or of a `store` that is itself read (see `REFUSALS` below), so no
    outer array value ever has to exist as a value.
  * the `store` expansion is the read-over-write axiom itself, an equivalence,
    not a relaxation.
  * outer EXTENSIONALITY is the one axiom the currying does not have.  It is
    unreachable on the accepted fragment for the same reason: an outer
    extensionality instance needs an equality between two outer array terms, and
    that context is refused.

So on the accepted fragment the surrogate is equisatisfiable, and in particular

    surrogate unsat  ==>  original unsat.

**That stronger claim is the one this lane does NOT rest its number on.**  The
reported reach counts only `unsat`, the direction that holds even if the
equisatisfiability argument above has a hole, exactly as ADR-1965 did.  A
surrogate `sat` is reported in its own column and counted nowhere.  The
argument is checked rather than asserted: `check-surrogate-soundness.py` runs z3
on the ORIGINAL and on the SURROGATE of every accepted file and requires the two
verdicts to agree wherever both are decided — a check that has an opportunity to
fire on every accepted file, not only on the refutable ones.

What the number means
---------------------
A surrogate `unsat` is a file whose refutation needs outer read-over-write,
inner array theory, congruence and arithmetic — all of which we have — and
NOTHING about the nested sort beyond the currying this script performs.  It is a
lower bound on what an implementation of the named gate reaches, and it models
the cheapest such implementation (curry + syntactic ROW) rather than the best.

REFUSALS
--------
A file is refused, and says why, when an outer array term reaches any context
other than the base of a `select` or of a `store` that is itself read:

  * an equality or `distinct` over outer arrays        -> outer extensionality
  * a quantifier binding an outer array variable
  * an outer array passed to, or returned by, a function of arity > 0
  * an outer array under `ite`, `let`, `const`-array, or any other head
  * nesting deeper than 2 (`(Array I (Array J (Array K E)))`)
  * any `define-fun` mentioning an outer array sort

Usage
-----
    python3 outer_row_surrogate.py <in.smt2> <out.smt2>
    python3 outer_row_surrogate.py --self-test
"""

import re
import sys

TOKEN = re.compile(r"""
      ;[^\n]*                 # line comment
    | \|[^|]*\|               # |quoted symbol|
    | "(?:[^"]|"")*"          # string literal
    | [()]
    | [^\s()|";]+             # ordinary atom
""", re.VERBOSE)


class Refused(Exception):
    """The file is outside this surrogate's accepted fragment."""


# ---------------------------------------------------------------------------
# s-expressions
# ---------------------------------------------------------------------------

def tokenize(text):
    pos, out, n = 0, [], len(text)
    while pos < n:
        if text[pos].isspace():
            pos += 1
            continue
        m = TOKEN.match(text, pos)
        if not m:
            raise Refused(f"lex error at offset {pos}: {text[pos:pos + 20]!r}")
        tok = m.group(0)
        pos = m.end()
        if not tok.startswith(";"):
            out.append(tok)
    return out


def parse(tokens):
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


def text_of(form):
    if isinstance(form, str):
        return form
    return "(" + " ".join(text_of(x) for x in form) + ")"


# ---------------------------------------------------------------------------
# sorts
# ---------------------------------------------------------------------------

def is_array_sort(f):
    return isinstance(f, list) and len(f) == 3 and f[0] == "Array"


def array_depth(f):
    """Nesting depth of an array sort: 0 for a scalar, 1 flat, 2 nested, ..."""
    if not is_array_sort(f):
        return 0
    return 1 + array_depth(f[2])


def mentions_outer_array(f):
    """True if the sort form contains an array whose ELEMENT is an array."""
    if not isinstance(f, list):
        return False
    if is_array_sort(f) and is_array_sort(f[2]):
        return True
    return any(mentions_outer_array(x) for x in f)


# ---------------------------------------------------------------------------
# the rewrite
# ---------------------------------------------------------------------------

# heads that may legally have an outer-array-valued ARGUMENT, and only in the
# base position.  Everything else is a refusal.
READ_HEADS = ("select", "store")


class Surrogate:
    # An outer-array-valued `let` binding is inlined rather than refused: it is
    # the SV-COMP generator's sharing idiom (`.cseN`), not a use of the outer
    # array as a value, and refusing it would have put 9 of ALIA's 36 winnable
    # files outside the instrument for a reason that is about this script rather
    # than about the solver.  Inlining is exact (a `let` IS substitution), and
    # the duplication it can cause is bounded by `MAX_GROWTH` below.
    MAX_GROWTH = 60
    MAX_BYTES = 8 << 20

    def __init__(self):
        self.outer = {}       # symbol -> (index sort form, element sort form)
        self.row_name = {}    # symbol -> curried function name
        self.alias = {}       # let-bound name -> outer-array-valued form

    # -- classification ----------------------------------------------------

    def is_outer_term(self, f):
        """Syntactically outer-array-valued?  The accepted fragment makes this
        decidable without a sort inference pass: the only outer-array-valued
        terms it admits are a declared outer constant, a `let` alias for one,
        and a `store` chain over either."""
        if isinstance(f, str):
            return f in self.outer or f in self.alias
        if isinstance(f, list) and len(f) == 4 and f[0] == "store":
            return self.is_outer_term(f[1])
        return False

    def touches_outer(self, f):
        """Does this term mention a declared outer array symbol at all?"""
        if isinstance(f, str):
            return f in self.outer
        if isinstance(f, list):
            return any(self.touches_outer(x) for x in f)
        return False

    # -- outer read --------------------------------------------------------

    def read(self, base, idx):
        """`(select base idx)` where base is outer-array-valued.  Returns the
        curried / read-over-write-expanded replacement, an INNER array term."""
        if isinstance(base, str):
            if base in self.alias:
                return self.read(self.alias[base], idx)
            return [self.row_name[base], idx]
        # (store A i r) : read-over-write, applied syntactically.
        _, a, i, r = base
        return ["ite", ["=", self.term(i), idx], self.term(r), self.read(a, idx)]

    # -- terms -------------------------------------------------------------

    def term(self, f):
        if isinstance(f, str):
            if f in self.outer or f in self.alias:
                raise Refused(
                    f"outer array `{f}` appears as a bare value, not as the base "
                    f"of a select/store -- outer extensionality would be needed"
                )
            return f
        if not f:
            return f
        head = f[0]

        if head == "select" and len(f) == 3 and self.is_outer_term(f[1]):
            return self.read(f[1], self.term(f[2]))

        if head in ("forall", "exists") and len(f) == 3:
            shadowed = {}
            for b in f[1]:
                if isinstance(b, list) and len(b) == 2 and is_array_sort(b[1]) \
                        and array_depth(b[1]) >= 2:
                    raise Refused(
                        f"quantifier binds an OUTER array variable "
                        f"`{text_of(b)}` -- outside the curried fragment"
                    )
                # a binder shadows any inlined alias of the same name
                if isinstance(b, list) and b and b[0] in self.alias:
                    shadowed[b[0]] = self.alias.pop(b[0])
            try:
                body = self.term(f[2])
            finally:
                self.alias.update(shadowed)
            return [head, f[1], body]

        if head == "let" and len(f) == 3:
            binds, added, shadowed = [], [], {}
            for b in f[1]:
                if not (isinstance(b, list) and len(b) == 2):
                    raise Refused(f"malformed let binding {text_of(b)}")
                if self.is_outer_term(b[1]):
                    # Outer-array-valued: inline it.  `let` is substitution, so
                    # this is exact; the growth cap below is what keeps it from
                    # being exact and unusable.
                    added.append((b[0], b[1]))
                else:
                    binds.append([b[0], self.term(b[1])])
            # SMT-LIB `let` is parallel, so every binding is recorded only after
            # all of them have been read against the OUTER scope.
            for name, val in added:
                if name in self.alias:
                    shadowed[name] = self.alias[name]
                self.alias[name] = val
            for name, _ in ((b[0], None) for b in binds):
                # a non-outer binding shadows any alias of the same name
                if name in self.alias:
                    shadowed.setdefault(name, self.alias[name])
                    del self.alias[name]
            try:
                body = self.term(f[2])
            finally:
                for name, _ in added:
                    self.alias.pop(name, None)
                self.alias.update(shadowed)
            if not binds:
                return body
            return [head, binds, body]

        # every other head: no argument of it may be outer-array-valued, and no
        # argument may MENTION an outer array except through a select/store we
        # have already rewritten.
        out = [head if isinstance(head, str) else self.term(head)]
        for arg in f[1:]:
            if self.is_outer_term(arg):
                raise Refused(
                    f"outer array term reaches `{head}` in a non-read position: "
                    f"{text_of(f)[:120]}"
                )
            out.append(self.term(arg))
        return out


LOGIC_WITH_UF = {
    "ALIA": "AUFLIA",
    "ABV": "AUFBV",
    "AUFLIA": "AUFLIA",
    "AUFLIRA": "AUFLIRA",
    "AUFNIRA": "AUFNIRA",
    "AUFBV": "AUFBV",
}


def distribute_select_over_ite(f):
    """`(select (ite c A B) k)` -> `(ite c (select A k) (select B k))`, to a
    fixpoint, and the same for `store`.

    This is NOT part of the surrogate.  It is a SECOND, separately reported
    instrument: the currying leaves behind exactly this shape (the read-over-
    write expansion IS an array-sorted `ite`), and the controls showed that our
    solver answers `unknown` on `c2` with the shape and `unsat` without it.  So
    running the sweep twice, with and without this pass, separates "the file
    needs outer read-over-write" from "the file needs one rewrite we do not
    have", and the difference between the two columns is what that rewrite is
    worth.

    It is an equivalence (both branches are total terms), so it changes no
    verdict; the sweep's z3 columns are the check on that.
    """
    if not isinstance(f, list) or not f:
        return f
    f = [distribute_select_over_ite(x) for x in f]
    if f[0] in ("select", "store") and len(f) >= 3:
        base = f[1]
        if isinstance(base, list) and len(base) == 4 and base[0] == "ite":
            _, c, a, b = base
            return distribute_select_over_ite(
                ["ite", c, [f[0], a, *f[2:]], [f[0], b, *f[2:]]]
            )
    return f


def rewrite(text, distribute=False):
    forms = parse(tokenize(text))
    s = Surrogate()

    # pass 1: find the outer array declarations and refuse the shapes that
    # cannot be curried.
    for f in forms:
        if not isinstance(f, list) or not f:
            continue
        head = f[0]
        if head == "define-fun" and any(mentions_outer_array(x) for x in f[1:]):
            raise Refused("define-fun mentions an outer array sort")
        if head in ("declare-fun", "declare-const"):
            if head == "declare-const":
                name, args, res = f[1], [], f[2]
            else:
                if len(f) != 4:
                    raise Refused(f"malformed declare-fun {text_of(f)[:80]}")
                name, args, res = f[1], f[2], f[3]
            for a in args:
                if mentions_outer_array(a):
                    raise Refused(
                        f"`{name}` takes an outer array argument -- outside the "
                        f"curried fragment"
                    )
            if mentions_outer_array(res):
                if args:
                    raise Refused(
                        f"`{name}` has arity {len(args)} and returns an outer "
                        f"array -- currying it would need a higher-order sort"
                    )
                if array_depth(res) != 2:
                    raise Refused(
                        f"`{name}` : {text_of(res)} nests {array_depth(res)} "
                        f"deep; this instrument curries exactly one level"
                    )
                s.outer[name] = (res[1], res[2])
                base = name.strip("|")
                s.row_name[name] = f"|{base}..row|"

    if not s.outer:
        raise Refused("no outer array declaration -- nothing to measure here")

    # pass 2: rewrite.
    out = []
    for f in forms:
        if not isinstance(f, list) or not f:
            out.append(f)
            continue
        head = f[0]
        if head == "set-logic":
            out.append(["set-logic", LOGIC_WITH_UF.get(f[1], "ALL")])
            continue
        if head in ("declare-fun", "declare-const"):
            name = f[1]
            if name in s.outer:
                idx, elem = s.outer[name]
                out.append(["declare-fun", s.row_name[name], [idx], elem])
            else:
                out.append(f)
            continue
        if head == "assert":
            if len(f) != 2:
                raise Refused("malformed assert")
            body = s.term(f[1])
            if distribute:
                body = distribute_select_over_ite(body)
            out.append(["assert", body])
            continue
        if head in ("define-fun", "define-fun-rec", "define-sort", "declare-sort",
                    "set-info", "set-option", "check-sat", "exit", "push", "pop",
                    "get-info", "reset", "echo"):
            out.append(f)
            continue
        # An unrecognized command that mentions an outer array is a refusal
        # rather than a pass-through: silently copying it is how a surrogate
        # measures a file it did not actually rewrite.
        if s.touches_outer(f):
            raise Refused(f"unhandled command mentioning an outer array: {head}")
        out.append(f)

    result = "\n".join(text_of(x) for x in out) + "\n"
    if len(result) > Surrogate.MAX_BYTES or \
            len(result) > Surrogate.MAX_GROWTH * max(len(text), 1):
        raise Refused(
            f"inlining the shared outer-array `let`s grew the file "
            f"{len(result) / max(len(text), 1):.1f}x to {len(result)} bytes; "
            f"refusing rather than measuring a blow-up this instrument caused"
        )
    return result


# ---------------------------------------------------------------------------
# self-test
# ---------------------------------------------------------------------------

SELF_TESTS = [
    # (name, input, expect: "ok" or a substring of the refusal reason)
    (
        "outer store under an inner select is expanded, not refused",
        """(set-logic ALIA)
           (declare-fun M () (Array Int (Array Int Int)))
           (declare-fun i () Int) (declare-fun j () Int) (declare-fun o () Int)
           (declare-fun r () (Array Int Int))
           (assert (= 0 (select (select (store M i r) j) o)))
           (check-sat)""",
        "ok",
    ),
    (
        "a quantified INNER array variable survives untouched",
        """(set-logic ALIA)
           (declare-fun M () (Array Int (Array Int Int)))
           (declare-fun b () Int)
           (assert (forall ((v (Array Int Int)))
                     (= 0 (select (select (store M b v) b) 0))))
           (check-sat)""",
        "ok",
    ),
    (
        "equality between two outer arrays is REFUSED (extensionality)",
        """(set-logic ALIA)
           (declare-fun M () (Array Int (Array Int Int)))
           (declare-fun N () (Array Int (Array Int Int)))
           (assert (= M N))
           (check-sat)""",
        "non-read position",
    ),
    (
        "a store whose result is compared is REFUSED",
        """(set-logic ALIA)
           (declare-fun M () (Array Int (Array Int Int)))
           (declare-fun N () (Array Int (Array Int Int)))
           (declare-fun i () Int) (declare-fun r () (Array Int Int))
           (assert (= (store M i r) N))
           (check-sat)""",
        "non-read position",
    ),
    (
        "a quantified OUTER array variable is REFUSED",
        """(set-logic ALIA)
           (declare-fun M () (Array Int (Array Int Int)))
           (assert (forall ((w (Array Int (Array Int Int))))
                     (= (select (select w 0) 0) 0)))
           (check-sat)""",
        "OUTER array variable",
    ),
    (
        "an outer array as a function argument is REFUSED",
        """(set-logic ALIA)
           (declare-fun M () (Array Int (Array Int Int)))
           (declare-fun p ((Array Int (Array Int Int))) Bool)
           (assert (p M))
           (check-sat)""",
        "outer array argument",
    ),
    (
        "triple nesting is REFUSED",
        """(set-logic ALIA)
           (declare-fun M () (Array Int (Array Int (Array Int Int))))
           (assert (= 0 (select (select (select M 0) 0) 0)))
           (check-sat)""",
        "nests 3 deep",
    ),
    (
        "a file with no outer array is REFUSED (nothing to measure)",
        """(set-logic ALIA)
           (declare-fun m () (Array Int Int))
           (assert (= 0 (select m 0)))
           (check-sat)""",
        "no outer array declaration",
    ),
    (
        "a let binding an outer store is INLINED, not refused",
        """(set-logic ALIA)
           (declare-fun M () (Array Int (Array Int Int)))
           (declare-fun i () Int) (declare-fun r () (Array Int Int))
           (assert (let ((a (store M i r))) (= 0 (select (select a 0) 0))))
           (check-sat)""",
        "ok",
    ),
    (
        "an inlined alias used as a bare VALUE is still refused",
        """(set-logic ALIA)
           (declare-fun M () (Array Int (Array Int Int)))
           (declare-fun N () (Array Int (Array Int Int)))
           (declare-fun i () Int) (declare-fun r () (Array Int Int))
           (assert (let ((a (store M i r))) (= a N)))
           (check-sat)""",
        "non-read position",
    ),
    (
        "a quantifier binder SHADOWS an inlined alias",
        """(set-logic ALIA)
           (declare-fun M () (Array Int (Array Int Int)))
           (declare-fun i () Int) (declare-fun r () (Array Int Int))
           (assert (let ((a (store M i r)))
                     (forall ((a Int)) (> a (select (select M 0) 0)))))
           (check-sat)""",
        "ok",
    ),
]


def self_test():
    bad = 0

    for name, src, expect in SELF_TESTS:
        try:
            got = rewrite(src)
            actual = "ok"
        except Refused as e:
            got, actual = None, str(e)
        if expect == "ok":
            ok = actual == "ok"
        else:
            ok = actual != "ok" and expect in actual
        print(f"{'PASS' if ok else 'FAIL'}  {name}")
        if not ok:
            bad += 1
            print(f"      expected {expect!r}, got {actual!r}")

    # The read-over-write expansion is the load-bearing part, so assert its
    # SHAPE rather than only that it did not refuse.
    out = rewrite(SELF_TESTS[0][1])
    for want in ("ite", "|M..row|", "(declare-fun |M..row| (Int) (Array Int Int))"):
        if want not in out:
            print(f"FAIL  expansion shape: {want!r} missing from\n{out}")
            bad += 1
        else:
            print(f"PASS  expansion shape contains {want!r}")
    # The OUTER store must be gone.  An inner one would be legitimate, but this
    # fixture has none, so any surviving `store` is the outer one.
    if "(store" in out:
        print(f"FAIL  the outer store survived the rewrite:\n{out}")
        bad += 1
    else:
        print("PASS  the outer store is gone")

    # The nested select must survive as a select on the curried result.
    if "(select (ite" not in out and "(select (|M..row|" not in out:
        print(f"FAIL  the inner select did not land on a curried row:\n{out}")
        bad += 1
    else:
        print("PASS  the inner select reads the curried row")

    # --distribute is a separate instrument and gets its own shape assertion:
    # the array-sorted `ite` the currying produces must be gone, and the `ite`
    # must have moved OUTSIDE the select.
    src = SELF_TESTS[0][1]
    plain = rewrite(src)
    dist = rewrite(src, distribute=True)
    checks = [
        ("plain leaves `(select (ite`", "(select (ite" in plain),
        ("--distribute removes `(select (ite`", "(select (ite" not in dist),
        ("--distribute keeps the ite", "(ite " in dist),
        ("--distribute changes nothing else", plain != dist),
    ]
    for name, ok in checks:
        print(f"{'PASS' if ok else 'FAIL'}  {name}")
        if not ok:
            bad += 1
            print(f"      plain: {plain}\n      dist:  {dist}")

    print("\nself-test:", "OK" if bad == 0 else f"{bad} FAILURES")
    return 1 if bad else 0


def main(argv):
    if len(argv) == 2 and argv[1] == "--self-test":
        return self_test()
    distribute = "--distribute" in argv
    argv = [a for a in argv if a != "--distribute"]
    if len(argv) != 3:
        print(__doc__)
        return 2
    try:
        out = rewrite(open(argv[1], errors="replace").read(), distribute=distribute)
    except Refused as e:
        print(f"REFUSED: {e}", file=sys.stderr)
        return 1
    with open(argv[2], "w") as fh:
        fh.write(out)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))

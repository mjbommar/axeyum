#!/usr/bin/env python3
"""QUANT-INSTANCE-PROBE -- name the GROUND CONSEQUENCE of each `quant-inst`
step z3's own refutation proof actually used, as an assertable SMT-LIB term.

    z3-proof-instances.py <proof-file> [--json] [--count] [--applications]

ADR-2113 named the terms z3 substitutes (`bench-results/uflia-trace-20260915/
proof-instances.py`) but never the GROUND FORMULA those substitutions produce.
This tool closes that gap: it walks z3's `(get-proof)` output for every
`((_ quant-inst t1 .. tn) F)` application -- `quant-inst`'s own shape is a
LEAF proof step, like `asserted`: the indexed identifier's trailing tokens are
the substituted terms, and its single argument `F` IS the step's conclusion,
which is always the tautology `(or (not <quantified-formula>) <body[t]>)` --
and extracts `<body[t]>`, the one ground consequence a caller can `assert`
directly (sound because `forall x. P(x)` entails `P(t)` for every ground `t`,
regardless of what triggered the substitution).

Verified against a hand-built fixture in `scripts/tests/fixtures/
z3-proof-instances-sample.proof` (`forall x. f(x) = x + 1`, asserted `a = 5`,
negated `f(a) = 6`): the proof contains exactly one `(_ quant-inst 5)` step
and this tool recovers `(= (+ 5 (* (- 1) (f 5))) (- 1))` -- z3's own
internally-rewritten form of `f(5) = 5 + 1`, not the surface syntax, because
the proof operates over z3's normalized body. That is expected and sound: the
recovered term still uses only symbols the query itself declared.

# Why the conclusion, not the substituted terms

`proof-instances.py`'s `t1..tn` name WHICH ground terms were used, which
answers a term-CONSTRUCTION question (`ground-membership.py`'s: did we ever
build this term). It does not answer a term-SELECTION or ground-REFUTATION
question, because `t1..tn` alone is not a formula -- rebuilding `body[t]` from
bare substitution values requires re-deriving which bound variable maps to
which term and re-parsing the (possibly internally-rewritten) quantifier body,
which this tool avoids entirely by reading the conclusion z3 already computed.

# Parsing discipline (matches `proof-instances.py`, restated because reusing
# the reasoning without reading the code first is how a new bug ships)

- The tokenizer and s-expression parser are both ITERATIVE. A z3 proof nests
  `let` hundreds to thousands deep and a recursive descent dies on the
  interpreter's own stack before reaching the first `quant-inst`.
- `let` names are collected into ONE flat environment and substituted to a
  bounded fixpoint (`--depth`, default 200) -- z3's own output is acyclic, but
  an unbounded expander on a TRUNCATED proof is how a lane reached 63 GB
  (CLAUDE.md, Measuring anything).
- A `(_ quant-inst t1 .. tn)` node is found the same way
  `proof-instances.py.find_quant_inst` finds it (`cur[0] == "_"` and
  `cur[1] == "quant-inst"`), so the two tools' RAW occurrence counts stay
  comparable at the same denominator (`--count` here should equal `wc -l` of
  `proof-instances.py`'s INSTANCE lines on the same proof) -- and separately
  this tool looks for the 2-element PARENT application
  `((_ quant-inst ..) F)` to recover `F`, the conclusion.

# Positive control

`--applications`/`--count` land at the SAME raw occurrence count
`proof-instances.py` reports on the same file, because both walk for the
identical `(_ quant-inst ..)` node shape; that equality is this tool's own
self-check and is exercised in `scripts/tests/test_z3_proof_instances.py`.
"""

from __future__ import annotations

import json
import sys
from typing import Optional


def tokenize(text: str) -> list:
    out: list = []
    i = 0
    n = len(text)
    while i < n:
        c = text[i]
        if c in "()":
            out.append(c)
            i += 1
        elif c.isspace():
            i += 1
        elif c == "|":
            j = text.index("|", i + 1)
            out.append(text[i : j + 1])
            i = j + 1
        elif c == ";":
            j = text.find("\n", i)
            i = n if j < 0 else j + 1
        else:
            j = i
            while j < n and not text[j].isspace() and text[j] not in "()|;":
                j += 1
            out.append(text[i:j])
            i = j
    return out


def parse(tokens: list) -> object:
    """Iterative s-expression parse over a FLAT token list (no positions),
    returning the FIRST complete top-level form and ignoring anything after
    it. z3's `(get-proof)` output is `((set-logic ..) (proof ..))` -- a
    2-element wrapper -- and this tool's callers start scanning from
    `(proof` (or `(let ` for a bare proof body), which leaves the wrapper's
    own closing paren dangling after the `(proof ...)` form completes. A
    parser that demands the WHOLE remaining text balance to exactly one form
    would reject that valid input; stopping at the first complete form
    (matching `proof-instances.py.parse`'s behaviour) is the correct read."""
    stack: list = []
    cur: list = []
    for t in tokens:
        if t == "(":
            stack.append(cur)
            cur = []
        elif t == ")":
            if not stack:
                raise ValueError("unbalanced ) in proof (before any form opened)")
            done = cur
            cur = stack.pop()
            cur.append(done)
            if not stack:
                # The form that opened at depth 0 just closed.
                return done
        else:
            cur.append(t)
    raise ValueError("unbalanced ( at end of proof -- no top-level form closed")


def render(node) -> str:
    if isinstance(node, str):
        return node
    return "(" + " ".join(render(x) for x in node) + ")"


def collect_lets(node, env: dict) -> None:
    """One flat pass recording every `let` binding met anywhere in the proof.
    z3 emits the whole proof as a SINGLE `let` chain and never rebinds a name,
    so one flat environment is correct and nothing is shadowed."""
    stack = [node]
    while stack:
        cur = stack.pop()
        if isinstance(cur, str):
            continue
        if cur and cur[0] == "let" and len(cur) >= 3 and isinstance(cur[1], list):
            for binding in cur[1]:
                if isinstance(binding, list) and len(binding) == 2:
                    env[binding[0]] = binding[1]
            stack.extend(cur[2:])
            stack.extend(cur[1])
            continue
        stack.extend(x for x in cur if isinstance(x, list))


def expand(node, env: dict, depth: int = 0, limit: int = 200):
    """Substitutes `let` names to a bounded fixpoint. `limit` guards a
    truncated/adversarial proof; z3's own output is acyclic and never needs
    it in practice."""
    if depth > limit:
        return node
    if isinstance(node, str):
        if node in env:
            return expand(env[node], env, depth + 1, limit)
        return node
    return [expand(x, env, depth + 1, limit) for x in node]


def find_quant_inst_raw(node) -> list:
    """Every `(_ quant-inst t1 .. tn)` NODE, in document order -- the same
    shape `proof-instances.py.find_quant_inst` finds, kept identical on
    purpose so the two tools' raw counts are comparable (the positive
    control)."""
    found: list = []
    stack = [node]
    while stack:
        cur = stack.pop()
        if isinstance(cur, str):
            continue
        if len(cur) >= 2 and cur[0] == "_" and cur[1] == "quant-inst":
            found.append(cur)
        stack.extend(x for x in cur if isinstance(x, list))
    return found


def find_quant_inst_applications(node) -> list:
    """Every 2-element application `((_ quant-inst t1 .. tn) F)`, i.e. the
    quant-inst NODE together with its single argument `F` -- `quant-inst` is
    a leaf proof rule (no premises; `F` IS the conclusion, exactly like
    `(asserted F)`), so `F` is what this tool needs. Returns
    `(params, formula_node)` pairs in document order."""
    out: list = []
    stack = [node]
    while stack:
        cur = stack.pop()
        if isinstance(cur, str):
            continue
        if (
            len(cur) == 2
            and isinstance(cur[0], list)
            and len(cur[0]) >= 2
            and cur[0][0] == "_"
            and cur[0][1] == "quant-inst"
        ):
            out.append((cur[0][2:], cur[1]))
        stack.extend(x for x in cur if isinstance(x, list))
    return out


def is_not(node) -> bool:
    return isinstance(node, list) and len(node) == 2 and node[0] == "not"


def instance_body(expanded_conclusion) -> Optional[list]:
    """`expanded_conclusion` is `(or (not <quantified-formula>) <body[t]>)`.
    Returns `<body[t]>` -- the one disjunct that is not the negated
    quantifier -- or `None` if the shape does not match (reported, never
    silently skipped by the caller)."""
    if not (isinstance(expanded_conclusion, list) and expanded_conclusion):
        return None
    if expanded_conclusion[0] != "or":
        return None
    disjuncts = expanded_conclusion[1:]
    kept = [d for d in disjuncts if not is_not(d)]
    dropped = [d for d in disjuncts if is_not(d)]
    if len(dropped) != 1 or len(kept) != 1:
        return None
    return kept[0]


def applications(node, out: set) -> None:
    INTERPRETED = {
        "+", "-", "*", "div", "mod", "abs", "<=", "<", ">=", ">", "=", "distinct",
        "and", "or", "not", "=>", "xor", "ite", "let", "true", "false",
        "select", "store", "forall", "exists", "!", "_",
    }
    stack = [node]
    while stack:
        cur = stack.pop()
        if isinstance(cur, str):
            continue
        if cur and isinstance(cur[0], str) and cur[0] not in INTERPRETED:
            out.add(render(cur))
        stack.extend(x for x in cur if isinstance(x, list))


def extract(text: str) -> dict:
    """Returns a dict: `raw_count` (occurrences of the `(_ quant-inst ..)`
    node shape, comparable to `proof-instances.py`), `bodies` (ordered,
    DEDUPED, rendered `body[t]` strings this tool could recover), and
    `unmatched` (count of quant-inst applications whose conclusion was not
    the expected `(or (not F) body)` shape -- reported, not hidden)."""
    start = text.find("(proof")
    if start < 0:
        start = text.find("(let ")
    if start < 0:
        return {"raw_count": 0, "bodies": [], "unmatched": 0, "error": "NO-PROOF"}

    tokens = tokenize(text[start:])
    tree = parse(tokens)
    env: dict = {}
    collect_lets(tree, env)

    raw_count = len(find_quant_inst_raw(tree))
    apps = find_quant_inst_applications(tree)

    bodies: list = []
    seen: set = set()
    unmatched = 0
    for _params, formula in apps:
        conclusion = expand(formula, env)
        body = instance_body(conclusion)
        if body is None:
            unmatched += 1
            continue
        rendered = render(body)
        if rendered not in seen:
            seen.add(rendered)
            bodies.append(rendered)

    return {"raw_count": raw_count, "bodies": bodies, "unmatched": unmatched}


def main(argv: list) -> int:
    args = [a for a in argv[1:] if not a.startswith("--")]
    flags = {a for a in argv[1:] if a.startswith("--")}
    if not args:
        sys.stderr.write(__doc__ or "")
        return 2

    try:
        with open(args[0], encoding="utf-8", errors="replace") as fh:
            text = fh.read()
    except OSError as exc:
        sys.stderr.write(f"z3-proof-instances: cannot read {args[0]}: {exc}\n")
        return 2

    try:
        result = extract(text)
    except ValueError as exc:
        sys.stderr.write(f"PARSE-FAIL {args[0]}: {exc}\n")
        return 3

    if result.get("error") == "NO-PROOF":
        sys.stderr.write(f"NO-PROOF {args[0]}: no `(proof ...)` form found\n")
        return 1

    if "--count" in flags:
        print(result["raw_count"])
        return 0

    if "--applications" in flags:
        apps: set = set()
        for b in result["bodies"]:
            apps.add(b)
        # Re-walk each body for the uninterpreted applications inside it.
        seen_apps: set = set()
        for b_str in result["bodies"]:
            node = parse(tokenize(b_str))
            applications(node, seen_apps)
        for a in sorted(seen_apps):
            print(a)
        return 0

    if "--json" in flags:
        json.dump(result, sys.stdout, indent=1)
        print()
        return 0

    for b in result["bodies"]:
        print(f"(assert {b})")
    if result["unmatched"]:
        sys.stderr.write(
            f"UNMATCHED {result['unmatched']} of "
            f"{result['unmatched'] + len(result['bodies'])} quant-inst "
            "applications did not have the expected (or (not F) body) shape\n"
        )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))

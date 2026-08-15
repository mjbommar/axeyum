#!/usr/bin/env python3
"""Does a geometry fact's SMT-LIB `formal.statement` say what its certificate proves?

WHY THIS EXISTS. A `cas-certificate` geometry fact carries two independent
statements of the same theorem: the polynomials in
`artifacts/geometry-certificates/<id>.json`, which is what the checker
re-derives, and the SMT-LIB `formal.statement` in `artifacts/facts/`, which is
what every downstream consumer reads. Nothing connected them. The fact is
`proved` because the certificate re-derives; the certificate knows nothing about
the transcription, and prose review does not catch a transposed sign or a
swapped vertex.

Three lanes in a row noticed this and each cross-evaluated by hand, at 400
random rational configurations, and each recorded the count in a diary
(`F:geometry-euler-line`: 2400 comparisons; `F:geometry-pappus-hexagon`: 4000).
Hand-work that three lanes repeat is a gate, so this is that gate: the same
measurement, committed, re-runnable, and cheap enough to be a `checker_command`.

WHAT IT CHECKS. For each fact naming a geometry certificate, the SMT-LIB
antecedent is split into its conjuncts and matched positionally against the
certificate's `hypotheses` then its `saturations`, and the consequent against the
`conclusions`. At each of `--samples` random rational configurations both sides
are evaluated exactly (`fractions.Fraction`), and each pair must keep a
**constant nonzero ratio** across every sample.

Proportionality rather than equality is the right test and not a weakening: a
polynomial and a nonzero rational multiple of it have the same zero set, state
the same hypothesis, and generate the same ideal, and the row-reduction sign in a
concyclicity determinant is exactly such a multiple. Two polynomials whose ratio
is constant on a random sample of a Zariski-dense set are proportional; the ratio
is reported per conjunct so a reader can see which are literal (`x1`) and which
carry a sign.

WHAT IT DOES NOT CHECK. That either statement is the intended geometry. Nothing
inside a polynomial identity can tell you that `equidistant` means equidistant --
that is the coordinatisation control's job, and the certificates carry their own
rational witnesses for it. This checks only that the two statements of the
theorem agree with each other, which is the failure a fact ledger exists to
prevent.

Usage:
    python3 scripts/check-geometry-fact-transcription.py [F:id ...]
    python3 scripts/check-geometry-fact-transcription.py --samples 400 --seed 7
"""

from __future__ import annotations

import argparse
import json
import random
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FACTS = ROOT / "artifacts" / "facts"

# --------------------------------------------------------------------------
# A very small S-expression reader and evaluator, scoped to what these
# statements use. Anything outside that vocabulary is an error rather than a
# default, because a silently-ignored operator would make this gate agree with
# a statement it never read.
# --------------------------------------------------------------------------


def tokenize(text: str) -> list[str]:
    return text.replace("(", " ( ").replace(")", " ) ").split()


def parse(tokens: list[str], position: int = 0):
    """Return `(node, next_position)`; a node is a `str` or a `list`."""
    if position >= len(tokens):
        raise ValueError("unexpected end of s-expression")
    token = tokens[position]
    if token == "(":
        items = []
        position += 1
        while tokens[position] != ")":
            item, position = parse(tokens, position)
            items.append(item)
        return items, position + 1
    if token == ")":
        raise ValueError("unbalanced ')'")
    return token, position + 1


ARITHMETIC = {"+", "-", "*", "/"}


def evaluate(node, assignment: dict[str, Fraction]) -> Fraction:
    """Evaluate an arithmetic term exactly."""
    if isinstance(node, str):
        if node in assignment:
            return assignment[node]
        try:
            return Fraction(node)
        except ValueError as error:
            raise ValueError(f"unbound symbol `{node}`") from error
    if not node:
        raise ValueError("empty application")
    head = node[0]
    if head not in ARITHMETIC:
        raise ValueError(f"unsupported operator `{head}` in an arithmetic term")
    args = [evaluate(child, assignment) for child in node[1:]]
    if not args:
        raise ValueError(f"`{head}` applied to nothing")
    if head == "-" and len(args) == 1:
        return -args[0]
    total = args[0]
    for value in args[1:]:
        if head == "+":
            total += value
        elif head == "-":
            total -= value
        elif head == "*":
            total *= value
        else:
            if value == 0:
                raise ValueError("division by zero while evaluating a transcription")
            total /= value
    return total


def expand_lets(node, environment: dict):
    """Inline every `let` binding, so the rest of this file sees pure terms.

    Substitution is exact here because the bindings are arithmetic terms over the
    quantified coordinates -- `F:geometry-centroid-divides-medians` names its two
    midpoints this way, and a reader is better served by the abbreviation than by
    a checker that refuses it.
    """
    if isinstance(node, str):
        return environment.get(node, node)
    if node and node[0] == "let":
        extended = dict(environment)
        for name, definition in node[1]:
            extended[name] = expand_lets(definition, extended)
        return expand_lets(node[2], extended)
    return [expand_lets(child, environment) for child in node]


def atom_term(node):
    """`(left - right, polarity)` for an equality atom, possibly negated.

    The difference rather than one side: these statements write both
    `(= e 0.0)` and `(= (* 3.0 px) (+ ax bx cx))`, and only the difference is
    comparable with a certificate polynomial.
    """
    if isinstance(node, list) and node and node[0] == "not":
        if len(node) != 2:
            raise ValueError("`not` takes one argument")
        term, polarity = atom_term(node[1])
        if not polarity:
            raise ValueError("double negation is not expected here")
        return term, False
    if not (isinstance(node, list) and len(node) == 3 and node[0] == "="):
        raise ValueError(f"expected an equality atom, got {node!r}")
    return ["-", node[1], node[2]], True


def statement_parts(text: str):
    """`(hypothesis terms, condition terms, conclusion terms, variables)`."""
    tree, end = parse(tokenize(text))
    if end != len(tokenize(text)):
        raise ValueError("trailing tokens after the assertion")
    if not (isinstance(tree, list) and tree[0] == "assert"):
        raise ValueError("the statement must be a single `assert`")
    body = tree[1]
    if not (isinstance(body, list) and body[0] == "forall"):
        raise ValueError("the assertion must be a `forall`")
    variables = [binding[0] for binding in body[1]]
    implication = expand_lets(body[2], {})
    hypotheses, conditions = [], []
    if isinstance(implication, list) and implication[0] == "=>":
        antecedent, consequent = implication[1], implication[2]
        conjuncts = antecedent[1:] if antecedent[0] == "and" else [antecedent]
        for conjunct in conjuncts:
            term, positive = atom_term(conjunct)
            (hypotheses if positive else conditions).append(term)
    else:
        # An unconditional theorem -- four of the corpus's nine are outright
        # polynomial identities, with no hypothesis and no side condition, and
        # this is what that looks like rather than a parse failure.
        consequent = implication
    consequents = consequent[1:] if (
        isinstance(consequent, list) and consequent[0] == "and"
    ) else [consequent]
    conclusions = []
    for item in consequents:
        term, positive = atom_term(item)
        if not positive:
            raise ValueError("a negated conclusion is not expected here")
        conclusions.append(term)
    return hypotheses, conditions, conclusions, variables


# --------------------------------------------------------------------------
# The certificate side: the committed polynomials, evaluated directly.
# --------------------------------------------------------------------------


def evaluate_poly(poly: dict, assignment: dict[str, Fraction]) -> Fraction:
    total = Fraction(0)
    for term in poly["terms"]:
        numerator, denominator = term["coefficient"]
        value = Fraction(numerator, denominator)
        for name, power in term["monomial"]:
            value *= assignment[name] ** power
        total += value
    return total


def compare(fact_path: Path, samples: int, rng: random.Random, half_range: int) -> bool:
    fact = json.loads(fact_path.read_text())
    if fact.get("proof_route") != "cas-certificate":
        return True
    artifacts = {
        row["artifact"]
        for row in fact.get("evidence", [])
        if str(row.get("artifact", "")).startswith("artifacts/geometry-certificates/")
    }
    if not artifacts:
        return True
    if len(artifacts) > 1:
        print(f"  {fact['id']}: cites {len(artifacts)} certificates; expected one")
        return False
    certificate = json.loads((ROOT / artifacts.pop()).read_text())

    hypotheses, conditions, conclusions, variables = statement_parts(
        fact["formal"]["statement"]
    )
    pairs: list[tuple[str, object, dict]] = []
    expected = [
        ("hypothesis", hypotheses, [row["poly"] for row in certificate["hypotheses"]]),
        (
            "condition",
            conditions,
            [row["condition"] for row in certificate["saturations"]],
        ),
        ("conclusion", conclusions, [row["poly"] for row in certificate["conclusions"]]),
    ]
    for kind, transcribed, committed in expected:
        if len(transcribed) != len(committed):
            print(
                f"  {fact['id']}: the statement has {len(transcribed)} {kind} atoms, "
                f"the certificate has {len(committed)}"
            )
            return False
        for index, (left, right) in enumerate(zip(transcribed, committed)):
            pairs.append((f"{kind}[{index}]", left, right))

    # The certificate's `coordinates` are derived from its GENERATORS, so an
    # unconditional theorem (Varignon: no hypothesis, no condition, hence no
    # generator) declares none at all. What must hold is that every variable
    # either statement actually mentions is quantified over -- an unquantified
    # coordinate in the fact would be a free variable in a `forall` statement,
    # which is the real defect this guards.
    free = set(variables)
    mentioned = set(certificate["coordinates"])
    for _, _, committed in pairs:
        for term in committed["terms"]:
            mentioned.update(name for name, _ in term["monomial"])
    if not mentioned <= free:
        print(
            f"  {fact['id']}: the certificate mentions {sorted(mentioned - free)}, "
            f"which the statement does not quantify over"
        )
        return False

    ratios: dict[str, Fraction | None] = {}
    comparisons = 0
    for _ in range(samples):
        assignment = {
            name: Fraction(
                rng.randint(-half_range, half_range), rng.randint(1, half_range)
            )
            for name in sorted(free)
        }
        for label, transcribed, committed in pairs:
            try:
                left = evaluate(transcribed, assignment)
            except ValueError as error:
                print(f"  {fact['id']}: {label}: {error}")
                return False
            right = evaluate_poly(committed, assignment)
            comparisons += 1
            if right == 0 or left == 0:
                if left != 0 or right != 0:
                    print(
                        f"  {fact['id']}: {label} disagrees on vanishing at {assignment}"
                    )
                    return False
                continue
            ratio = left / right
            if label not in ratios:
                ratios[label] = ratio
            elif ratios[label] != ratio:
                print(
                    f"  {fact['id']}: {label} is not a constant multiple "
                    f"({ratios[label]} then {ratio})"
                )
                return False

    scaled = {
        label: str(ratio) for label, ratio in ratios.items() if ratio not in (Fraction(1),)
    }
    detail = f"  scaled: {scaled}" if scaled else ""
    print(
        f"  ok  {fact['id']:<40} {len(pairs)} atoms x {samples} samples = "
        f"{comparisons} comparisons, 0 mismatches{detail}"
    )
    return True


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("facts", nargs="*", help="fact ids; default is every geometry fact")
    parser.add_argument("--samples", type=int, default=400)
    parser.add_argument("--seed", type=int, default=20260815)
    parser.add_argument("--half-range", type=int, default=9)
    args = parser.parse_args()

    if args.facts:
        paths = [FACTS / (fact.replace("F:", "F-") + ".json") for fact in args.facts]
    else:
        paths = sorted(FACTS.glob("F-geometry-*.json"))
    missing = [path for path in paths if not path.exists()]
    if missing:
        for path in missing:
            print(f"  no such fact: {path.name}")
        return 1
    if not paths:
        print("no geometry facts found; this gate examined nothing")
        return 1

    rng = random.Random(args.seed)
    print(f"geometry fact transcription: {len(paths)} facts, seed {args.seed}")
    failures = sum(0 if compare(path, args.samples, rng, args.half_range) else 1 for path in paths)
    if failures:
        print(f"\n{failures} fact(s) whose SMT-LIB statement disagrees with its certificate")
        return 1
    print(f"\nall {len(paths)} geometry facts transcribe faithfully")
    return 0


if __name__ == "__main__":
    sys.exit(main())

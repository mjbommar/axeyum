"""Derive, from a geometry certificate, HOW MUCH a kernel reconstruction of it
actually establishes.

The problem this module exists for
----------------------------------
`scripts/validate-facts.py`'s `classify_cas_certificate_checker` decides that a
`cas-certificate` fact is `kernel-reconstructed` by looking at whether an
executed `cargo test`/`cargo run` segment NAMES the `axeyum-lean-kernel`
package.  That is the right question about *which trust anchor ran* and it is
no question at all about *what the anchor was asked to check*.  A reconstruction
whose kernel obligation is ``poly_expr(X) = 1 * poly_expr(X)`` names the kernel
package, runs a real `add_declaration`, is admitted axiom-free -- and
establishes a `mul_one`-shaped ring fact true of every polynomial.  It moves the
headline counter by exactly as much as a reconstruction with real content.

So this module answers the second question, from the CERTIFICATE rather than
from the fact's own prose, and it is deliberately not a boolean.  ADR-0601 SS2's
split is `kernel-reconstructed` versus `cas-internal`; the finding here is that
`kernel-reconstructed` is itself two things, and a fact of the weaker kind is
honest -- Thales is real work -- but must not read identically to the stronger.

The ladder
----------
Per conclusion of a certificate, the kernel obligation is

    conclusion_poly  =  sum_i  cofactor_i * generator_i

and what it establishes is decided by how many generators actually appear:

``empty``
    No coordinates, no generators, and an empty conclusion polynomial.  The CAS
    cancelled everything before the certificate existed, so the only
    reconstructible statement is ``0 = 0`` over zero variables
    (`varignon-midpoint-parallelogram`).  Nothing to reconstruct.

``refl``
    Exactly one generator carries a nonzero cofactor, that cofactor is the
    constant 1, and the generator polynomial is IDENTICAL to the conclusion
    polynomial.  The obligation is ``X = 1 * X`` for one particular X: true of
    every polynomial, so it does not discriminate this theorem from any other
    (`thales-right-angle-in-semicircle`).

``scale``
    Exactly one generator carries a nonzero cofactor, but the product is not the
    identity above -- a non-constant cofactor has to be distributed through the
    generator and the monomials collected.  Real ring work, but still a law about
    ONE polynomial and a multiplier; no two independently-derived geometric
    predicates are tied together.

``combination``
    Two or more generators carry nonzero cofactors.  Monomials contributed by
    DISTINCT generators must cancel against each other for the identity to hold,
    which is what makes it specific to the configuration
    (`orthocentre-altitudes-concurrent`: 16 monomials in, 8 out).

Only ``combination`` clears the substance bar.  ``refl`` and ``scale`` are
disclosable, not forbidden -- see `scripts/check-cas-substance.py`.

Why the derivation reads the certificate and not the fact
---------------------------------------------------------
A fact's `formal.statement` is prose-adjacent: across the 14 facts measured on
2026-08-30, some spell the polynomials out in full and others carry placeholder
names (`generator_P_on_median_from_A`, `c0x`, `g0`) that no parser can expand.
A gate keyed on that text would be defeated by writing a placeholder, and a gate
a lane can defeat by rewording is the checker-that-cannot-fail defect wearing a
different hat.  The certificate is the artifact the CAS actually emitted.
"""

from __future__ import annotations

from typing import Any

# A polynomial is {"terms": [{"monomial": [[var, exp], ...],
#                             "coefficient": [num, den]}, ...]}.

#: The shapes a certificate derivation can produce, ordered WEAKEST FIRST --
#: `analyse_certificate` takes the minimum over a certificate's conclusions.
CERTIFICATE_SHAPES = ("empty", "refl", "scale", "combination")

#: Two further shapes that a certificate derivation never produces, because the
#: reconstructions carrying them are not cofactor identities at all.  They are
#: DECLARED by the fact and this module cannot derive them; the gate says so in
#: its own output rather than letting them read as measured.
#:
#: ``identity``
#:     A symbolic ring identity at one or more free variables, not in
#:     conclusion = sum(cofactor * generator) form -- e.g. the partial-fractions
#:     coefficient-matching identity, or (x+1)(x-1) = x^2-1 at free x.
#: ``evaluation``
#:     A closed obligation at concrete rationals, no free variable -- e.g. an
#:     IVT sign bracket, p(1) < 0 and p(2) > 0.  Specific to the polynomial, and
#:     silent about every other point.
DECLARED_ONLY_SHAPES = ("identity", "evaluation")

SHAPES = CERTIFICATE_SHAPES + DECLARED_ONLY_SHAPES

#: The shapes whose kernel obligation is true of EVERY polynomial in place of
#: the certificate's, and so establishes nothing specific to the theorem.
NON_DISCRIMINATING_SHAPES = ("empty", "refl")


def poly_terms(poly: Any) -> list[dict]:
    """The term list of a polynomial, tolerating `None` and a missing key."""
    if not isinstance(poly, dict):
        return []
    terms = poly.get("terms")
    return terms if isinstance(terms, list) else []


def is_zero_poly(poly: Any) -> bool:
    """True when the polynomial has no terms at all.

    A cofactor that is the zero polynomial contributes nothing to the
    combination, so it must not be counted as an active generator -- otherwise
    padding a certificate with zero cofactors would promote a `refl` obligation
    to `combination` without changing what the kernel checks.
    """
    return not poly_terms(poly)


def is_constant_one_poly(poly: Any) -> bool:
    """True for the polynomial 1: a single term, empty monomial, coefficient 1/1."""
    terms = poly_terms(poly)
    if len(terms) != 1:
        return False
    term = terms[0]
    if not isinstance(term, dict):
        return False
    if term.get("monomial"):
        return False
    coefficient = term.get("coefficient")
    if not isinstance(coefficient, list) or len(coefficient) != 2:
        return False
    num, den = coefficient
    return den != 0 and num == den


def analyse_conclusion(certificate: dict, conclusion: dict) -> dict:
    """Derive the substance record for ONE conclusion of a certificate."""
    generators = certificate.get("generators") or []
    cofactors = conclusion.get("cofactors") or []
    concl_poly = conclusion.get("poly")

    active: list[int] = [
        i for i, cofactor in enumerate(cofactors) if not is_zero_poly(cofactor)
    ]

    # Monomials the combination starts from, before any cancellation: each
    # active generator contributes (its term count) x (its cofactor's term
    # count) products.  This is an upper bound on the expanded left-hand side
    # and is what makes cancellation visible as a number.
    input_monomials = sum(
        len(poly_terms(generators[i])) * len(poly_terms(cofactors[i]))
        for i in active
        if i < len(generators)
    )
    output_monomials = len(poly_terms(concl_poly))

    if (
        not (certificate.get("coordinates") or [])
        and not generators
        and not poly_terms(concl_poly)
    ):
        shape = "empty"
    elif len(active) >= 2:
        shape = "combination"
    elif len(active) == 1:
        i = active[0]
        generator = generators[i] if i < len(generators) else None
        if is_constant_one_poly(cofactors[i]) and generator == concl_poly:
            shape = "refl"
        else:
            shape = "scale"
    else:
        # No active generator at all, yet a non-empty conclusion: the identity
        # asserts the conclusion polynomial is zero on the nose.  Not `empty`
        # (there is something to translate) and not a combination of anything.
        shape = "scale" if poly_terms(concl_poly) else "empty"

    return {
        "conclusion_id": conclusion.get("id"),
        "shape": shape,
        "active_generators": len(active),
        "declared_generators": len(generators),
        "coordinates": len(certificate.get("coordinates") or []),
        "input_monomials": input_monomials,
        "output_monomials": output_monomials,
        "cancelled_monomials": max(0, input_monomials - output_monomials),
        "discriminating": shape not in NON_DISCRIMINATING_SHAPES,
    }


def analyse_certificate(certificate: dict) -> dict:
    """Derive the substance record for a whole certificate.

    The certificate's shape is the WEAKEST of its conclusions': a certificate
    whose reconstruction covers one real combination and one `x = x` is only as
    strong as what a reader is told, and a reader told "combination" would
    over-read the second.  Weakest-wins keeps the aggregate honest in the same
    direction the classification rule it sits under does (`classify_cas_
    certificate_fact` lets the STRONGER win across evidence rows, because there
    the question is whether an independent re-derivation EXISTS at all).
    """
    conclusions = certificate.get("conclusions") or []
    per_conclusion = [analyse_certificate_conclusion(certificate, c) for c in conclusions]
    if not per_conclusion:
        weakest = "empty"
    else:
        weakest = min(
            per_conclusion, key=lambda r: CERTIFICATE_SHAPES.index(r["shape"])
        )["shape"]
    return {
        "certificate_id": certificate.get("id"),
        "shape": weakest,
        "discriminating": weakest not in NON_DISCRIMINATING_SHAPES,
        "coordinates": len(certificate.get("coordinates") or []),
        "declared_generators": len(certificate.get("generators") or []),
        "conclusions": per_conclusion,
    }


# Kept as a separate name so `analyse_conclusion` reads well at a call site that
# has only one conclusion in hand.
analyse_certificate_conclusion = analyse_conclusion


# ---------------------------------------------------------------------------
# A second, INDEPENDENT refl detector, over the fact's own `formal.statement`.
#
# The certificate derivation above is authoritative but only exists for facts
# that name a certificate artifact; 8 of the 14 kernel-reconstructed facts
# measured on 2026-08-30 have none (their reconstructions are sign brackets and
# coefficient-matching identities, produced inside a Rust test rather than
# emitted as a JSON certificate).  For those the declared shape would otherwise
# be pure self-report.
#
# This detector gives that group one genuine failure mode: parse the statement
# as s-expressions, erase multiplication by the literal 1, and ask whether any
# equation's two sides are then structurally identical.  Run over the 14 it
# returns True for `F:geometry-thales-cofactor-identity-kernel-checked` and for
# nothing else -- which is the discrimination it has to show to be worth having.
#
# It is deliberately NOT the primary signal: a statement carrying placeholder
# names (`generator_P_on_median_from_A`, `c0x`, `g0` -- three of the 14 do)
# cannot be expanded by any parser, so a gate keyed on this alone would be
# defeated by rewording.  Unparseable input yields None, meaning "no signal",
# never "clean".
# ---------------------------------------------------------------------------

import re as _re

_SEXPR_TOKEN_RE = _re.compile(r"\(|\)|[^\s()]+")
_SEXPR_COMMENT_RE = _re.compile(r";[^\n]*")


def parse_sexprs(text: str) -> list | None:
    """Parse `text` as a sequence of s-expressions, or None if unbalanced."""
    tokens = _SEXPR_TOKEN_RE.findall(_SEXPR_COMMENT_RE.sub("", text or ""))
    top: list = []
    stack: list[list] = [top]
    for token in tokens:
        if token == "(":
            node: list = []
            stack[-1].append(node)
            stack.append(node)
        elif token == ")":
            if len(stack) == 1:
                return None
            stack.pop()
        else:
            stack[-1].append(token)
    return top if len(stack) == 1 else None


def _erase_multiplication_by_one(expr):
    """Rewrite ``(* 1 X)`` and ``(* X 1)`` to ``X``, recursively."""
    if not isinstance(expr, list):
        return expr
    rewritten = [_erase_multiplication_by_one(sub) for sub in expr]
    if len(rewritten) == 3 and rewritten[0] == "*":
        if rewritten[1] == "1":
            return rewritten[2]
        if rewritten[2] == "1":
            return rewritten[1]
    return rewritten


def _collect_equations(expr, out: list) -> None:
    if isinstance(expr, list):
        if len(expr) == 3 and expr[0] == "=":
            out.append(expr)
        for sub in expr:
            _collect_equations(sub, out)


def statement_is_refl_shaped(statement: str) -> bool | None:
    """True when some equation in `statement` is ``X = X`` after erasing ``*1``.

    Returns None when the statement does not parse or contains no equation at
    all -- "no signal", which callers must not read as "not refl".
    """
    parsed = parse_sexprs(statement)
    if parsed is None:
        return None
    equations: list = []
    _collect_equations(parsed, equations)
    if not equations:
        return None
    return any(
        _erase_multiplication_by_one(lhs) == _erase_multiplication_by_one(rhs)
        for _, lhs, rhs in equations
    )

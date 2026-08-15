#!/usr/bin/env python3
"""Generate the tampered SOS certificate fixtures.

WHY THIS EXISTS. A checker is only worth what it *rejects*. The 2026-08-15
ledger audit found 40 of 162 checker runs in `artifacts/facts/` exiting zero on
completion alone -- `nat_theorem_inventory -- this_theorem_does_not_exist`
prints "0 theorems" and exits 0, and that was the shape of a real fact's
checker. So every certificate family in this repository now ships false
certificates alongside the true ones, and a gate that runs the checker over them
and requires a NON-ZERO exit.

The fixtures are committed, so a reader can diff a tampered file against the
honest one and see exactly which byte was changed. This script is the record of
how each was produced, and re-running it must reproduce them byte for byte:

    python3 scripts/gen-sos-negative-controls.py --check

Every tamper is a single, surgical substitution against the emitted artifact,
and the script REFUSES to write a fixture whose substitution did not apply --
otherwise a rename upstream would silently turn a tamper into a copy of the
honest file, which the gate would then happily "reject" for no reason, or worse,
accept.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
SOURCE = ROOT / "artifacts" / "sos-certificates"
TARGET = ROOT / "artifacts" / "instances" / "sos" / "negative-controls"

# (fixture name, source artifact, [(needle, replacement), ...], why it must be rejected)
TAMPERS: list[tuple[str, str, list[tuple[str, str]], str]] = [
    (
        "lyapunov-tampered-square",
        "damped-rotation-lyapunov",
        [('[["x", 1], ["y", 1]], "coefficient": [5, 1]}', '[["x", 1], ["y", 1]], "coefficient": [6, 1]}')],
        "one coefficient inside a square of the decrease certificate moved by one",
    ),
    (
        "lyapunov-tampered-field",
        "damped-rotation-lyapunov",
        [('[["y", 1]], "coefficient": [10, 1]}]}, {"terms"', '[["y", 1]], "coefficient": [11, 1]}]}, {"terms"')],
        "the vector field itself edited: the checker re-derives V-dot from the field, so this "
        "breaks the decrease identity even though no field in the file names a derivative",
    ),
    (
        "lyapunov-zero-decay",
        "damped-rotation-lyapunov",
        [('"decay": [2, 1]', '"decay": [0, 1]')],
        "a zero decay constant certifies non-increase, not decrease",
    ),
    (
        "lyapunov-negative-decay",
        "damped-rotation-lyapunov",
        [('"decay": [2, 1]', '"decay": [-2, 1]')],
        "a negative decay constant is an anti-Lyapunov claim",
    ),
    (
        "lyapunov-inflated-decay",
        "damped-rotation-lyapunov",
        [('"decay": [2, 1]', '"decay": [3, 1]')],
        "a faster rate claimed than the squares pay for",
    ),
    (
        "lyapunov-loose-upper",
        "damped-rotation-lyapunov",
        [('"upper": [52, 1]', '"upper": [51, 1]')],
        "the upper sandwich constant lowered below what the squares certify, which would inflate "
        "the reported decay rate",
    ),
    (
        "lyapunov-negative-weight",
        "damped-rotation-lyapunov",
        [('{"weight": [52, 1], "square": {"terms": [{"monomial": [["x", 1], ["y", 1]], "coefficient": [1, 1]}]}}', '{"weight": [-52, 1], "square": {"terms": [{"monomial": [["x", 1], ["y", 1]], "coefficient": [1, 1]}]}}')],
        "a negative weight makes a `sum of squares` certify nothing",
    ),
    (
        "lyapunov-naive-witness-moved",
        "damped-rotation-lyapunov",
        [('"naive_failure": [["x", [1, 1]], ["y", [1, 1]]]', '"naive_failure": [["x", [0, 1]], ["y", [1, 1]]]')],
        "the point where the naive candidate |x|^2 fails moved to one where it does not, so the "
        "artifact would no longer show that the search did any work",
    ),
    (
        "barrier-tampered-field",
        "energy-barrier-reachability",
        [('{"monomial": [["y", 3]], "coefficient": [-1, 1]}', '{"monomial": [["y", 3]], "coefficient": [1, 1]}')],
        "the damping sign flipped: B-dot is re-derived here, so -B-dot is no longer a square",
    ),
    (
        "barrier-tampered-barrier",
        "energy-barrier-reachability",
        [('"barrier": {"terms": [{"monomial": [], "coefficient": [-6, 1]}', '"barrier": {"terms": [{"monomial": [], "coefficient": [-3, 1]}')],
        "the barrier level moved, so it no longer separates the two discs",
    ),
    (
        "barrier-initial-witness-outside",
        "energy-barrier-reachability",
        [('"initial_witness": [["x", [0, 1]], ["y", [2, 1]]]', '"initial_witness": [["x", [5, 1]], ["y", [0, 1]]]')],
        "the committed point is no longer in the initial set, so the set is not shown nonempty "
        "and an empty initial set satisfies every barrier certificate ever written",
    ),
    (
        "barrier-unsafe-witness-outside",
        "energy-barrier-reachability",
        [('"unsafe_witness": [["x", [5, 1]], ["y", [0, 1]]]', '"unsafe_witness": [["x", [0, 1]], ["y", [0, 1]]]')],
        "the same failure on the unsafe side: an empty unsafe set is trivially unreachable",
    ),
    (
        "barrier-zero-margin",
        "energy-barrier-reachability",
        [('"initial_margin": [1, 1]', '"initial_margin": [0, 1]')],
        "a zero margin leaves the two sets touching at B = 0",
    ),
    (
        "barrier-dropped-multiplier",
        "energy-barrier-reachability",
        [('"initial_multipliers": [{"squares": [{"weight": [1, 1], "square": {"terms": [{"monomial": [], "coefficient": [1, 1]}]}}]}]', '"initial_multipliers": []')],
        "a Positivstellensatz multiplier dropped, so the certificate no longer covers its generator",
    ),
    (
        "motzkin-dual-not-psd",
        "motzkin-psd-not-sos",
        [('[[["z", 6]], [8, 1]]', '[[["z", 6]], [1, 1]]')],
        "one dual value lowered until the moment matrix stops being positive semidefinite, so the "
        "functional is no longer nonnegative on squares",
    ),
    (
        "motzkin-dual-nonneg-on-form",
        "motzkin-psd-not-sos",
        [('[[["z", 6]], [8, 1]]', '[[["z", 6]], [100, 1]]')],
        "the sharpest control here: the same value RAISED keeps the moment matrix PSD and makes "
        "the functional POSITIVE on the form, so the PSD obligation passes and the sign obligation "
        "must fail -- a checker that only ran the matrix test would accept this",
    ),
    (
        "motzkin-tampered-multiplier",
        "motzkin-psd-not-sos",
        [('"multiplier": {"terms": [{"monomial": [["x", 2]], "coefficient": [1, 1]}, {"monomial": [["y", 2]], "coefficient": [1, 1]}, {"monomial": [["z", 2]], "coefficient": [1, 1]}]}', '"multiplier": {"terms": [{"monomial": [["x", 2]], "coefficient": [1, 1]}, {"monomial": [["y", 2]], "coefficient": [1, 1]}]}')],
        "a multiplier that vanishes on a whole line, which would certify nonnegativity nowhere on it",
    ),
    (
        "motzkin-tampered-square",
        "motzkin-psd-not-sos",
        [('{"weight": [3, 4]', '{"weight": [1, 2]')],
        "one weight in the SOS decomposition of |x|^2 * form changed",
    ),
    (
        "motzkin-dual-off-degree",
        "motzkin-psd-not-sos",
        [('[[["z", 6]], [8, 1]]', '[[["z", 6]], [8, 1]], [[["x", 2], ["y", 2]], [-1000, 1]]')],
        "a dual value planted at a monomial of the wrong degree, which no moment-matrix entry "
        "reads and which would therefore be a free parameter",
    ),
]

# Fixtures that are not tampered artifacts but malformed documents.
LITERALS: list[tuple[str, str, str]] = [
    (
        "not-a-certificate",
        "{}\n",
        "an empty object: no format tag, no kind, nothing to check",
    ),
    (
        "float-coefficient",
        None,
        "an exact rational replaced by a decimal literal; this format admits no floats",
    ),
]


def build() -> dict[str, str]:
    out: dict[str, str] = {}
    for name, source, substitutions, _why in TAMPERS:
        path = SOURCE / f"{source}.json"
        text = path.read_text(encoding="utf-8")
        for needle, replacement in substitutions:
            if needle not in text:
                raise SystemExit(
                    f"{name}: the substitution target is not present in {path.name}.\n"
                    f"  looking for: {needle}\n"
                    "A tamper whose edit did not apply is a COPY of the honest artifact, which "
                    "the gate would then reject for no reason or accept outright. Refusing."
                )
            if text.count(needle) != 1:
                raise SystemExit(
                    f"{name}: the substitution target occurs {text.count(needle)} times in "
                    f"{path.name}; a tamper must be surgical."
                )
            text = text.replace(needle, replacement, 1)
        out[f"{name}.json"] = text

    out["not-a-certificate.json"] = "{}\n"
    honest = (SOURCE / "damped-rotation-lyapunov.json").read_text(encoding="utf-8")
    needle = '"lower": [1, 2]'
    if needle not in honest:
        raise SystemExit("float-coefficient: the substitution target is missing")
    out["float-coefficient.json"] = honest.replace(needle, '"lower": [0.5, 1]', 1)
    return out


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="do not write; fail if any committed fixture differs",
    )
    args = parser.parse_args()

    fixtures = build()
    TARGET.mkdir(parents=True, exist_ok=True)

    # Every honest artifact must still be honest, or the tampers were built from
    # something already broken.
    for path in sorted(SOURCE.glob("*.json")):
        json.loads(path.read_text(encoding="utf-8"))

    differed = 0
    for name, text in sorted(fixtures.items()):
        path = TARGET / name
        current = path.read_text(encoding="utf-8") if path.exists() else None
        if current == text:
            continue
        differed += 1
        if args.check:
            print(f"DIFFERS  {path.relative_to(ROOT)}", file=sys.stderr)
        else:
            path.write_text(text, encoding="utf-8")
            print(f"written  {path.relative_to(ROOT)}")

    stale = {p.name for p in TARGET.glob("*.json")} - set(fixtures)
    if stale:
        print(f"STALE fixtures not produced by this script: {sorted(stale)}", file=sys.stderr)
        return 1

    if args.check and differed:
        print(f"{differed} fixture(s) differ from this generator", file=sys.stderr)
        return 1
    print(f"{len(fixtures)} negative-control fixture(s), {differed} rewritten")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""S1's exit criterion, executed rather than asserted (ADR-0747).

The trusted-library safety roadmap's S1 exit is verbatim:

    swapped binders, changed constants, altered relations, source drift, and
    replacing the upstream statement with Axeyum's own rendering all reject.

This constructs each of those five against the LIVE ledger, runs the real
gates, and restores every touched file byte-exactly. It fails if any mutation
stops being rejected -- and equally if the CLEAN tree stops passing, which is
the positive control that separates "the gates reject these five" from "the
gates reject everything".

WHY THIS IS A GATE AND NOT A NOTE
---------------------------------

An exit criterion demonstrated once in a transcript stops holding the moment
somebody edits the gate it was demonstrated against, and nothing says so. The
five mutations are cheap (~2s total, no cargo, no kernel), so there is no
reason for them to live anywhere but in the check that runs on every merge.

MUTATION 5 IS NOT INVENTED
--------------------------

It replays the two real damaged forms recovered from `e79804fdd`, where a lane
flipping two totient mirrors to `proved` overwrote `formal.statement` with our
own `render_lean` output and dropped the catalog hash pin. That is the mutation
with a live precedent -- twice on one day, and nineteen times earlier in the
mirror programme. It is also the sharpest of the five, because it does not make
the fact false: the theorems are real and axiom-free. It makes the mirror's
claim *unfalsifiable from the fact*, since with our rendering in the field that
should hold Mathlib's proposition, both sides say the same thing by
construction.

WHICH GATE CATCHES WHICH
------------------------

Deliberately recorded per mutation, because "something failed" is not evidence
that the right thing failed. A mutation rejected only by a gate that rejects
for an unrelated reason has not been shown to reject at all.

Exit 0 when all five reject and the clean tree passes, 1 otherwise, 2 on a
fixture that no longer applies (a renamed fact, a changed statement) -- which is
a real outcome worth distinguishing, since a fixture that silently stops
matching its subject is how this kind of check rots into a formality.
"""

from __future__ import annotations

import json
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
FACTS = ROOT / "artifacts/facts"

STATEMENT_GATE = ["python3", "scripts/check-settled-fact-statements.py", "--quiet"]
MIRROR_GATE = ["python3", "scripts/check-mirror-statement-fidelity.py"]

# A native, non-mirror row: the general constructive Intermediate Value Theorem,
# ADR-0603 row 1. Chosen because the mirrors' hash-pinned-catalog route does not
# apply to it, so mutations 1-3 exercise the half of S1 that S0 measured as
# uncovered -- and because if a statement claim is worth protecting anywhere it
# is worth protecting on the loudest claim the programme makes.
NATIVE = "F-creal-ivt-approx.json"

# The two mirrors from `e79804fdd`, with the exact text each carried while
# damaged. Restored from that commit's diff, not retyped from memory.
TOTIENT_DVD = "F-ml430-nat-totient-dvd-of-dvd-9622e44a.json"
TOTIENT_DVD_DAMAGED = (
    "theorem Nat.totient_dvd_of_dvd : ((x0 : AxNat) -> ((x1 : AxNat) -> "
    "((x2 : AxNat.dvd x0 x1) -> AxNat.dvd (AxNat.totient x0) (AxNat.totient x1))))"
)
TOTIENT_EQ = "F-ml430-nat-eq-or-eq-of-totient-eq-totient-d4d154c7.json"
TOTIENT_EQ_DAMAGED = (
    "theorem Nat.eq_or_eq_of_totient_eq_totient : ((x0 : AxNat) -> ((x1 : AxNat) -> "
    "((x2 : AxNat.dvd x0 x1) -> ((x3 : Eq.{1} AxNat (AxNat.totient x0) (AxNat.totient x1)) -> "
    "Or (Eq.{1} AxNat x0 x1) (Eq.{1} AxNat (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x0) "
    "x1)))))"
)


class FixtureStale(Exception):
    """A mutation no longer applies to its subject."""


def run(cmd: list[str]) -> int:
    return subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True).returncode


def load(name: str) -> tuple[pathlib.Path, str, dict]:
    path = FACTS / name
    if not path.is_file():
        raise FixtureStale(f"{name} is gone — the fixture names a fact that no longer exists")
    raw = path.read_text(encoding="utf-8")
    return path, raw, json.loads(raw)


def mutate_formal(data: dict, statement: str, language: str | None = None) -> dict:
    out = json.loads(json.dumps(data))
    out["formal"]["statement"] = statement
    if language is not None:
        out["formal"]["language"] = language
    return out


def swap_first_two_binders(statement: str) -> str:
    """`x1` <-> `x2`. A swapped binder keeps every token and changes the claim.

    On `ivt_approx` this exchanges the interval endpoints, turning
    "uniformly continuous on [a, b] with F a <= 0 <= F b" into a statement
    about [b, a]. Nothing about the text looks wrong."""
    if "x1" not in statement or "x2" not in statement:
        raise FixtureStale("subject no longer binds x1 and x2 — cannot swap binders")
    return statement.replace("x1", "\x00").replace("x2", "x1").replace("\x00", "x2")


def change_a_constant(statement: str) -> str:
    """One `CReal.zero` becomes `CReal.one`.

    `F a <= 0 <= F b` is the IVT's whole hypothesis; at `1` the theorem is a
    different (and weaker-sited) claim about where the sign change lives."""
    if "CReal.zero" not in statement:
        raise FixtureStale("subject no longer mentions CReal.zero — cannot change a constant")
    return statement.replace("CReal.zero", "CReal.one", 1)


def alter_a_relation(statement: str) -> str:
    """`CReal.le` becomes `CReal.lt` once. Non-strict to strict is the classic
    silent weakening, and on a constructive statement it is not a harmless
    tightening: it changes which instances the theorem covers."""
    if "CReal.le" not in statement:
        raise FixtureStale("subject no longer mentions CReal.le — cannot alter a relation")
    return statement.replace("CReal.le", "CReal.lt", 1)


def main() -> int:
    # --- positive control ------------------------------------------------
    clean_statement = run(STATEMENT_GATE)
    clean_mirror = run(MIRROR_GATE)
    print(f"STATEMENT_IDENTITY_MUTATIONS|control|clean-tree|statement={clean_statement}|mirror={clean_mirror}")
    if clean_statement != 0 or clean_mirror != 0:
        print(
            "STATEMENT_IDENTITY_MUTATIONS|ERROR|the clean tree does not pass; every "
            "rejection below would be meaningless",
            file=sys.stderr,
        )
        return 1

    results: list[tuple[str, str, int, int]] = []
    touched: dict[pathlib.Path, str] = {}

    def apply(path: pathlib.Path, original: str, data: dict) -> None:
        touched[path] = original
        path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")

    def restore() -> None:
        for path, original in touched.items():
            path.write_text(original, encoding="utf-8")
        touched.clear()

    try:
        native_path, native_raw, native = load(NATIVE)
        original = native["formal"]["statement"]

        for label, mutated in (
            ("1 swapped binders", swap_first_two_binders(original)),
            ("2 changed constant", change_a_constant(original)),
            ("3 altered relation", alter_a_relation(original)),
        ):
            if mutated == original:
                raise FixtureStale(f"{label}: mutation produced an identical statement")
            apply(native_path, native_raw, mutate_formal(native, mutated))
            results.append((label, NATIVE, run(STATEMENT_GATE), run(MIRROR_GATE)))
            restore()

        # --- 4 source drift ------------------------------------------------
        # A mirror's `formal.statement` edited away from the pinned upstream
        # source while staying a plausible Mathlib-surface proposition. This is
        # the one a token screen cannot see: it is still `lean4-surface`, still
        # uses Mathlib notation, and only the catalog hash knows it is wrong.
        mirror_path, mirror_raw, mirror = load(TOTIENT_DVD)
        upstream = mirror["formal"]["statement"]
        drifted = upstream.replace("∣", "=", 1)
        if drifted == upstream:
            raise FixtureStale("4 source drift: subject no longer carries the divides sign")
        apply(mirror_path, mirror_raw, mutate_formal(mirror, drifted))
        results.append(("4 source drift", TOTIENT_DVD, run(STATEMENT_GATE), run(MIRROR_GATE)))
        restore()

        # --- 5 our own rendering, replayed from e79804fdd -------------------
        dvd_path, dvd_raw, dvd = load(TOTIENT_DVD)
        eq_path, eq_raw, eq = load(TOTIENT_EQ)
        if dvd["formal"]["statement"] == TOTIENT_DVD_DAMAGED:
            raise FixtureStale("5: the subject already carries the damaged form")
        apply(dvd_path, dvd_raw, mutate_formal(dvd, TOTIENT_DVD_DAMAGED, "lean4"))
        apply(eq_path, eq_raw, mutate_formal(eq, TOTIENT_EQ_DAMAGED, "lean4"))
        results.append(
            ("5 our own rendering", f"{TOTIENT_DVD}+{TOTIENT_EQ}", run(STATEMENT_GATE), run(MIRROR_GATE))
        )
        restore()
    except FixtureStale as exc:
        restore()
        print(f"STATEMENT_IDENTITY_MUTATIONS|STALE|{exc}", file=sys.stderr)
        return 2
    except BaseException:
        restore()
        raise

    failed = 0
    for label, subject, statement_exit, mirror_exit in results:
        by = []
        if statement_exit != 0:
            by.append("statement-pin")
        if mirror_exit != 0:
            by.append("mirror-fidelity")
        verdict = "REJECTED" if by else "ACCEPTED"
        if not by:
            failed = 1
        print(
            f"STATEMENT_IDENTITY_MUTATIONS|{label}|{subject}|{verdict}"
            f"|by={'+'.join(by) or 'NOTHING'}"
            f"|statement_exit={statement_exit}|mirror_exit={mirror_exit}"
        )

    # Restoration is part of the contract: a check that leaves the ledger
    # mutated is worse than one that does not run.
    if run(STATEMENT_GATE) != 0 or run(MIRROR_GATE) != 0:
        print(
            "STATEMENT_IDENTITY_MUTATIONS|ERROR|the tree did not come back clean",
            file=sys.stderr,
        )
        return 1

    if failed:
        print("STATEMENT_IDENTITY_MUTATIONS|FAIL|a required mutation was accepted", file=sys.stderr)
        return 1
    print(f"STATEMENT_IDENTITY_MUTATIONS|PASS|{len(results)}/5 rejected|tree restored")
    return 0


if __name__ == "__main__":
    sys.exit(main())

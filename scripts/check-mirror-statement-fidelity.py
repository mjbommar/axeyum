#!/usr/bin/env python3
"""An `ml430` mirror must carry the proposition it mirrors, not our rendering of it.

WHAT THIS EXISTS TO STOP
------------------------

An `ml430` fact mirrors one proposition from the pinned Mathlib v4.30 source.
Its top-level ``statement`` is a prose REFERENCE BY NAME -- "The proposition
declared as ``Nat.coprime_add_self_left`` in the pinned Mathlib v4.30 source."
-- so the proposition itself lives in exactly one place, ``formal.statement``.

Nineteen mirrors had that field overwritten with the kernel's own
``Kernel::render_lean`` output::

    theorem Nat.coprime_add_self_left : ((x0 : AxNat) -> ((x1 : AxNat) -> Iff ...

Nothing was false: the theorems are real and axiom-free, and each fact still
named its Mathlib lemma in prose. But the file no longer carried the
proposition it claimed to mirror ANYWHERE, so "we proved what Mathlib states"
could not be checked from the fact -- only from git history or by going back to
the pinned source. Self-containment is the whole point of a mirror row.

It recurs because flipping a fact to ``proved`` is precisely the moment a lane
has the rendered type in hand, and writing it down is the natural thing to do.
Prose did not stop it (the count grew 1 -> 3 -> 19 as the measurement widened),
so there is a gate; and because suppressing the impulse without an outlet would
just produce the same drift again, ``formal.kernel_statement`` now exists to
hold the rendering. See
``docs/research/11-design-review/2026-08-29-nineteen-mirrors-lost-their-statement.md``.

WHY THERE IS A HASH GUARD AND NOT ONLY A TOKEN SCREEN
----------------------------------------------------

A token screen ("does it start with ``theorem``, does it say ``AxNat``") catches
the observed defect and nothing else. It cannot see a statement replaced by a
DIFFERENT plausible Lean statement, which is the same integrity failure with
better camouflage.

The preregistered catalogs pin a content hash per fact --
``mathlib-nat-int-fact-catalog-v1.json`` and ``nursery-v2-extension.json``
carry ``source_statement_sha256`` -- so for 362 of 374 mirrors the check is
exact rather than heuristic: sha256 of ``formal.statement`` must equal the pin.
The token guards remain because 12 mirrors (the ``ml430-mutation-*`` family,
deliberately mutated propositions) have no pin by construction and nothing else
would cover them.

The hash guard is also what makes the repair auditable: every restored
statement was verified against its pin, not against a second transcription.

WHY IT DOES NOT FIRE ON HEALTHY ROWS
------------------------------------

Scope is exactly the mirror programme (``F:ml430-*``). Facts outside it
legitimately carry ``render_lean`` output -- ``fact.schema.json`` says ``lean4``
means Lean kernel core and is "the form a fact should normally carry". Running
these guards ledger-wide would flag the correct majority, which is the fastest
way to make a gate ignored.

Exit 0 clean, 1 on any violation, 2 on a malformed input the gate cannot read.
"""

from __future__ import annotations

import glob
import hashlib
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# Mirror-programme fact ids. A prefix, not a substring: `ml430` appearing
# anywhere in some future unrelated id must not silently pull it into scope.
MIRROR_PREFIX = "F:ml430-"

# The mirror convention, held by all 355 healthy mirrors at the time this
# landed. `lean4` means kernel core (`render_lean`); a mirror states Mathlib's
# surface proposition, so it is `lean4-surface`.
MIRROR_LANGUAGE = "lean4-surface"

# Declaration keywords a kernel rendering opens with. A Mathlib surface
# PROPOSITION never does -- it is a type, not a declaration.
KERNEL_PREFIXES = ("theorem ", "def ", "axiom ", "opaque ", "instance ", "abbrev ")

# `lean_pp` roots. These are this kernel's non-shadowing names for its own
# carriers and cannot appear in a Mathlib surface statement, which spells the
# naturals `ℕ` and the integers `ℤ`.
#
# Matched with a word boundary on the LEFT only: `AxNat.gcd` must hit, and a
# hypothetical Mathlib identifier ending in `...AxNat` must not.
KERNEL_CARRIERS = ("AxNat", "AxInt", "AxRat", "AxReal", "AxString", "AxChar")
KERNEL_CARRIER_RE = re.compile(r"(?<![A-Za-z0-9_.])(?:" + "|".join(KERNEL_CARRIERS) + r")\b")

# Explicit universe annotation, e.g. `Eq.{1}`, `Sort.{u}`. Lean's pretty-printer
# suppresses these in surface output; `render_lean` emits them.
UNIVERSE_RE = re.compile(r"\.\{[0-9a-zA-Z_, +]*\}")

# `render_lean`'s generated binder names: `(x0 : ...)`, `(x12 : ...)`. Mathlib
# binders are `{m n : ℕ}`, `(a b c : ℤ}` and so on.
KERNEL_BINDER_RE = re.compile(r"\(x\d+ : ")

CATALOG_GLOB = "artifacts/autogenesis/*.json"


def _sha(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def load_pins(root: str) -> dict[str, set[str]]:
    """fact_id -> the set of preregistered statement hashes claimed for it.

    Derived from whatever preregistered artefact carries the pair, never from a
    hand-maintained list: a list would measure the maintainer's memory, and a
    new draw's catalog would be silently out of scope.
    """
    pins: dict[str, set[str]] = {}
    for path in sorted(glob.glob(os.path.join(root, CATALOG_GLOB))):
        try:
            with open(path, encoding="utf-8") as fh:
                doc = json.load(fh)
        except (OSError, ValueError):
            continue
        if not isinstance(doc, dict):
            continue
        for rows in doc.values():
            if not isinstance(rows, list):
                continue
            for row in rows:
                if not isinstance(row, dict):
                    continue
                fid, digest = row.get("fact_id"), row.get("source_statement_sha256")
                if isinstance(fid, str) and isinstance(digest, str) and digest:
                    pins.setdefault(fid, set()).add(digest)
    return pins


def load_facts(root: str) -> list[tuple[str, dict]]:
    out = []
    for path in sorted(glob.glob(os.path.join(root, "artifacts/facts/*.json"))):
        with open(path, encoding="utf-8") as fh:
            doc = json.load(fh)
        if isinstance(doc, dict):
            out.append((path, doc))
    return out


def check(root: str) -> tuple[list[str], dict[str, int]]:
    violations: list[str] = []
    stats = {"facts": 0, "mirrors": 0, "pinned": 0, "unpinned": 0}

    pins = load_pins(root)
    facts = load_facts(root)

    # `kernel_statement` is a ledger-wide field, so its one structural rule is
    # checked over every fact rather than only over mirrors. Everything below
    # this loop is scoped to the mirror programme, where the guards would
    # otherwise flag the correct majority.
    for path, doc in facts:
        stats["facts"] += 1
        formal = doc.get("formal")
        if not isinstance(formal, dict):
            continue
        # G7 -- `kernel_statement` is meaningless without the declaration it renders.
        if "kernel_statement" in formal and not isinstance(formal.get("kernel_theorem"), str):
            violations.append(
                "%s: `formal.kernel_statement` is set but `formal.kernel_theorem` does "
                "not name a declaration, so nothing says what was rendered"
                % os.path.basename(path)
            )

    mirrors = [(p, d) for p, d in facts if str(d.get("id", "")).startswith(MIRROR_PREFIX)]

    for path, doc in mirrors:
        stats["mirrors"] += 1
        name = os.path.basename(path)
        fid = doc["id"]
        formal = doc.get("formal")
        if not isinstance(formal, dict):
            violations.append("%s: no `formal` object" % name)
            continue
        stmt = formal.get("statement")
        if not isinstance(stmt, str) or not stmt:
            violations.append("%s: `formal.statement` is missing or empty" % name)
            continue

        # G1 -- a declaration keyword. `render_lean` prints `theorem NAME : TYPE`;
        # a mirror states the TYPE.
        if stmt.startswith(KERNEL_PREFIXES):
            violations.append(
                "%s: `formal.statement` opens with a kernel DECLARATION keyword "
                "(%r) -- it should be the Mathlib proposition, and the rendering "
                "belongs in `formal.kernel_statement`" % (name, stmt.split(" ", 1)[0])
            )

        # G2 -- a `lean_pp` carrier root. Mathlib says `ℕ`; we say `AxNat`.
        hit = KERNEL_CARRIER_RE.search(stmt)
        if hit:
            violations.append(
                "%s: `formal.statement` names the kernel carrier %r -- that is our "
                "rendering, not Mathlib's proposition" % (name, hit.group(0))
            )

        # G3 -- an explicit universe annotation (`Eq.{1}`).
        hit = UNIVERSE_RE.search(stmt)
        if hit:
            violations.append(
                "%s: `formal.statement` carries the explicit universe annotation %r, "
                "which only `render_lean` emits" % (name, hit.group(0))
            )

        # G4 -- `render_lean`'s generated binder names.
        hit = KERNEL_BINDER_RE.search(stmt)
        if hit:
            violations.append(
                "%s: `formal.statement` uses a generated kernel binder %r rather than "
                "Mathlib's own binder names" % (name, hit.group(0))
            )

        # G5 -- the mirror language convention. A mirror states surface syntax;
        # `lean4` would assert the statement IS kernel core.
        if formal.get("language") != MIRROR_LANGUAGE:
            violations.append(
                "%s: `formal.language` is %r; every mirror states Mathlib surface "
                "syntax and must be %r" % (name, formal.get("language"), MIRROR_LANGUAGE)
            )

        # G6 -- exact fidelity to the preregistered pin, where one exists.
        claimed = pins.get(fid)
        if claimed:
            stats["pinned"] += 1
            if _sha(stmt) not in claimed:
                violations.append(
                    "%s: `formal.statement` does not match the preregistered "
                    "`source_statement_sha256` (%s vs %s) -- the pinned Mathlib "
                    "proposition is not what this fact carries"
                    % (name, _sha(stmt)[:16], ", ".join(sorted(s[:16] for s in claimed)))
                )
        else:
            stats["unpinned"] += 1

    # G8 -- non-vacuity, on the SCOPE. A gate that examined nothing is worse
    # than no gate: it reports green for a ledger it never read.
    if stats["mirrors"] == 0:
        violations.append(
            "the gate examined ZERO mirror facts -- the `%s` scope selector is broken, "
            "not the ledger" % MIRROR_PREFIX
        )

    # G9 -- non-vacuity, on the HASH CHECK specifically. Guarded on
    # `mirrors > 0` so it is independent of G8 rather than a second symptom of
    # it: a broken catalog lookup silently downgrades this gate to a token
    # screen while every other line of output looks identical.
    if stats["mirrors"] > 0 and stats["pinned"] == 0:
        violations.append(
            "the gate verified ZERO statement hashes across %d mirrors -- no "
            "preregistered catalog was read, so the exact check did not run at all"
            % stats["mirrors"]
        )

    return violations, stats


def main(argv: list[str]) -> int:
    root = argv[1] if len(argv) > 1 else ROOT
    try:
        violations, stats = check(root)
    except (OSError, ValueError) as exc:
        print("MIRROR_STATEMENT_FIDELITY|ERROR|%s" % exc)
        return 2

    for v in violations:
        print("  !! " + v)
    print(
        "MIRROR_STATEMENT_FIDELITY|facts=%d|mirrors=%d|hash_verified=%d|unpinned=%d"
        "|violations=%d|verdict=%s"
        % (
            stats["facts"],
            stats["mirrors"],
            stats["pinned"],
            stats["unpinned"],
            len(violations),
            "FAIL" if violations else "PASS",
        )
    )
    return 1 if violations else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))

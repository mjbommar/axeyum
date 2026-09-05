#!/usr/bin/env python3
"""Measure and ratchet the ADR-0601 SS2 `cas-internal` residue (roadmap W1-13).

Why this exists
----------------
ADR-0601 SS2 requires every `cas-certificate` fact's evidence to classify as
`kernel-reconstructed` (an independent re-derivation through the kernel trust
anchor exists) or `cas-internal` (the checker never leaves the CAS's own
normal form) -- never a third, unclassifiable case. `scripts/validate-facts.py`
already computes this split (`classify_cas_certificate_fact`) and prints it in
its summary line, but nothing FAILS if the `cas-internal` share grows at the
expense of a fact that used to reconstruct: the summary line is descriptive,
not a gate. `docs/math-department/11-applied-and-computational.md`'s W1-13
names this residue "the honest boundary of the trusted pipeline, and it
should be a published, falling number" -- a number with nobody keeping it
from rising is not a falling number, it is a sentence.

`scripts/check-cas-substance.py` (ADR-0622) already ratchets something
adjacent and is easy to mistake for this gate: it floors WHAT the 14
`kernel-reconstructed` facts' kernel obligations establish (shape:
`combination`/`refl`/`evaluation`/...), never the COUNT split between
`kernel-reconstructed` and `cas-internal` itself. The
2026-09-04 applied-and-computational audit found both scripts and could not
determine which question either one answers without running them -- this
file is the answer to "measure the residue", not "measure the substance of
what already reconstructed".

What this gate does
--------------------
1. Reads every `artifacts/facts/*.json` fact whose `proof_route` is
   `cas-certificate` and classifies it with `validate-facts.py`'s own
   `classify_cas_certificate_fact` -- ONE definition of the classification,
   reused rather than reimplemented, exactly as `check-cas-substance.py`
   reuses it.
2. Reports the headline split (total / kernel-reconstructed / cas-internal /
   unrecognized) and, with `--report`, the same split per `formal.fragment`
   family.
3. Ratchets a FLOOR: every fact recorded as `kernel-reconstructed` in the
   committed `.ratchet` file must still classify as `kernel-reconstructed`
   today. A fact regressing to `cas-internal`, going `unrecognized`, or
   disappearing from the ledger entirely is refused. Nothing here refuses a
   NEW `cas-internal` fact or a shrinking total `cas-internal` count growing
   in absolute terms as the ledger grows -- ADR-0601 makes `cas-internal` an
   honest label, not a forbidden one, so only regression of the floor is a
   defect. `unrecognized` is refused unconditionally, at any count, because
   ADR-0601 SS2 allows no third case at all.

Exit status: 0 when the floor holds, 1 on any violation, 2 on a usage error.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
RATCHET = REPO_ROOT / "scripts" / "check-cas-internal-residue.ratchet"


def _load_validate_facts():
    """Import `scripts/validate-facts.py`, whose name is not an identifier.

    Reused rather than reimplemented on purpose, exactly as
    `check-cas-substance.py` does: "which facts are kernel-reconstructed"
    must have exactly one definition, or this gate and the headline it
    qualifies can disagree about which facts they are talking about.
    """
    path = REPO_ROOT / "scripts" / "validate-facts.py"
    spec = importlib.util.spec_from_file_location("validate_facts_residue", path)
    if spec is None or spec.loader is None:  # pragma: no cover - defensive
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


RATCHET_HEADER = """\
# The ADR-0601 SS2 `cas-certificate` classification floor -- W1-13's
# `cas-internal` residue. One row per fact:
#
#   <fact id>\t<kernel-reconstructed|cas-internal|unrecognized>\t<fragment>
#
# Regenerate with: python3 scripts/check-cas-internal-residue.py --update
#
# A `kernel-reconstructed` row is ground this ledger has already
# established: an independent re-derivation through the trust anchor exists.
# Losing that -- the row flipping to `cas-internal`, going `unrecognized`, or
# disappearing -- is a real regression and the gate refuses it. GAINING a
# kernel-reconstructed fact, or adding any new `cas-internal` fact, needs no
# edit: the residue may grow in absolute count as the ledger grows, so long
# as no fact that used to reconstruct stops doing so. See ADR-0601 and
# docs/math-department/11-applied-and-computational.md (W1-13).
"""


def read_ratchet(path: Path) -> dict[str, tuple[str, str]] | None:
    """`{fact id: (classification, fragment)}`, or `None` when absent."""
    if not path.is_file():
        return None
    rows: dict[str, tuple[str, str]] = {}
    for line in path.read_text().splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) != 3:
            continue
        rows[parts[0]] = (parts[1], parts[2])
    return rows


def current_classification(
    validate_facts, facts_dir: Path
) -> dict[str, tuple[str, str]]:
    """`{fact id: (classification, fragment)}` for every `cas-certificate` fact."""
    current: dict[str, tuple[str, str]] = {}
    for path in sorted(facts_dir.glob("*.json")):
        fact = json.loads(path.read_text())
        if fact.get("proof_route") != "cas-certificate":
            continue
        classification = validate_facts.classify_cas_certificate_fact(fact)
        fragment = (fact.get("formal") or {}).get("fragment") or "<none>"
        current[fact.get("id", f"<{path.name}>")] = (classification, fragment)
    return current


def ratchet_errors(
    recorded: dict[str, tuple[str, str]], current: dict[str, tuple[str, str]]
) -> list[str]:
    """The floor rule: a recorded `kernel-reconstructed` fact must stay one."""
    errors: list[str] = []
    for fid in sorted(recorded):
        was_classification, _was_fragment = recorded[fid]
        if was_classification != "kernel-reconstructed":
            continue
        if fid not in current:
            errors.append(
                f"{fid}: recorded as kernel-reconstructed and is gone from the "
                f"ledger now. A smaller headline is not a pass; if the removal "
                f"is deliberate, record it with --update so the diff is visible."
            )
            continue
        now_classification, _now_fragment = current[fid]
        if now_classification != "kernel-reconstructed":
            errors.append(
                f"{fid}: recorded as kernel-reconstructed and now classifies "
                f"as {now_classification!r}. This is the ADR-0601 SS2 residue "
                f"growing at a fact that used to reconstruct through the "
                f"kernel -- exactly the regression this gate exists to catch."
            )
    return errors


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--facts-root",
        default=str(REPO_ROOT),
        help="repository root holding artifacts/facts",
    )
    parser.add_argument(
        "--report",
        action="store_true",
        help="print the per-fragment breakdown as well as the headline",
    )
    parser.add_argument(
        "--update",
        action="store_true",
        help="rewrite the ratchet file from the current ledger, then exit",
    )
    parser.add_argument(
        "--ratchet",
        default=str(RATCHET),
        help="ratchet file to check against (the controls point this elsewhere)",
    )
    args = parser.parse_args(argv)

    root = Path(args.facts_root)
    facts_dir = root / "artifacts" / "facts"
    if not facts_dir.is_dir():
        print(f"FAIL: no fact directory at {facts_dir}", file=sys.stderr)
        return 2

    validate_facts = _load_validate_facts()
    current = current_classification(validate_facts, facts_dir)

    total = len(current)
    by_class: dict[str, int] = {}
    by_fragment: dict[str, dict[str, int]] = {}
    for fid, (cls, frag) in current.items():
        by_class[cls] = by_class.get(cls, 0) + 1
        by_fragment.setdefault(frag, {})
        by_fragment[frag][cls] = by_fragment[frag].get(cls, 0) + 1

    unrecognized = by_class.get("unrecognized", 0)
    kernel_reconstructed = by_class.get("kernel-reconstructed", 0)
    cas_internal = by_class.get("cas-internal", 0)

    print(
        f"cas-certificate: {total} total -- kernel-reconstructed "
        f"{kernel_reconstructed}, cas-internal {cas_internal}, "
        f"unrecognized {unrecognized}"
    )
    if total:
        print(f"  cas-internal residue share: {cas_internal / total:.1%}")

    if args.report:
        print()
        header = f"  {'fragment':45s} {'kernel-reconstructed':>21s} {'cas-internal':>13s} {'unrecognized':>13s}"
        print(header)
        for frag in sorted(by_fragment):
            counts = by_fragment[frag]
            print(
                f"  {frag:45s} {counts.get('kernel-reconstructed', 0):>21d} "
                f"{counts.get('cas-internal', 0):>13d} "
                f"{counts.get('unrecognized', 0):>13d}"
            )
        print()

    ratchet_path = Path(args.ratchet)
    if args.update:
        ratchet_path.write_text(
            RATCHET_HEADER
            + "".join(
                f"{fid}\t{cls}\t{frag}\n"
                for fid, (cls, frag) in sorted(current.items())
            )
        )
        print(f"recorded {total} cas-certificate fact(s) in {ratchet_path}")
        return 0

    errors: list[str] = []
    if unrecognized:
        errors.append(
            f"{unrecognized} cas-certificate fact(s) classify as "
            f"'unrecognized' -- neither kernel-reconstructed nor cas-internal. "
            f"ADR-0601 SS2 requires every cas-certificate fact to be one or "
            f"the other; validate-facts.py's own validate_one should already "
            f"refuse this, so seeing it here means that guard was weakened."
        )

    recorded = read_ratchet(ratchet_path)
    if recorded is None:
        print(
            f"FAIL: no ratchet at {ratchet_path}. Without it this gate cannot "
            f"notice a fact regressing from kernel-reconstructed to "
            f"cas-internal. Run --update to record the current floor.",
            file=sys.stderr,
        )
        return 1
    errors.extend(ratchet_errors(recorded, current))

    if errors:
        print(f"FAIL: {len(errors)} cas-internal residue violation(s)")
        for error in errors:
            print(f"  - {error}")
        return 1

    was_kernel_reconstructed = sum(
        1 for cls, _frag in recorded.values() if cls == "kernel-reconstructed"
    )
    print(
        f"OK: {kernel_reconstructed} kernel-reconstructed cas-certificate "
        f"fact(s) (floor {was_kernel_reconstructed}, all held), "
        f"{cas_internal} cas-internal, {unrecognized} unrecognized"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

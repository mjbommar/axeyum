#!/usr/bin/env python3
"""Gate the SUBSTANCE of every `kernel-reconstructed` `cas-certificate` fact.

Why this exists
---------------
`scripts/validate-facts.py` splits the `cas-certificate` route into
`kernel-reconstructed` and `cas-internal` (ADR-0601 SS2) by asking whether an
executed `cargo test`/`cargo run` segment NAMES the `axeyum-lean-kernel`
package.  That is a real question and it is not the question a reader of the
headline thinks is being answered.  It never inspects WHAT the kernel was asked
to check, so the counter moves identically for

    poly_expr(X) = Rat.ofInt 1 * poly_expr(X)          <- true of every X

and for a six-variable identity in which sixteen monomials from two
independently-derived geometric predicates cancel to eight.  Both run
`Kernel::add_declaration`, both are admitted axiom-free, both read as
`kernel-reconstructed 14`.

Measured 2026-08-30 over all 14: one of them is the first kind
(`F:geometry-thales-cofactor-identity-kernel-checked`, whose registering lane
found this and disclosed it in prose), and a second candidate was correctly
declined before registration because its certificate is entirely empty
(`varignon-midpoint-parallelogram`: no coordinates, no generators, both
conclusion polynomials already `{"terms": []}`).  Two lanes' judgement caught
both edges.  Judgement does not scale to N lanes; this does.

What it refuses
---------------
Every fact whose `proof_route` is `cas-certificate` and which
`classify_cas_certificate_fact` calls `kernel-reconstructed` must carry a
`cas_substance` block, and:

  1. it must declare a `shape` from `cas_substance.SHAPES`;
  2. it must name a `certificate` artifact, or say why none exists;
  3. where it names one, the DERIVED shape must equal the declared shape --
     this is the half a lane cannot talk its way around, because the number
     comes from the CAS's own output;
  4. a non-discriminating shape (`empty`, `refl`) must be DISCLOSED, in a
     `disclosure` string and in an `axiom_footprint` entry named by
     `disclosure_axiom_key`, so the weakness is where a reader of the fact
     will hit it and not only in a validator's summary;
  5. shape `empty` is refused outright -- there is nothing to reconstruct;
  6. independently of any certificate, if the fact's own `formal.statement`
     parses and contains an equation that is `X = X` after erasing
     multiplication by 1, the declared shape must be `refl`.

Registration is the honest outcome for a weak-but-real reconstruction, which is
why nothing here excludes `refl`.  What it forbids is `refl` reading the same
as `combination`.

What it does NOT establish, stated because a gate that implies coverage it
lacks is the defect this file exists to fix
-----------------------------------------------------------------------------
Rule 3 is only available for facts naming a certificate artifact: 6 of the 14.
The other 8 reconstruct sign brackets and coefficient-matching identities built
inside a Rust test, with no JSON certificate to derive from, so their declared
shape is checked by rules 1, 2, 5 and 6 and is otherwise SELF-REPORTED.  The
report prints that split as a number rather than leaving it implicit.  Closing
it means having those producers emit certificates; that is future work and is
recorded as such in ADR-0622.

Exit status: 0 when every fact passes, 1 on any violation, 2 on a usage error.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))

from cas_substance import (  # noqa: E402
    NON_DISCRIMINATING_SHAPES,
    SHAPES,
    analyse_certificate,
    statement_is_refl_shaped,
)


def _load_validate_facts():
    """Import `scripts/validate-facts.py`, whose name is not an identifier.

    Reused rather than reimplemented on purpose: "which facts are
    kernel-reconstructed" must have exactly one definition, or this gate and the
    headline it qualifies can disagree about which facts they are talking about.
    """
    path = REPO_ROOT / "scripts" / "validate-facts.py"
    spec = importlib.util.spec_from_file_location("validate_facts", path)
    if spec is None or spec.loader is None:  # pragma: no cover - defensive
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def axiom_footprint_keys(fact: dict) -> set[str]:
    """The `key` half of each `key: prose` entry in `axiom_footprint`."""
    keys = set()
    for entry in fact.get("axiom_footprint") or []:
        if isinstance(entry, str):
            keys.add(entry.split(":", 1)[0].strip())
    return keys


def check_fact(fact: dict, facts_root: Path) -> tuple[list[str], dict | None]:
    """Check one kernel-reconstructed fact.  Returns (errors, substance record)."""
    errors: list[str] = []
    fid = fact.get("id", "<unknown>")
    substance = fact.get("cas_substance")

    if not isinstance(substance, dict):
        errors.append(
            f"{fid}: classifies as kernel-reconstructed but carries no "
            f"`cas_substance` block. Every such fact must say what its kernel "
            f"obligation establishes; naming the axeyum-lean-kernel package is "
            f"not that (ADR-0622)."
        )
        return errors, None

    declared_shape = substance.get("shape")
    if declared_shape not in SHAPES:
        errors.append(
            f"{fid}: cas_substance.shape {declared_shape!r} is not one of "
            f"{list(SHAPES)}."
        )

    if declared_shape == "empty":
        errors.append(
            f"{fid}: cas_substance.shape is `empty` -- a certificate with no "
            f"coordinates, no generators and an empty conclusion polynomial has "
            f"nothing to reconstruct, so the fact must not be registered as a "
            f"kernel reconstruction at all."
        )

    if "certificate" not in substance:
        errors.append(
            f"{fid}: cas_substance has no `certificate` key. Name the artifact "
            f"the shape is derived from, or set it to null and say why in "
            f"`derivation_declined_reason`."
        )
    else:
        certificate_path = substance.get("certificate")
        if certificate_path is None:
            reason = (substance.get("derivation_declined_reason") or "").strip()
            if not reason:
                errors.append(
                    f"{fid}: cas_substance.certificate is null, so the declared "
                    f"shape is self-reported and unverifiable here. "
                    f"`derivation_declined_reason` must say why no certificate "
                    f"artifact exists."
                )
        else:
            resolved = facts_root / certificate_path
            if not resolved.is_file():
                errors.append(
                    f"{fid}: cas_substance.certificate {certificate_path!r} is not "
                    f"a file. A path that does not resolve derives nothing."
                )
            else:
                derived = analyse_certificate(json.loads(resolved.read_text()))
                if derived["shape"] != declared_shape:
                    errors.append(
                        f"{fid}: cas_substance.shape is {declared_shape!r} but the "
                        f"certificate {certificate_path} derives {derived['shape']!r} "
                        f"(active generators per conclusion: "
                        f"{[c['active_generators'] for c in derived['conclusions']]}). "
                        f"The certificate is the authority."
                    )
                substance = {**substance, "_derived": derived}

    if declared_shape in NON_DISCRIMINATING_SHAPES:
        if not (substance.get("disclosure") or "").strip():
            errors.append(
                f"{fid}: shape {declared_shape!r} does not discriminate this "
                f"theorem from any other, so `cas_substance.disclosure` must say "
                f"so in full. Registration with disclosure is the honest outcome; "
                f"silence is not."
            )
        key = (substance.get("disclosure_axiom_key") or "").strip()
        if not key:
            errors.append(
                f"{fid}: shape {declared_shape!r} requires "
                f"`cas_substance.disclosure_axiom_key` naming the "
                f"`axiom_footprint` entry that carries the disclosure."
            )
        elif key not in axiom_footprint_keys(fact):
            errors.append(
                f"{fid}: cas_substance.disclosure_axiom_key {key!r} names no entry "
                f"in this fact's axiom_footprint. A reader of the fact must meet "
                f"the disclosure where the assumptions are listed, not only here."
            )

    text_refl = statement_is_refl_shaped((fact.get("formal") or {}).get("statement") or "")
    if text_refl is True and declared_shape != "refl":
        errors.append(
            f"{fid}: formal.statement contains an equation that is X = X once "
            f"multiplication by 1 is erased, but cas_substance.shape is "
            f"{declared_shape!r}. Such an obligation is refl-shaped whatever the "
            f"certificate says."
        )

    return errors, substance


# --------------------------------------------------------------------------
# THE RATCHET.  The headline count is DERIVED -- 12 registered mutants each kill
# a control and the number moves under mutation, so it is not a literal -- and
# that is not the same as being defended.  Measured 2026-08-30:
#
#   strip a fact's kernel reconstruction AND its cas_substance block -> exit 0,
#                                                            "OK: 13 ..."
#   strip the reconstruction but KEEP the block               -> exit 1, G12
#   delete the fact file outright                             -> exit 0,
#                                                            "OK: 13 ..."
#
# So it catches an INCONSISTENT downgrade and passes a CONSISTENT one.  A gate
# that reports a smaller number as success cannot notice deletion, and this is
# the ledger's own headline metric.  Compare `--expect-axioms 26`, which is what
# a pinned expectation looks like elsewhere here.
#
# What the floor IS, stated plainly because a ratchet with a hand-chosen number
# is a wish: it is the SET of facts that reached kernel reconstruction, with,
# for each, the two properties this gate can actually verify -- whether its
# shape was DERIVED from a committed certificate, and whether that shape is
# DISCRIMINATING.  Nothing is asserted about facts that do not exist yet:
# growth is free and needs no edit here.
#
# What it REFUSES:
#   R1 a ratcheted fact that no longer classifies as kernel-reconstructed --
#      downgraded to `cas-internal`, or the file deleted outright;
#   R2 a ratcheted fact whose shape was derived from a certificate and is now
#      self-reported (it lost the artifact, so the gate stopped checking it);
#   R3 a ratcheted fact whose shape was discriminating and is now `refl` or
#      `empty`.
#
# All three are LOSSES OF ESTABLISHED GROUND, which is the only thing a ratchet
# should refuse.  Any of them can be recorded deliberately with `--update`, and
# the diff is then visible in review rather than absorbed into a smaller
# headline.  A missing or empty ratchet file is refused outright: this gate has
# had a nonzero floor since the day it was written, so an empty one means the
# file was lost, not that the ledger emptied.
RATCHET = REPO_ROOT / "scripts" / "check-cas-substance.ratchet"

# The per-fact ratchet alone still has one hole, and it is worth naming rather
# than hiding: deleting a fact AND its ratchet row in one commit satisfies every
# rule above.  That is true of every baseline in this repository -- `--update`
# exists precisely so a deliberate loss is recorded -- but here the number IS
# the headline, so it also carries an absolute floor, which is what
# `--expect-axioms 26` looks like elsewhere in this ledger.  Raise it when the
# ledger grows; lowering it is a published retreat, not a maintenance edit.
MIN_KERNEL_RECONSTRUCTED = 14

RATCHET_HEADER = """\
# The kernel-reconstructed cas-certificate floor. One row per fact:
#
#   <fact id>\t<derived|declared>\t<discriminating|non-discriminating>
#
# Regenerate with: python3 scripts/check-cas-substance.py --update
#
# A row here is ground this ledger has already established. Losing one is a
# real regression and the gate refuses it; GAINING a fact needs no edit. See
# ADR-0699 for why the count alone was not enough.
"""


def read_ratchet(path):
    """`{fact id: (provenance, discriminating)}`, or None when absent."""
    if not path.is_file():
        return None
    rows = {}
    for line in path.read_text().splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) != 3:
            continue
        rows[parts[0]] = (parts[1], parts[2] == "discriminating")
    return rows


def ratchet_errors(recorded, current):
    """R1/R2/R3. `current` is `{fact id: (provenance, discriminating)}`."""
    errors = []
    for fid in sorted(recorded):
        was_provenance, was_discriminating = recorded[fid]
        if fid not in current:
            errors.append(
                f"{fid}: recorded as kernel-reconstructed and is not one now. "
                f"Either its checker stopped naming the kernel package or the "
                f"fact is gone. A smaller headline is not a pass; if the "
                f"downgrade is deliberate, record it with --update so the diff "
                f"is visible."
            )
            continue
        now_provenance, now_discriminating = current[fid]
        if was_provenance == "derived" and now_provenance != "derived":
            errors.append(
                f"{fid}: its shape was DERIVED from a committed certificate and "
                f"is now self-reported. The gate can no longer check the half a "
                f"lane cannot talk its way around (ADR-0622 rule 3)."
            )
        if was_discriminating and not now_discriminating:
            errors.append(
                f"{fid}: its shape was discriminating and is now "
                f"non-discriminating. Registration stays honest for a weak "
                f"reconstruction; silently BECOMING weak does not."
            )
    return errors


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--facts-root",
        default=str(REPO_ROOT),
        help="repository root holding artifacts/facts and the certificate artifacts",
    )
    parser.add_argument(
        "--report",
        action="store_true",
        help="print the per-fact substance table as well as the verdict",
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
    parser.add_argument(
        "--min-reconstructed",
        type=int,
        default=MIN_KERNEL_RECONSTRUCTED,
        help="absolute floor on the kernel-reconstructed count (the fixture "
             "controls set this to 0 so they can exercise one rule at a time)",
    )
    args = parser.parse_args(argv)

    root = Path(args.facts_root)
    facts_dir = root / "artifacts" / "facts"
    if not facts_dir.is_dir():
        print(f"FAIL: no fact directory at {facts_dir}", file=sys.stderr)
        return 2

    validate_facts = _load_validate_facts()

    errors: list[str] = []
    rows: list[tuple[str, str, str, bool]] = []
    cas_facts = 0
    kernel_reconstructed = 0

    for path in sorted(facts_dir.glob("*.json")):
        fact = json.loads(path.read_text())
        if fact.get("proof_route") != "cas-certificate":
            continue
        cas_facts += 1
        classification = validate_facts.classify_cas_certificate_fact(fact)
        if classification != "kernel-reconstructed":
            if isinstance(fact.get("cas_substance"), dict):
                errors.append(
                    f"{fact.get('id')}: carries a `cas_substance` block but "
                    f"classifies as {classification!r}, not kernel-reconstructed. "
                    f"The block asserts what a KERNEL obligation establishes; on a "
                    f"fact whose checker never leaves the CAS it asserts nothing."
                )
            continue
        kernel_reconstructed += 1
        fact_errors, substance = check_fact(fact, root)
        errors.extend(fact_errors)
        shape = (substance or {}).get("shape", "<missing>")
        derived = "derived" if (substance or {}).get("_derived") else "declared"
        rows.append(
            (
                fact.get("id", "<unknown>"),
                str(shape),
                derived,
                shape not in NON_DISCRIMINATING_SHAPES,
            )
        )

    if args.report:
        print(f"cas-certificate facts: {cas_facts}")
        print(f"kernel-reconstructed:  {kernel_reconstructed}")
        print()
        print(f"  {'fact':62s} {'shape':12s} {'provenance':10s} discriminating")
        for fid, shape, derived, disc in rows:
            print(f"  {fid:62s} {shape:12s} {derived:10s} {disc}")
        print()
        by_shape: dict[str, int] = {}
        for _, shape, _, _ in rows:
            by_shape[shape] = by_shape.get(shape, 0) + 1
        for shape in SHAPES:
            if shape in by_shape:
                mark = "" if shape not in NON_DISCRIMINATING_SHAPES else "   <- establishes nothing specific"
                print(f"  {shape:12s} {by_shape[shape]:3d}{mark}")
        derived_count = sum(1 for _, _, d, _ in rows if d == "derived")
        print()
        print(
            f"  shape derived from a certificate: {derived_count} of {len(rows)}; "
            f"the other {len(rows) - derived_count} are self-reported and this gate "
            f"cannot verify them (ADR-0622)."
        )
        print()

    current = {
        fid: (provenance, discriminating)
        for fid, _shape, provenance, discriminating in rows
    }

    ratchet_path = Path(args.ratchet)
    if args.update:
        ratchet_path.write_text(
            RATCHET_HEADER
            + "".join(
                f"{fid}\t{provenance}\t"
                f"{'discriminating' if discriminating else 'non-discriminating'}\n"
                for fid, (provenance, discriminating) in sorted(current.items())
            )
        )
        print(f"recorded {len(current)} kernel-reconstructed fact(s) in {ratchet_path}")
        return 0

    recorded = read_ratchet(ratchet_path)
    if recorded is None:
        print(
            f"FAIL: no ratchet at {ratchet_path}. Without it this gate reports a "
            f"SMALLER number as success and cannot notice a deletion. Run "
            f"--update to record the current floor.",
            file=sys.stderr,
        )
        return 1
    if len(recorded) < args.min_reconstructed:
        print(
            f"FAIL: the ratchet at {ratchet_path} names {len(recorded)} fact(s) "
            f"against an absolute floor of {args.min_reconstructed}. Trimming "
            f"the ratchet and the ledger together satisfies every per-fact rule; "
            f"this is what stops that being silent.",
            file=sys.stderr,
        )
        return 1
    if kernel_reconstructed < args.min_reconstructed:
        print(
            f"FAIL: {kernel_reconstructed} kernel-reconstructed cas-certificate "
            f"fact(s) against an absolute floor of {args.min_reconstructed}. A "
            f"smaller headline is a retreat to publish, not a pass.",
            file=sys.stderr,
        )
        return 1
    errors.extend(ratchet_errors(recorded, current))

    if errors:
        print(f"FAIL: {len(errors)} cas-certificate substance violation(s)")
        for error in errors:
            print(f"  - {error}")
        return 1

    print(
        f"OK: {kernel_reconstructed} kernel-reconstructed cas-certificate fact(s) "
        f"carry a checked cas_substance block "
        f"(ratchet floor {len(recorded)}, all held)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

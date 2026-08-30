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

    if errors:
        print(f"FAIL: {len(errors)} cas-certificate substance violation(s)")
        for error in errors:
            print(f"  - {error}")
        return 1

    print(
        f"OK: {kernel_reconstructed} kernel-reconstructed cas-certificate fact(s) "
        f"carry a checked cas_substance block"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

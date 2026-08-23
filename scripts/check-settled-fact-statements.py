#!/usr/bin/env python3
"""A settled fact's statement is what the ledger CLAIMS. It must not drift.

On 2026-08-22 commit `30737a155` presented itself as a route upgrade on
`F:geometry-varignon-midpoint-parallelogram`, cas-certificate -> kernel-lean. It
was not one. It REPLACED the fact's `formal.statement` — smtlib2 over `Real`
became lean4 over `CPoint` — dropped three named assumptions, and discarded two
checked witness-replay evidence rows. Those are different propositions over
different carriers and neither formally implies the other.

Nothing caught it for a day. `validate-facts.py` checks a fact's structure and
its semantic consistency (a `proved` fact with nothing `checked` fails, an
`open` one carrying evidence fails) and has no opinion about a statement
CHANGING. Nor should it: it sees one snapshot, and drift is a property of two.

Why it matters is the checker lesson one level up. CLAUDE.md: "at N lanes the
ledger IS the product, so a checker that cannot fail is worse than no checker."
A fact whose statement can be edited to match whatever was proved is exactly
that — "we proved X" degrades into "we proved something we then labelled X", and
nothing in the diff looks wrong.

A full-history audit found this was the ONLY carrier change among 140 settled
facts. Six other statement edits exist and all are benign: `66cb03eff` replaced
hand-written seed types with kernel-dumped ones (a correction toward truth), and
`1c33d3405` was the `Real` -> `AxReal` rename. So the rule here is not "never
edit" — legitimate corrections happen — it is "an edit must be a deliberate,
recorded act rather than a side effect".

MECHANISM: `artifacts/ontology/settled-fact-statement-pins.json` holds the
SHA-256 of `formal.statement` for every settled fact. A changed statement fails
unless an `amendments` row names the fact, both digests, and a reason. A fact
becoming settled adds a pin (that is not drift). A fact LEAVING settled status,
or vanishing, is reported — a retraction should be visible.

FAIL-CLOSED. An unreadable or empty manifest is an error, not a quiet pass: a
guard whose subject has vanished reports the same "no violations" as one that
works, and this repository has shipped that exact defect (40 of 162 checker runs
exiting 0 on completion alone).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
FACTS = ROOT / "artifacts/facts"
PINS = ROOT / "artifacts/ontology/settled-fact-statement-pins.json"
SETTLED = {"proved", "computed"}


class StatementDriftError(Exception):
    pass


def digest(statement: object) -> str:
    return hashlib.sha256(str(statement).encode()).hexdigest()


def read_facts() -> dict[str, dict]:
    if not FACTS.is_dir():
        raise StatementDriftError("artifacts/facts is not a directory")
    out: dict[str, dict] = {}
    for path in sorted(FACTS.glob("*.json")):
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise StatementDriftError(f"unreadable fact {path.name}: {exc}") from exc
        if data.get("epistemic_status") not in SETTLED:
            continue
        formal = data.get("formal") or {}
        if formal.get("statement") is None:
            continue
        out[data["id"]] = {
            "language": formal.get("language"),
            "statement_sha256": digest(formal["statement"]),
        }
    if not out:
        raise StatementDriftError("no settled facts read — the gate has no subject")
    return out


def read_pins() -> tuple[dict[str, dict], dict[str, dict]]:
    if not PINS.is_file():
        raise StatementDriftError(f"missing manifest: {PINS.relative_to(ROOT)}")
    try:
        manifest = json.loads(PINS.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise StatementDriftError(f"unreadable manifest: {exc}") from exc
    pins = manifest.get("pins")
    if not isinstance(pins, list) or not pins:
        raise StatementDriftError("manifest carries no pins")
    by_id = {row["fact_id"]: row for row in pins}
    amendments = {}
    for row in manifest.get("amendments", []) or []:
        if not isinstance(row, dict):
            continue
        missing = [k for k in ("fact_id", "from_sha256", "to_sha256", "reason") if not row.get(k)]
        if missing:
            raise StatementDriftError(
                f"amendment for {row.get('fact_id')!r} lacks {missing} — "
                "an amendment must name both digests and a reason, or it is not a record"
            )
        amendments[row["fact_id"]] = row
    return by_id, amendments


def check(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quiet", action="store_true")
    parser.add_argument("--write", action="store_true", help="re-pin (adds new settled facts only)")
    args = parser.parse_args(argv)

    current = read_facts()
    pins, amendments = read_pins()

    violations: list[str] = []
    drifted = 0
    for fact_id, now in sorted(current.items()):
        pin = pins.get(fact_id)
        if pin is None:
            continue  # newly settled: pinned below, not drift
        if pin["statement_sha256"] == now["statement_sha256"]:
            continue
        drifted += 1
        amendment = amendments.get(fact_id)
        if amendment is None:
            violations.append(
                f"{fact_id}: formal.statement CHANGED "
                f"({pin.get('language')!r} -> {now['language']!r}) with no amendment. "
                "A settled fact's statement is the claim; editing it to match a new "
                "proof makes the claim unfalsifiable."
            )
        elif amendment["from_sha256"] != pin["statement_sha256"] or amendment[
            "to_sha256"
        ] != now["statement_sha256"]:
            violations.append(
                f"{fact_id}: amendment digests do not match the actual change — "
                "the amendment records a different edit than the one made"
            )

    retracted = sorted(set(pins) - set(current))
    for fact_id in retracted:
        if fact_id not in amendments:
            violations.append(
                f"{fact_id}: was settled and pinned, and is no longer settled or is absent. "
                "A retraction must be recorded, not silent."
            )

    if args.write:
        manifest = json.loads(PINS.read_text(encoding="utf-8"))
        manifest["pins"] = [
            {"fact_id": k, "language": v["language"], "statement_sha256": v["statement_sha256"]}
            for k, v in sorted(current.items())
        ]
        PINS.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
        if not args.quiet:
            print(f"SETTLED_FACT_STATEMENTS|rewrote {len(current)} pin(s)")
        return 0

    if not args.quiet:
        print(
            f"SETTLED_FACT_STATEMENTS|settled={len(current)}|pinned={len(pins)}"
            f"|drifted={drifted}|amendments={len(amendments)}|retracted={len(retracted)}"
        )
    for violation in violations:
        print(f"SETTLED_FACT_STATEMENTS|VIOLATION|{violation}", file=sys.stderr)
    if violations:
        print(f"SETTLED_FACT_STATEMENTS|FAIL|{len(violations)}", file=sys.stderr)
        return 1
    if not args.quiet:
        print("SETTLED_FACT_STATEMENTS|PASS")
    return 0


def main() -> int:
    try:
        return check()
    except StatementDriftError as exc:
        print(f"SETTLED_FACT_STATEMENTS|ERROR|{exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())

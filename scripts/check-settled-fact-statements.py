#!/usr/bin/env python3
"""A settled fact's statement is what the ledger CLAIMS. It must not drift, and
a fact must not be able to opt out of being watched by simply never being pinned.

WHAT THIS EXISTS TO STOP
------------------------

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

A full-history audit found the carrier change was the ONLY one among 140 settled
facts. Six other statement edits exist and all are benign: `66cb03eff` replaced
hand-written seed types with kernel-dumped ones (a correction toward truth), and
`1c33d3405` was the `Real` -> `AxReal` rename. So the rule here is not "never
edit" — legitimate corrections happen — it is "an edit must be a deliberate,
recorded act rather than a side effect".

S1 — WHY THIS GATE GREW (ADR-0752)
----------------------------------

S0's safety-matrix census (ADR-0746) measured `exact_statement` at 142 of 2117
proved facts. This gate was the reason: it read absence from the manifest as
"newly settled", never as a gap, so 1,976 settled facts could have their
statement rewritten and the gate would print `drifted=0` and exit 0. That is the
repository's signature defect — a checker that cannot fail — sitting on its own
statement-integrity check.

Four things changed.

**1. Absence is a violation, ratcheted.** `coverage_floor.max_unpinned_settled`
bounds how many settled facts may lack a pin. It starts at the coverage actually
achieved, so it never demands work that has not already been done; and the floor
must be TIGHT — slack is itself a violation telling you to run `--write`. That
is what makes loosening self-reverting: raising the allowance to sneak an
unpinned fact past makes the gate fail on the following run, because the actual
count is below the raised allowance. A monotone floor you can edit is not a
ratchet; a floor the gate re-derives is.

**2. The reader-facing statement is pinned too.** S1's exit is about statement
IDENTITY, and a native fact makes two claims: `formal.statement` is the
canonical kernel rendering, and the top-level `statement` is what a human reads.
Pinning only the first lets the prose be rewritten to describe a different
theorem while the formal side sits still — the same unfalsifiability, aimed at
the only field most readers ever see.

**3. A fact may not be silently repointed at another declaration.**
`formal.kernel_theorem` names the admitted declaration. Changing it changes
which theorem the fact is about, which is a bigger edit than changing the
statement text, and nothing watched it.

**4. `--write` can no longer launder drift.** It used to rewrite `pins` from
current state unconditionally, so anyone who ran it after a drift re-pinned the
damage and the gate went green. It now refuses to touch a pin whose digests
moved without an amendment, and when an amendment does license the change it
preserves the superseded digests in `history` — the roadmap's "preserve previous
statements when correcting a row".

There is also a structural bind that needs no pin at all: a `lean4` statement
rendered by `render_lean` opens `theorem <name> :`, and that name must be the
fact's `kernel_theorem`. It catches a statement replaced by a *different*
theorem's rendering, which is the sharpest form of statement error and the one a
content hash cannot describe (a hash says "changed", this says "changed into
something that is about another declaration").

MECHANISM
---------

`artifacts/ontology/settled-fact-statement-pins.json` holds, per settled fact,
the SHA-256 of `formal.statement`, the SHA-256 of the reader-facing `statement`,
and the `kernel_theorem` it names. A change to any of the three fails unless an
`amendments` row names the fact, both digests, and a reason.

FAIL-CLOSED. An unreadable or empty manifest, or one with no `coverage_floor`,
is an error rather than a quiet pass: a guard whose subject has vanished reports
the same "no violations" as one that works, and this repository has shipped that
exact defect (40 of 162 checker runs exiting 0 on completion alone).

Exit 0 clean, 1 on any violation, 2 on input the gate cannot read.

Controls: `scripts/tests/test_settled_fact_statements.py`, one test per guard,
each mutation-verified to die alone.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
FACTS = ROOT / "artifacts/facts"
PINS = ROOT / "artifacts/ontology/settled-fact-statement-pins.json"
SETTLED = {"proved", "computed"}

# A `render_lean` dump opens with a declaration keyword and the declaration's
# own name. Bare-type statements (no header) exist and are legitimate; they are
# exempt from the name check and counted under `max_header_exempt` so a new one
# cannot appear quietly.
HEADER = re.compile(r"^\s*(theorem|def|axiom|opaque|abbrev|inductive)\s+(\S+)\s*:")

# How many offending ids a violation line names before truncating. A violation
# that prints 2,000 ids is a violation nobody reads.
NAMED = 8

FLOOR_KEYS = ("max_unpinned_settled", "min_identity_bound", "max_header_exempt")


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
        statement = formal["statement"]
        header = HEADER.match(statement) if isinstance(statement, str) else None
        out[data["id"]] = {
            "language": formal.get("language"),
            "statement_sha256": digest(statement),
            "prose_sha256": digest(data.get("statement")),
            "kernel_theorem": formal.get("kernel_theorem"),
            "header_name": header.group(2) if header else None,
        }
    if not out:
        raise StatementDriftError("no settled facts read — the gate has no subject")
    return out


def read_pins() -> tuple[dict[str, dict], dict[str, dict], dict[str, int]]:
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

    floor = manifest.get("coverage_floor")
    if not isinstance(floor, dict):
        raise StatementDriftError(
            "manifest carries no `coverage_floor`. Absence of a pin is the defect "
            "this gate was rebuilt to catch; without a floor it cannot fail on it."
        )
    floors: dict[str, int] = {}
    for key in FLOOR_KEYS:
        value = floor.get(key)
        if not isinstance(value, int) or isinstance(value, bool) or value < 0:
            raise StatementDriftError(
                f"coverage_floor.{key} must be a non-negative integer, got {value!r}"
            )
        floors[key] = value

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
    return by_id, amendments, floors


def _sample(ids: list[str]) -> str:
    shown = ", ".join(ids[:NAMED])
    return shown if len(ids) <= NAMED else f"{shown}, … (+{len(ids) - NAMED} more)"


def evaluate(
    current: dict[str, dict], pins: dict[str, dict], amendments: dict[str, dict], floors: dict[str, int]
) -> tuple[list[str], dict[str, int]]:
    """Return (violations, counters). Pure, so `--write` can consult it."""
    violations: list[str] = []
    drifted = 0
    unpinned: list[str] = []
    identity_bound = 0
    header_exempt: list[str] = []

    for fact_id, now in sorted(current.items()):
        pin = pins.get(fact_id)
        amendment = amendments.get(fact_id)

        # --- structural bind: the rendered header names this declaration ----
        if now["language"] == "lean4" and now["kernel_theorem"]:
            if now["header_name"] is None:
                header_exempt.append(fact_id)
            elif now["header_name"] != now["kernel_theorem"]:
                violations.append(
                    f"{fact_id}: formal.statement is headed "
                    f"`{now['header_name']}` but the fact claims kernel_theorem "
                    f"`{now['kernel_theorem']}` — the statement is a rendering of a "
                    "DIFFERENT declaration than the one this fact is about."
                )

        if pin is None:
            unpinned.append(fact_id)
            continue

        if (
            pin.get("kernel_theorem")
            and pin.get("prose_sha256")
            and pin.get("statement_sha256")
            and pin.get("kernel_theorem") == now["kernel_theorem"]
        ):
            identity_bound += 1

        # --- guard: the formal statement must not change silently -----------
        if pin["statement_sha256"] != now["statement_sha256"]:
            drifted += 1
            if amendment is None:
                violations.append(
                    f"{fact_id}: formal.statement CHANGED "
                    f"({pin.get('language')!r} -> {now['language']!r}) with no amendment. "
                    "A settled fact's statement is the claim; editing it to match a new "
                    "proof makes the claim unfalsifiable."
                )
            elif (
                amendment["from_sha256"] != pin["statement_sha256"]
                or amendment["to_sha256"] != now["statement_sha256"]
            ):
                violations.append(
                    f"{fact_id}: amendment digests do not match the actual change — "
                    "the amendment records a different edit than the one made"
                )

        # --- guard: the reader-facing statement must not change silently ----
        pinned_prose = pin.get("prose_sha256")
        if pinned_prose is not None and pinned_prose != now["prose_sha256"]:
            if (
                amendment is None
                or amendment.get("from_prose_sha256") != pinned_prose
                or amendment.get("to_prose_sha256") != now["prose_sha256"]
            ):
                violations.append(
                    f"{fact_id}: the reader-facing `statement` CHANGED with no matching "
                    "amendment. It is the only field most readers see; rewriting it to "
                    "describe a different theorem is the same unfalsifiability as "
                    "rewriting the formal side."
                )

        # --- guard: the fact must not be repointed at another declaration ---
        pinned_theorem = pin.get("kernel_theorem")
        if pinned_theorem is not None and pinned_theorem != now["kernel_theorem"]:
            if amendment is None or amendment.get("to_kernel_theorem") != now["kernel_theorem"]:
                violations.append(
                    f"{fact_id}: formal.kernel_theorem moved "
                    f"{pinned_theorem!r} -> {now['kernel_theorem']!r} with no matching "
                    "amendment. Which declaration a fact is about is a larger claim "
                    "than how its statement is spelled."
                )

    retracted = sorted(set(pins) - set(current))
    for fact_id in retracted:
        if fact_id not in amendments:
            violations.append(
                f"{fact_id}: was settled and pinned, and is no longer settled or is absent. "
                "A retraction must be recorded, not silent."
            )

    # --- guard: absence is a gap, not a shrug -------------------------------
    if len(unpinned) > floors["max_unpinned_settled"]:
        violations.append(
            f"{len(unpinned)} settled fact(s) carry NO statement pin, above the "
            f"allowance of {floors['max_unpinned_settled']}. An unpinned statement can be "
            "rewritten and nothing fails. Run `--write` to pin them: "
            f"{_sample(unpinned)}"
        )
    elif len(unpinned) < floors["max_unpinned_settled"]:
        violations.append(
            f"coverage_floor.max_unpinned_settled is SLACK: allows {floors['max_unpinned_settled']}, "
            f"actual {len(unpinned)}. A ratchet that permits more than has been achieved is "
            "how a loosened floor survives; run `--write` to tighten it."
        )

    if identity_bound < floors["min_identity_bound"]:
        violations.append(
            f"statement identity bindings fell to {identity_bound}, below the floor of "
            f"{floors['min_identity_bound']}. A binding ties one fact's kernel rendering, "
            "reader-facing statement and named declaration together; losing one un-binds a "
            "claim that was bound."
        )
    elif identity_bound > floors["min_identity_bound"]:
        violations.append(
            f"coverage_floor.min_identity_bound is SLACK: floor {floors['min_identity_bound']}, "
            f"actual {identity_bound}. Run `--write` to record the progress, or the next "
            "regression to this level will pass."
        )

    if len(header_exempt) > floors["max_header_exempt"]:
        violations.append(
            f"{len(header_exempt)} lean4 fact(s) name a kernel_theorem but carry a "
            f"statement with no `theorem <name> :` header, above the allowance of "
            f"{floors['max_header_exempt']}. A headerless statement cannot be checked "
            f"against the declaration it claims: {_sample(header_exempt)}"
        )
    elif len(header_exempt) < floors["max_header_exempt"]:
        violations.append(
            f"coverage_floor.max_header_exempt is SLACK: allows {floors['max_header_exempt']}, "
            f"actual {len(header_exempt)}. Run `--write` to tighten it."
        )

    counters = {
        "settled": len(current),
        "pinned": len(pins),
        "unpinned": len(unpinned),
        "identity_bound": identity_bound,
        "header_exempt": len(header_exempt),
        "drifted": drifted,
        "amendments": len(amendments),
        "retracted": len(retracted),
    }
    return violations, counters


def rewrite(current: dict[str, dict], pins: dict[str, dict], amendments: dict[str, dict]) -> int:
    """Add pins for unpinned settled facts; carry amended ones forward with history.

    Refuses to move a pin whose digests changed without an amendment. That is
    the anti-laundering guard: `--write` used to rebuild `pins` from current
    state unconditionally, so running it after a drift re-pinned the damage.
    """
    blocked = []
    for fact_id, now in sorted(current.items()):
        pin = pins.get(fact_id)
        if pin is None:
            continue
        changed = (
            pin["statement_sha256"] != now["statement_sha256"]
            or (pin.get("prose_sha256") is not None and pin["prose_sha256"] != now["prose_sha256"])
            or (
                pin.get("kernel_theorem") is not None
                and pin["kernel_theorem"] != now["kernel_theorem"]
            )
        )
        if changed and fact_id not in amendments:
            blocked.append(fact_id)
    if blocked:
        print(
            f"SETTLED_FACT_STATEMENTS|REFUSED|--write would re-pin {len(blocked)} changed "
            f"statement(s) with no amendment, which would launder the drift this gate "
            f"exists to catch: {_sample(blocked)}",
            file=sys.stderr,
        )
        return 1

    manifest = json.loads(PINS.read_text(encoding="utf-8"))
    rows = []
    for fact_id, now in sorted(current.items()):
        old = pins.get(fact_id)
        history = list(old.get("history", [])) if old else []
        if old is not None and (
            old["statement_sha256"] != now["statement_sha256"]
            or old.get("prose_sha256") != now["prose_sha256"]
            or old.get("kernel_theorem") != now["kernel_theorem"]
        ):
            superseded = {k: v for k, v in old.items() if k not in ("fact_id", "history")}
            if superseded not in history:
                history.append(superseded)
        row = {
            "fact_id": fact_id,
            "language": now["language"],
            "statement_sha256": now["statement_sha256"],
            "prose_sha256": now["prose_sha256"],
        }
        if now["kernel_theorem"]:
            row["kernel_theorem"] = now["kernel_theorem"]
        if history:
            row["history"] = history
        rows.append(row)

    manifest["schema_version"] = 2
    manifest["pins"] = rows
    pinned_ids = {r["fact_id"] for r in rows}
    unpinned = [f for f in current if f not in pinned_ids]
    identity = sum(
        1 for r in rows if r.get("kernel_theorem") and r.get("prose_sha256") and r.get("statement_sha256")
    )
    header_exempt = sum(
        1
        for f, now in current.items()
        if now["language"] == "lean4" and now["kernel_theorem"] and now["header_name"] is None
    )
    old_floor = manifest.get("coverage_floor") or {}
    manifest["coverage_floor"] = {
        # Ratchets only tighten. `min` on an allowance, `max` on a requirement.
        "max_unpinned_settled": min(
            old_floor.get("max_unpinned_settled", len(unpinned)), len(unpinned)
        ),
        "min_identity_bound": max(old_floor.get("min_identity_bound", identity), identity),
        "max_header_exempt": min(old_floor.get("max_header_exempt", header_exempt), header_exempt),
    }
    PINS.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(
        f"SETTLED_FACT_STATEMENTS|wrote {len(rows)} pin(s)"
        f"|unpinned={len(unpinned)}|identity_bound={identity}|header_exempt={header_exempt}"
    )
    return 0


def check(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quiet", action="store_true")
    parser.add_argument(
        "--write",
        action="store_true",
        help="pin newly settled facts and tighten the ratchet; refuses to re-pin "
        "an unamended change",
    )
    args = parser.parse_args(argv)

    current = read_facts()
    pins, amendments, floors = read_pins()

    if args.write:
        return rewrite(current, pins, amendments)

    violations, counters = evaluate(current, pins, amendments, floors)

    if not args.quiet:
        print(
            "SETTLED_FACT_STATEMENTS|"
            + "|".join(f"{k}={v}" for k, v in counters.items())
            + "|floor_unpinned=%d|floor_identity=%d|floor_header_exempt=%d"
            % (
                floors["max_unpinned_settled"],
                floors["min_identity_bound"],
                floors["max_header_exempt"],
            )
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

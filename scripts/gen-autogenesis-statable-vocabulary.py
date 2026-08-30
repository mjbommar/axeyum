#!/usr/bin/env python3
"""Derive `mathlib-statable-vocabulary-v1.json` instead of maintaining it.

`check-dispatchable-frontier.py`'s S2/S3/S4 constrain that artifact so tightly
that NOTHING in it is a free choice. Measured 2026-08-30 against the committed
file, before this generator existed:

    bridge == (union of settled row constants) - env      162/162 rows, exact
    row constants == Lean.Expr.const of the pinned type_repr        162/162

S2 forces `bridge` into `witnessed - env` from below (a bridge entry must be
witnessed) and S3 forces it from above (a settled row's constants must all be
admissible). Together they pin `bridge` to a single value. S4 pins the row SET
to the fact ledger in both directions. The only field neither gate touches is a
row's `constants` list -- which is exactly the field that came from the pinned
Mathlib inventory and cannot be re-derived from anything in the tree.

So the artifact was hand-maintained for a value that is entirely determined,
and it drifted the first time a batch of mirrors closed: 9 settled `Nat.clog_*`
/ `Nat.log_*` mirrors had no row at all, and S4 fired. That is the flywheel
outrunning its own bookkeeping, and prose asking people to keep a derived file
in sync is the thing this repository has repeatedly measured as failing.

WHAT THIS DOES *NOT* DO. It does not widen the screen. ADR-0619 records that
the statable pool grows by DECLARING kernel constants, not by relaxing the
admissibility test, and the derivation here is unchanged from the one the
committed artifact already documented: a constant enters `bridge` only because
a mirror stated with it has ALREADY been closed in the ledger. Regenerating
after a close admits the constants of a proposition we proved; it never admits
a constant on the strength of an assertion.

THE CACHE, AND WHY THE ROUTINE REPAIR NEEDS NO NAS. The `constants` come from a
39 MB NDJSON on `/nas3` that is not mounted on every fleet host. A generator
that needed it on every run would make the routine repair -- "a mirror closed,
regenerate" -- impossible on most machines, and the repair not being runnable
is how the file drifted in the first place. So the per-proposition constants
for every CATALOGUED proposition (settled and open alike) are snapshotted into
`mathlib-statement-constants-v1.json`, digest-bound to the pinned inventory.
Closing a mirror then needs no NAS: its constants were already derived. Only a
genuinely NEW catalogued proposition -- a nursery refill draw -- needs
`--refresh-cache`, and `--write` FAILS naming that command rather than emitting
a row it could not derive.

    --refresh-cache   needs /nas3     rebuild the constants cache
    --write           tree only       rebuild the vocabulary from the cache
    --check (default) tree only       verify the committed artifact

WHAT `--check` GUARDS, AND WHAT IT DELIBERATELY LEAVES TO S4. It does not
re-implement the frontier gate. S4 already fails on drift between the row set
and the ledger, in both directions, and duplicating it here would buy nothing
but a second thing to keep in sync. `--check` covers what no existing gate
looks at:

  V1  the rows must hash to the recorded `row_digest`. This is what makes the
      generator the only way a row gets in. A hand-appended row -- correct or
      fabricated -- passes S2, S3 and S4 whenever its constants are redundantly
      witnessed by another row, because no gate compares a row's constants
      against the source. V1 fires on the edit itself.
  V2  the `coverage` block must agree with the artifact's own contents. It was
      STALE on the committed file when this was written (`open_propositions`
      read 40 against a real 31) and nothing noticed, because no gate read it.
  V3  the pinned source (mathlib commit, tag, inventory sha256) must equal the
      pins this generator compiles in. A re-pin that moves the inventory
      without regenerating would leave constants derived from a different
      Mathlib behind a pin claiming otherwise.
  V4  `environment_snapshot` must name the file the frontier gate actually
      reads. A dangling pointer here would describe a screen nobody runs.

V1 is honest about its own limit: it binds the rows to what `--write` produced,
and someone who recomputes the digest by hand can defeat it. It catches
carelessness, not forgery, and carelessness is the measured failure mode. The
binding to Mathlib itself is `--refresh-cache` on a NAS host, and that is the
only place the inventory's authority enters.

Usage:
    python3 scripts/gen-autogenesis-statable-vocabulary.py
    python3 scripts/gen-autogenesis-statable-vocabulary.py --write
    python3 scripts/gen-autogenesis-statable-vocabulary.py --refresh-cache

Exit status:
    0  the committed artifact is exactly its derivation
    1  a guard fired (V1-V4), or --write/--refresh-cache changed a file
    2  an input could not be read
"""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import re
import sys
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
AUTOGENESIS = ROOT / "artifacts" / "autogenesis"
VOCABULARY = AUTOGENESIS / "mathlib-statable-vocabulary-v1.json"
CACHE = AUTOGENESIS / "mathlib-statement-constants-v1.json"
CATALOG = AUTOGENESIS / "mathlib-nat-int-fact-catalog-v1.json"
ENV_SNAPSHOT = AUTOGENESIS / "kernel-environment-snapshot-v1.json"
FACTS = ROOT / "artifacts" / "facts"

# The same pins `gen-autogenesis-nursery-refill.py` carries. Note the sibling
# `-v1.ndjson` has the SAME record count and is NOT the pinned artifact, so the
# count is not a substitute for the digest.
INVENTORY = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/sources/"
    "mathlib-v4.30.0-nat-int-statement-inventory-v2.ndjson"
)
INVENTORY_SHA256 = "4285e551680abf3b0cafb11709015f04b3aef3eb05ce23af2392b12cec31aecc"
SOURCE_COMMIT = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
SOURCE_TAG = "v4.30.0"

# `epistemic_status` values that count as CLOSED here. Identical to the
# frontier gate's, and deliberately not imported from it: that module is a
# gate, and a generator importing its constants would make a change to either
# silently change the other.
SETTLED = {"proved", "refuted", "computed"}

CONST_RE = re.compile(r"Lean\.Expr\.const\s+`+([^\s\)\[]+)")

KEYED_BY = (
    "Mathlib source_name, NOT fact_id. Naming a fact id here would put held-out"
    " ids in a non-population artifact -- check-autogenesis-holdout-isolation.py"
    " caught exactly that on the first draft of this file, 35 references. The"
    " checker resolves source_name to a fact through the catalog, which IS a"
    " population file and may name them."
)
DERIVATION = (
    "bridge = {Lean constants in the pinned type_repr of every SETTLED ml430"
    " mirror} \\ kernel-environment-snapshot-v1.declarations. Derived, never"
    " asserted: an entry exists only because a mirror stated with that constant"
    " has already been closed here. Regenerate with"
    " scripts/gen-autogenesis-statable-vocabulary.py --write; the per-row"
    " constants come from mathlib-statement-constants-v1.json, which is itself"
    " derived from the pinned inventory by --refresh-cache."
)


def die(message: str) -> None:
    print(f"ERROR: {message}", file=sys.stderr)
    raise SystemExit(2)


def read_json(path: pathlib.Path) -> Any:
    if not path.is_file():
        die(f"no input at {path}")
    try:
        return json.loads(path.read_text())
    except json.JSONDecodeError as exc:
        die(f"{path}: {exc}")


def load_catalog() -> dict[str, str]:
    doc = read_json(CATALOG)
    rows = doc.get("facts")
    if not isinstance(rows, list):
        die(f"{CATALOG}: no `facts` list")
    return {r["source_name"]: r["fact_id"] for r in rows
            if isinstance(r, dict) and r.get("kind") == "external-source"}


def load_statuses() -> dict[str, str]:
    if not FACTS.is_dir():
        die(f"no fact directory at {FACTS}")
    out: dict[str, str] = {}
    for path in sorted(FACTS.glob("*.json")):
        try:
            fact = json.loads(path.read_text())
        except json.JSONDecodeError as exc:
            die(f"{path}: {exc}")
        ident = fact.get("id")
        if isinstance(ident, str):
            out[ident] = fact.get("epistemic_status")
    if not out:
        die(f"{FACTS} contains no facts")
    return out


def row_digest(rows: list[dict[str, Any]]) -> str:
    """Bind the row set AND every row's constants to one value.

    Canonical: rows sorted by source_name, constants sorted within a row. So a
    reordering is not a change and a re-derivation on another host reproduces
    it byte for byte.
    """
    payload = [[r["source_name"], sorted(r["constants"])]
               for r in sorted(rows, key=lambda r: r["source_name"])]
    blob = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(blob.encode()).hexdigest()


def refresh_cache() -> int:
    if not INVENTORY.is_file():
        print(f"ERROR: the pinned statement inventory is not readable at "
              f"{INVENTORY}. --refresh-cache needs it; --write and --check do "
              f"not, which is the whole point of the cache.", file=sys.stderr)
        return 2
    raw = INVENTORY.read_bytes()
    actual = hashlib.sha256(raw).hexdigest()
    if actual != INVENTORY_SHA256:
        print(f"ERROR: {INVENTORY} is sha256 {actual}, expected "
              f"{INVENTORY_SHA256}.", file=sys.stderr)
        return 2

    catalog = load_catalog()
    want = set(catalog)
    constants: dict[str, list[str]] = {}
    for line in raw.decode().splitlines():
        record = json.loads(line)
        name = record.get("name")
        if name in want:
            constants[name] = sorted(set(CONST_RE.findall(record.get("type_repr") or "")))

    absent = sorted(want - set(constants))
    if absent:
        print(f"ERROR: {len(absent)} catalogued proposition(s) are not in the "
              f"pinned inventory ({', '.join(absent[:3])}). The catalog and the"
              f" pin disagree; do not paper over it here.", file=sys.stderr)
        return 2

    doc = {
        "constants": dict(sorted(constants.items())),
        "derivation": (
            "Lean.Expr.const occurrences in the pinned type_repr of every"
            " CATALOGUED ml430 proposition, settled and open alike. Cached so"
            " that regenerating the statable vocabulary after a mirror closes"
            " needs no /nas3."
        ),
        "kind": "axeyum-autogenesis-statement-constants",
        "schema_version": 1,
        "source": {
            "mathlib_commit": SOURCE_COMMIT,
            "mathlib_tag": SOURCE_TAG,
            "statement_inventory_sha256": INVENTORY_SHA256,
        },
    }
    return emit(CACHE, doc)


def build(cache: dict[str, Any]) -> dict[str, Any]:
    """The whole artifact, from the cache + the ledger + the env snapshot."""
    catalog = load_catalog()
    statuses = load_statuses()
    snapshot = read_json(ENV_SNAPSHOT)
    declarations = snapshot.get("declarations")
    if not isinstance(declarations, list):
        die(f"{ENV_SNAPSHOT}: `declarations` must be a list")
    env = set(declarations)

    pool = cache.get("constants")
    if not isinstance(pool, dict):
        die(f"{CACHE}: `constants` must be an object")

    settled_names = sorted(n for n, ident in catalog.items()
                           if statuses.get(ident) in SETTLED)
    uncached = [n for n in settled_names if n not in pool]
    if uncached:
        print(f"ERROR: {len(uncached)} settled proposition(s) have no cached "
              f"constants ({', '.join(uncached[:3])}). Run --refresh-cache on a "
              f"host with {INVENTORY.parent}; a row is never emitted with "
              f"constants this generator could not derive.", file=sys.stderr)
        raise SystemExit(2)

    rows = [{"constants": sorted(pool[n]), "source_name": n} for n in settled_names]
    witnessed = {c for r in rows for c in r["constants"]}
    bridge = sorted(witnessed - env)

    return {
        "bridge": bridge,
        "coverage": {
            "bridge_constants": len(bridge),
            "catalogued_propositions": len(catalog),
            "distinct_constants": len(witnessed),
            "open_propositions": len(catalog) - len(settled_names),
            "settled_propositions": len(settled_names),
        },
        "derivation": DERIVATION,
        "environment_snapshot": str(ENV_SNAPSHOT.relative_to(ROOT)),
        "keyed_by": KEYED_BY,
        "kind": "axeyum-autogenesis-statable-vocabulary",
        "row_digest": row_digest(rows),
        "schema_version": 1,
        "settled": rows,
        "source": {
            "mathlib_commit": SOURCE_COMMIT,
            "mathlib_tag": SOURCE_TAG,
            "statement_inventory_sha256": INVENTORY_SHA256,
        },
    }


def render(doc: dict[str, Any]) -> str:
    return json.dumps(doc, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def emit(path: pathlib.Path, doc: dict[str, Any]) -> int:
    text = render(doc)
    if path.is_file() and path.read_text() == text:
        print(f"UNCHANGED {path.relative_to(ROOT)}")
        return 0
    path.write_text(text)
    print(f"WROTE {path.relative_to(ROOT)}")
    return 1


def check() -> int:
    """V1-V4 over the committed artifact. Returns the count of FAIL lines."""
    doc = read_json(VOCABULARY)
    fails: list[str] = []

    rows = doc.get("settled")
    if not isinstance(rows, list) or not rows:
        die(f"{VOCABULARY}: `settled` must be a non-empty list")
    for row in rows:
        if not isinstance(row, dict) or not isinstance(row.get("constants"), list) \
                or not isinstance(row.get("source_name"), str):
            die(f"{VOCABULARY}: a settled row is not "
                f"{{source_name, constants}}")

    # V1 -- the rows must be what the generator produced. No other gate compares
    # a row's constants against anything, so a hand-appended row with invented
    # constants is invisible to S2/S3/S4 whenever another row witnesses them.
    recorded = doc.get("row_digest")
    actual = row_digest(rows)
    if recorded != actual:
        fails.append(
            f"V1 hand-edited-vocabulary: row_digest is {recorded!r} but the "
            f"{len(rows)} committed rows hash to {actual!r}. Rows are not "
            f"hand-written: run scripts/gen-autogenesis-statable-vocabulary.py "
            f"--write.")

    # V2 -- the coverage block is prose nobody re-derives. It was stale on the
    # committed file the day this was written and no gate read it.
    catalog = load_catalog()
    statuses = load_statuses()
    settled_names = {n for n, ident in catalog.items() if statuses.get(ident) in SETTLED}
    witnessed = {c for r in rows for c in r["constants"]}
    bridge = doc.get("bridge")
    if not isinstance(bridge, list):
        die(f"{VOCABULARY}: `bridge` must be a list")
    expected_coverage = {
        "bridge_constants": len(bridge),
        "catalogued_propositions": len(catalog),
        "distinct_constants": len(witnessed),
        "open_propositions": len(catalog) - len(settled_names),
        "settled_propositions": len(settled_names),
    }
    coverage = doc.get("coverage")
    if coverage != expected_coverage:
        differing = sorted(k for k in expected_coverage
                           if not isinstance(coverage, dict)
                           or coverage.get(k) != expected_coverage[k])
        fails.append(
            f"V2 stale-coverage-block: {differing} disagree with the "
            f"artifact's own contents and the ledger (recorded {coverage!r}, "
            f"derived {expected_coverage!r}).")

    # V3 -- the pin. Constants derived from one Mathlib behind a pin naming
    # another is the failure the whole external-source discipline exists to stop.
    source = doc.get("source")
    expected_source = {
        "mathlib_commit": SOURCE_COMMIT,
        "mathlib_tag": SOURCE_TAG,
        "statement_inventory_sha256": INVENTORY_SHA256,
    }
    if source != expected_source:
        fails.append(
            f"V3 source-pin-drift: the artifact pins {source!r}, this generator"
            f" derives against {expected_source!r}. One of them moved without "
            f"the other.")

    # V4 -- the artifact names the environment snapshot the screen is applied
    # against. A dangling pointer describes a screen nobody runs.
    # The absolute-path case is why this is not a one-liner: `ROOT / "/etc/foo"`
    # DISCARDS the left operand in pathlib, so a bare `(ROOT / named).is_file()`
    # cheerfully resolves outside the repository and passes. The controls suite
    # caught exactly that in this guard's first draft.
    named = doc.get("environment_snapshot")
    resolved = None
    if isinstance(named, str) and named:
        candidate = pathlib.Path(named)
        if not candidate.is_absolute():
            candidate = (ROOT / candidate).resolve()
            if candidate.is_relative_to(ROOT) and candidate.is_file():
                resolved = candidate
    if resolved is None:
        fails.append(
            f"V4 dangling-environment-snapshot: environment_snapshot is "
            f"{named!r}, which is not a readable file at a relative path under "
            f"the repository root. The screen's authority is that snapshot.")

    for line in fails:
        print(f"FAIL: {line}")
    if not fails:
        print(f"AUTOGENESIS_STATABLE_VOCABULARY|rows={len(rows)}"
              f"|bridge={len(bridge)}|cached={len(read_json(CACHE).get('constants', {}))}"
              f"|verdict=PASS")
    return len(fails)


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    mode = ap.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true",
                      help="rebuild the vocabulary from the cache (no /nas3)")
    mode.add_argument("--refresh-cache", action="store_true",
                      help="rebuild the constants cache from the pinned "
                           "inventory (needs /nas3)")
    args = ap.parse_args(argv)

    if args.refresh_cache:
        return refresh_cache()
    if args.write:
        return emit(VOCABULARY, build(read_json(CACHE)))
    return 1 if check() else 0


if __name__ == "__main__":
    sys.exit(main())

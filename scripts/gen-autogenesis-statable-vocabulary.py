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

# --- bridge provenance: WHY each constant was promoted --------------------
#
# The bridge's inference is: a mirror mentioning C was closed here, so C is
# expressible here. That fails whenever the mirror was closed by ELIDING C --
# restating the proposition in an equivalent form C never appears in.
#
# Measured instance, 2026-08-30. `F:ml430-nat-log-antitone-left` pins
#
#     forall {n : N}, AntitoneOn (fun b => Nat.log b n) (Set.Ioi 1)
#
# and closing it promoted `AntitoneOn` and `Set.Ioi`. Our theorem renders as
# `Le x1 x2 -> Lt 1 x1 -> Lt 1 x2 -> Le (log x2 x0) (log x1 x0)` -- no
# `AntitoneOn`, no `Set.Ioi`, no `Set` type at all. What that closure
# established is that THIS proposition has an equivalent pointwise form. It did
# not establish that `Set.Ioi` is expressible here.
#
# THE FIX IS A LABEL, NOT A DELETION, AND THE MEASUREMENT IS WHY.
# `--check`'s candidate sibling -- promote only what the rendered kernel type
# mentions -- was tested and REFUTED: Mathlib's pinned `type_repr` is mostly
# ELABORATION constants (`OfNat.ofNat` 73 witnesses, `instOfNatNat` 61,
# `instHAdd`/`HAdd.hAdd` 32) that can never appear in a kernel rendering by
# name, because our kernel has no typeclasses. Applying it takes the statable
# open pool from 24 to 0. Dropping only the constants this classifier calls
# `elided` takes it from 24 to 22. So the defect is real and SMALL, and
# deleting the bridge would be a far larger error than the one being fixed.
#
# The four classes, and what each one licenses:
#
#   elaboration  a Lean instance (`instHAdd`, `Nat.instDvd`) or a class
#                projection (`HAdd.hAdd`, `LE.le`). Notation, not vocabulary:
#                it carries no mathematical content of its own and CANNOT
#                appear in a kernel rendering, so the rendered-type test is
#                meaningless for it and is not applied. Both signals are Lean's
#                own mechanical naming conventions, not a hand-kept list.
#   expressed    some settled witness's rendered kernel type does mention it.
#                The bridge inference holds outright.
#   elided       every settled witness that HAS a rendered kernel type fails to
#                mention it. Promotion rests on an equivalent restatement.
#   unrendered   no settled witness carries `formal.kernel_statement` at all,
#                so the ledger cannot say. Measured 2026-08-30: 139 of 174
#                settled mirrors have no rendering recorded, which is why this
#                class exists instead of being folded into `elided`. Calling an
#                unmeasured thing a defect is the same error in the other
#                direction.
#
# `elided` IS A PRECISION FLAG, NOT A DEFECT FLAG, and overselling it would be
# dishonest. `Monotone` is elided and perfectly safe -- it unfolds to a
# pointwise arithmetic statement over env vocabulary, which is exactly what the
# frontier gate's docstring already says about `Nat.fib_mono`. `Set.Ioi` is
# elided and thin, because it unfolds through a `Set` type we do not have. This
# classifier cannot tell those apart and does not claim to. What it buys is
# that the statable count can be quoted with the elision-backed portion
# separated out, the way the CAS substance gate publishes its four kinds
# instead of a flat total.
INSTANCE_RE = re.compile(r"^inst[A-Z]")


def is_elaboration(const: str) -> bool:
    """Lean instance or class projection -- notation, never kernel vocabulary.

    Two mechanical conventions, both Lean's own:
      * `mkInstanceName` prefixes `inst` (`instHAdd`, `Nat.instDvd`).
      * a class's projection is the class name decapitalized (`HAdd.hAdd`,
        `OfNat.ofNat`). All-caps class names decapitalize whole -- `LE.le`, not
        `LE.lE` -- so both spellings count. Without that second spelling `LE.le`
        and `LT.lt` misclassify, which is how this was caught.
    """
    head, _, last = const.rpartition(".")
    last = last or const
    if INSTANCE_RE.match(last):
        return True
    if not head:
        return False
    tail = head.rpartition(".")[2]
    return last in (tail[:1].lower() + tail[1:], tail.lower())


TOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_.']*")


def kernel_tokens(rendered: str) -> set[str]:
    """Names a rendered kernel type mentions, in Mathlib-ish spelling.

    `lean_pp` renders the naturals as `AxNat` -- the `Ax` is *axeyum*, a
    non-shadowing export root, NOT an axiomatization -- so `AxNat.log` here is
    `Nat.log` there. Both the qualified name and its last component are
    returned, because a mirror may render `Nat.Coprime` as bare `Coprime`.
    """
    out: set[str] = set()
    for token in TOKEN_RE.findall(rendered or ""):
        head, _, rest = token.partition(".")
        if head.startswith("Ax") and len(head) > 2 and head[2].isupper():
            head = head[2:]
        name = head + ("." + rest if rest else "")
        out.add(name)
        out.add(name.rsplit(".", 1)[-1])
    return out


def classify_bridge(bridge: list[str],
                    rows: list[dict[str, Any]],
                    renderings: dict[str, str]) -> dict[str, dict[str, Any]]:
    """Per-bridge-constant provenance. Pure function of its three inputs."""
    witness: dict[str, list[str]] = {c: [] for c in bridge}
    for row in rows:
        for const in row["constants"]:
            if const in witness:
                witness[const].append(row["source_name"])
    tokens = {name: kernel_tokens(text) for name, text in renderings.items() if text}

    out: dict[str, dict[str, Any]] = {}
    for const in sorted(bridge):
        names = witness[const]
        rendered = [n for n in names if n in tokens]
        if is_elaboration(const):
            kind = "elaboration"
        elif not rendered:
            kind = "unrendered"
        elif any(const in tokens[n] or const.rsplit(".", 1)[-1] in tokens[n]
                 for n in rendered):
            kind = "expressed"
        else:
            kind = "elided"
        out[const] = {"class": kind,
                      "rendered_witnesses": len(rendered),
                      "witnesses": len(names)}
    return out

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


def load_renderings() -> dict[str, str]:
    """fact id -> `formal.kernel_statement`, the rendered kernel type.

    This is our side of the bridge inference and the ledger already carries it,
    so no cargo run is needed. It is SPARSE -- 35 of 174 settled mirrors had one
    on 2026-08-30 -- which is exactly why `classify_bridge` has an `unrendered`
    class rather than treating silence as elision.
    """
    out: dict[str, str] = {}
    for path in sorted(FACTS.glob("*.json")):
        try:
            fact = json.loads(path.read_text())
        except json.JSONDecodeError as exc:
            die(f"{path}: {exc}")
        ident = fact.get("id")
        rendered = (fact.get("formal") or {}).get("kernel_statement")
        if isinstance(ident, str) and isinstance(rendered, str) and rendered:
            out[ident] = rendered
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


BRIDGE_CLASSES = ("elaboration", "elided", "expressed", "unrendered")


def provenance_coverage(provenance: dict[str, dict[str, Any]]) -> dict[str, int]:
    """The tier counts, published so the statable pool can be quoted both ways."""
    return {f"bridge_{kind}":
            sum(1 for v in provenance.values() if v["class"] == kind)
            for kind in BRIDGE_CLASSES}


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

    renderings_by_id = load_renderings()
    provenance = classify_bridge(
        bridge, rows,
        {n: renderings_by_id[catalog[n]] for n in settled_names
         if catalog[n] in renderings_by_id})

    return {
        "bridge": bridge,
        "bridge_provenance": provenance,
        "coverage": {
            **provenance_coverage(provenance),
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
    # V5 -- the provenance block. It is the only thing separating "this
    # constant is expressible here" from "a mirror mentioning it was closed by
    # restating it without it", and no other gate derives it.
    renderings_by_id = load_renderings()
    derived_provenance = classify_bridge(
        bridge, rows,
        {n: renderings_by_id[catalog[n]] for n in settled_names
         if n in catalog and catalog[n] in renderings_by_id})
    recorded_provenance = doc.get("bridge_provenance")
    if recorded_provenance != derived_provenance:
        if not isinstance(recorded_provenance, dict):
            detail = f"it is {type(recorded_provenance).__name__}, not an object"
        else:
            keys = (set(derived_provenance) ^ set(recorded_provenance))
            moved = sorted(c for c in set(derived_provenance) & set(recorded_provenance)
                           if recorded_provenance[c] != derived_provenance[c])
            detail = (f"{len(keys)} constant(s) present on one side only "
                      f"({sorted(keys)[:4]}), {len(moved)} reclassified "
                      f"({moved[:4]})")
        fails.append(
            f"V5 bridge-provenance-drift: `bridge_provenance` is not its "
            f"derivation -- {detail}. It records WHY each bridge constant was "
            f"promoted, and a hand-edit here would let an elision-backed "
            f"constant be quoted as expressed. Run "
            f"scripts/gen-autogenesis-statable-vocabulary.py --write.")

    expected_coverage = {
        **provenance_coverage(derived_provenance),
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
    # `is_relative_to` is doing ALL the work here and the `is_absolute()` test
    # that stood beside it has been removed, because mutation testing showed no
    # case could kill it: `ROOT / "/etc/hostname"` DISCARDS the left operand in
    # pathlib, so the joined path is `/etc/hostname`, and containment already
    # rejects it. The naive form this replaced -- a bare
    # `(ROOT / named).is_file()` -- returned PASS for exactly that artifact.
    named = doc.get("environment_snapshot")
    resolved = None
    if isinstance(named, str) and named:
        candidate = (ROOT / named).resolve()
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
        split = provenance_coverage(derived_provenance)
        print(f"AUTOGENESIS_STATABLE_VOCABULARY|rows={len(rows)}"
              f"|bridge={len(bridge)}"
              f"|elaboration={split['bridge_elaboration']}"
              f"|expressed={split['bridge_expressed']}"
              f"|elided={split['bridge_elided']}"
              f"|unrendered={split['bridge_unrendered']}"
              f"|cached={len(read_json(CACHE).get('constants', {}))}"
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

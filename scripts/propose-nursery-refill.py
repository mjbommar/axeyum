#!/usr/bin/env python3
"""Is there anything left to REFILL the flywheel's input queue with?

`check-dispatchable-frontier.py` answers "how much work is queued" and fails at
G7 when that falls below a floor. It cannot answer the question that comes
next -- *and can the queue be refilled at all?* -- because refilling is not
something a script does here. Measured 2026-08-30 by reading
`gen-autogenesis-nursery-refill.py`:

    a "draw" is a SOURCE EDIT, not a runnable operation.

`FAMILY_MODULES` (20 families) and `FAMILY_ROUTES` are module-level dicts, and
`PER_FAMILY = 10` is a literal. Rows emitted = `PER_FAMILY * len(FAMILY_MODULES)`.
Re-running the generator with those dicts unchanged is a byte-level no-op: it
re-renders the same 200 entries and prints `AUTOGENESIS_NURSERY_REFILL_OK`. To
get more population a human must add a family name, choose its Mathlib modules,
add a routes entry, and re-run. Draws 2, 3 and 4 were all authored by hand on
one day and nothing has run since.

So the refill's real cost is not the generator, it is the JUDGEMENT of which
modules still carry ten fully-screened, unused candidates. That is mechanical,
and this script does it -- turning the hand-derivation into something with an
exit status.

    pinned Mathlib inventory (9,729 records)
      - already drawn into a nursery manifest
      - hygienic / generated names
      - blocked by the divergence registry
      - not statable here (constants outside env | bridge)
      - carrying an elided-proof glyph
      = SURVIVORS, grouped by Mathlib module
      -> a module with >= PER_FAMILY survivors is a READY FAMILY

Exit status depends on what it FOUND, not on completing: R3 fails when the
ready families cannot yield enough dispatchable rows to clear the frontier's
floor. That is the terminal condition for the whole flywheel, and before this
script nothing computed it.

WHY A TRACKED SNAPSHOT. The inventory is a 39 MB NDJSON on `/nas3`, which is
not present on every fleet host. A gate that simply exits 2 off-NAS would be
unrunnable in `check.sh` on most machines; a gate that PASSED off-NAS would be
the checker-that-cannot-fail defect with a host-capability excuse. So the
measurement is snapshotted into the tree and the gate reads the snapshot --
with R2 re-deriving every screen input's digest, so a snapshot measured against
a different environment, vocabulary or registry is STALE and fails rather than
being believed.

Usage:
    python3 scripts/propose-nursery-refill.py              # gate (reads snapshot)
    python3 scripts/propose-nursery-refill.py --remeasure  # rewrite it (needs /nas3)
    python3 scripts/propose-nursery-refill.py --names Init.Data.Nat.Lcm

Exit status:
    0  enough ready families exist to author a draw that clears the floor
    1  a guard fired (R2-R6) -- including "the pool cannot refill the queue"
    2  an input could not be read
"""

from __future__ import annotations

import argparse
import collections
import hashlib
import json
import math
import pathlib
import re
import sys
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
AUTOGENESIS = ROOT / "artifacts" / "autogenesis"
SNAPSHOT = AUTOGENESIS / "refill-headroom-v1.json"
NURSERY = AUTOGENESIS / "nursery-v1.json"
EXTENSION = AUTOGENESIS / "nursery-v2-extension.json"
ENV_SNAPSHOT = AUTOGENESIS / "kernel-environment-snapshot-v1.json"
VOCABULARY = AUTOGENESIS / "mathlib-statable-vocabulary-v1.json"
REGISTRY = AUTOGENESIS / "mirror-divergence-registry.json"
GENERATOR = ROOT / "scripts" / "gen-autogenesis-nursery-refill.py"

# The pinned candidate pool. Both the path and the digest are re-read from the
# GENERATOR's own source rather than duplicated here: two copies of a pin drift,
# and the copy in the gate drifting silently is how a headroom number comes to
# describe a pool the generator will never draw from. R6 enforces the join.
INVENTORY = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/sources/"
    "mathlib-v4.30.0-nat-int-statement-inventory-v2.ndjson")

# Mirrored from the generator. R6 re-reads them from its source and fails if
# either has moved, so these are a default, never an authority.
PER_FAMILY = 10
PARTITION_CYCLE_LEN = 3

# Mirrored from check-dispatchable-frontier.py's G7 for the same reason, and
# re-read from its source by R6.
FRONTIER_FLOOR = 10

CONST_RE = re.compile(r"Lean\.Expr\.const\s+`+([^\s\)\[]+)")
GLYPH_RE = re.compile(r"[⋯✝…]|\bsorry\b")
# The generator's hygiene screen, mirrored. A generated name carries a leading
# underscore on an internal component.
HYGIENE_RE = re.compile(r"\._|\bmatch_\d|_proof_\d|\.eq_\d|\.sizeOf_spec")

# R5's vacuity bound. A snapshot claiming that EVERY module in the inventory is
# ready has not screened anything; one claiming none has screened everything
# away. Both read as a working measurement from the exit status alone, which is
# the failure direction this repository keeps rediscovering. The real screen
# rejects roughly 70% of candidates, so a ready-module fraction anywhere near 1
# means the screen is not running.
MAX_READY_MODULE_FRACTION = 0.90


def die(message: str) -> None:
    print(f"ERROR: {message}", file=sys.stderr)
    raise SystemExit(2)


def sha256_file(path: pathlib.Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def dispatchable_yield(families: int) -> int:
    """Rows a draw of `families` NEW families contributes to the dispatchable set.

    `assign_partitions()` restarts `PARTITION_CYCLE = (held-out, development,
    train)` at index 0 for each draw's new families, so held-out takes
    `ceil(n/3)` of them -- NOT one third. That restart is deliberate (it is what
    lets a small draw add held-out families at all) and it means a draw of 1, 2,
    4 or 5 families over-weights held-out. The committed manifest is 9/6/5 over
    20 families: 45% held-out, not 33%.
    """
    if families <= 0:
        return 0
    held_out = math.ceil(families / PARTITION_CYCLE_LEN)
    return PER_FAMILY * (families - held_out)


def families_needed(floor: int) -> int:
    n = 1
    while dispatchable_yield(n) < floor:
        n += 1
        if n > 1000:  # unreachable; a runaway here would be a wrong yield model
            die("families_needed did not converge; dispatchable_yield is wrong")
    return n


def read_pins() -> dict[str, Any]:
    """R6's inputs: the constants this gate mirrors, re-read from their sources.

    A mirrored constant is a copy, and a copy that drifts turns a correct-looking
    measurement into one about a different world. Each is parsed out of the file
    that OWNS it, so moving `PER_FAMILY` or `FLOOR` breaks this gate loudly
    instead of leaving it quietly answering the old question.
    """
    out: dict[str, Any] = {}
    if not GENERATOR.is_file():
        die(f"no generator at {GENERATOR}")
    gen = GENERATOR.read_text()
    for key, pattern in (("per_family", r"^PER_FAMILY\s*=\s*(\d+)"),
                         ("inventory_sha256",
                          r'^INVENTORY_SHA256\s*=\s*"([0-9a-f]{64})"'),
                         ("inventory_records", r"^INVENTORY_RECORDS\s*=\s*(\d+)")):
        m = re.search(pattern, gen, re.M)
        if m is None:
            die(f"cannot read {key} from {GENERATOR.name}; this gate mirrors it "
                f"and must not fall back to a stale default")
        out[key] = m.group(1)
    m = re.search(r"^PARTITION_CYCLE\s*=\s*\(([^)]*)\)", gen, re.M)
    if m is None:
        die(f"cannot read PARTITION_CYCLE from {GENERATOR.name}")
    out["partition_cycle_len"] = len([p for p in m.group(1).split(",") if p.strip()])

    frontier = ROOT / "scripts" / "check-dispatchable-frontier.py"
    if not frontier.is_file():
        die(f"no frontier checker at {frontier}")
    m = re.search(r"^FLOOR\s*=\s*(\d+)", frontier.read_text(), re.M)
    if m is None:
        die("cannot read FLOOR from check-dispatchable-frontier.py")
    out["frontier_floor"] = int(m.group(1))
    return out


def used_source_names() -> set[str]:
    """Mathlib names already drawn into a nursery manifest.

    NOTE this is deliberately wider than the generator's own `catalogued` screen,
    which reads only the v1 catalog and does NOT exclude names already drawn into
    `nursery-v2-extension.json`. That is safe for the generator (it regenerates
    the manifest whole and the alphabetical slice re-derives identically) and
    NOT safe here: a module whose ten best candidates are already drawn is not a
    ready family, and counting them would propose a draw that yields nothing.
    """
    names: set[str] = set()
    for path in (NURSERY, EXTENSION):
        if not path.is_file():
            die(f"no nursery manifest at {path}")
        doc = json.loads(path.read_text())
        entries = doc.get("entries")
        if not isinstance(entries, list):
            die(f"{path}: no `entries` list")
        for entry in entries:
            name = entry.get("source_name")
            if isinstance(name, str):
                names.add(name)
    if not names:
        die("no source names read from either manifest; the screen would admit "
            "every already-drawn candidate")
    return names


def drawn_modules() -> set[str]:
    """Modules a FAMILY already owns.

    `module_family` in the generator is a flat dict built from `FAMILY_MODULES`,
    so two families naming the same module silently collide (last one wins).
    Proposing a module that is already owned is therefore not merely redundant,
    it corrupts the draw -- R4.
    """
    doc = json.loads(EXTENSION.read_text())
    modules: set[str] = set()
    for tup in (doc.get("family_modules") or {}).values():
        if isinstance(tup, list):
            modules.update(m for m in tup if isinstance(m, str))
    return modules


def input_digests() -> dict[str, str]:
    """R2's freshness key: everything a headroom measurement depends on."""
    digests = {}
    for label, path in (("env_snapshot", ENV_SNAPSHOT),
                        ("vocabulary", VOCABULARY),
                        ("registry", REGISTRY)):
        if not path.is_file():
            die(f"no screen input at {path}")
        digests[label] = sha256_file(path)
    digests["used_source_names"] = sha256_text(
        "\n".join(sorted(used_source_names())))
    digests["drawn_modules"] = sha256_text("\n".join(sorted(drawn_modules())))
    return digests


def load_registry_forms() -> list[dict[str, Any]]:
    doc = json.loads(REGISTRY.read_text())
    rows = doc.get("constructions")
    if not isinstance(rows, list):
        die(f"{REGISTRY}: no `constructions` list")
    return rows


def blocked_by_registry(statement: str, registry: list[dict[str, Any]]) -> bool:
    for entry in registry:
        for form in entry.get("surface_forms", []):
            if isinstance(form, str) and form in statement:
                return True
    return False


def remeasure(pins: dict[str, Any]) -> dict[str, Any]:
    if not INVENTORY.is_file():
        die(f"the pinned statement inventory is not readable at {INVENTORY}. "
            f"--remeasure needs it; the GATE does not (it reads the tracked "
            f"snapshot). This host cannot regenerate the snapshot -- run "
            f"--remeasure on a host with /nas3 mounted.")
    digest = sha256_file(INVENTORY)
    if digest != pins["inventory_sha256"]:
        die(f"inventory digest {digest} does not match the generator's pin "
            f"{pins['inventory_sha256']}. A sibling file with the SAME record "
            f"count exists (…-v1.ndjson), so the digest is the only "
            f"discriminator; measuring headroom against the wrong pool would "
            f"propose families the generator cannot draw.")

    used = used_source_names()
    owned = drawn_modules()
    registry = load_registry_forms()
    snapshot = json.loads(ENV_SNAPSHOT.read_text())
    vocabulary = json.loads(VOCABULARY.read_text())
    admissible = set(snapshot["declarations"]) | set(vocabulary["bridge"])

    reasons: collections.Counter = collections.Counter()
    per_module: collections.Counter = collections.Counter()
    sole_blockers: collections.Counter = collections.Counter()
    modules_seen: set[str] = set()
    records = 0

    for line in INVENTORY.open():
        line = line.strip()
        if not line:
            continue
        record = json.loads(line)
        records += 1
        name = record["name"]
        module = record.get("module", "")
        modules_seen.add(module)
        if name in used:
            reasons["already-drawn"] += 1
            continue
        if HYGIENE_RE.search(name):
            reasons["hygienic-or-generated"] += 1
            continue
        statement = record.get("type") or ""
        if blocked_by_registry(statement, registry):
            reasons["divergence-registry"] += 1
            continue
        missing = set(CONST_RE.findall(record.get("type_repr", ""))) - admissible
        if missing:
            reasons["not-statable-here"] += 1
            if len(missing) == 1:
                sole_blockers[next(iter(missing))] += 1
            continue
        if GLYPH_RE.search(statement):
            reasons["elided-proof-glyph"] += 1
            continue
        reasons["SURVIVES"] += 1
        per_module[module] += 1

    if records != int(pins["inventory_records"]):
        die(f"read {records} inventory records, the generator pins "
            f"{pins['inventory_records']}")

    ready = {m: c for m, c in per_module.items()
             if c >= int(pins["per_family"]) and m not in owned}
    return {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-refill-headroom",
        "measured_from": str(INVENTORY),
        "inventory_sha256": digest,
        "inventory_records": records,
        "why": (
            "A draw is a hand edit to gen-autogenesis-nursery-refill.py's "
            "FAMILY_MODULES and FAMILY_ROUTES, so the queue cannot refill "
            "itself. This snapshot is the mechanical half of that edit: which "
            "Mathlib modules still carry PER_FAMILY fully-screened, unused "
            "candidates. It names MODULES and COUNTS and never a fact id -- "
            "check-autogenesis-holdout-isolation.py forbids any non-population "
            "artifact naming a held-out row, and a candidate named here today "
            "may be drawn into held-out tomorrow."),
        "input_digests": input_digests(),
        "screen_rejections": {k: v for k, v in sorted(reasons.items())
                              if k != "SURVIVES"},
        "survivors": reasons["SURVIVES"],
        "modules_in_inventory": len(modules_seen),
        "modules_with_survivors": len(per_module),
        "ready_families": dict(sorted(ready.items())),
        "ready_family_count": len(ready),
        "modules_already_owned_by_a_family": len(owned),
        "top_sole_blockers": dict(sorted(sole_blockers.most_common(40))),
        "sole_blocker_note": (
            "A constant that is the ONLY thing blocking a row cannot enter the "
            "bridge on its own: check-dispatchable-frontier.py's S2 requires a "
            "bridge constant to be witnessed by an already-SETTLED mirror, and "
            "a mirror using it cannot be preregistered while the screen rejects "
            "it. The v1 nursery predates the screen and is what bootstrapped "
            "the current 70 bridge constants; nothing can bootstrap another one "
            "the same way. Measured 2026-08-30: instSubNat is the sole blocker "
            "of 292 rows, and instAddNat / instMulNat / HSub.hSub / instHSub "
            "are ALREADY bridged -- so the Nat subtraction instance is the "
            "missing sibling of four constants the bridge already has, while "
            "Nat.sub itself is in the environment. This is a real ceiling on "
            "the pool and it needs a decision, not a screen change."),
    }


def check(pins: dict[str, Any], verbose: bool = True) -> int:
    if not SNAPSHOT.is_file():
        die(f"no headroom snapshot at {SNAPSHOT}; regenerate with --remeasure "
            f"on a host that can read {INVENTORY}")
    doc = json.loads(SNAPSHOT.read_text())
    fails: list[str] = []

    # R6 -- the mirrored constants. Checked FIRST: every number below is
    # measured against them, so a drifted pin makes the rest of the run answer
    # a question nobody asked.
    if str(doc.get("inventory_sha256")) != pins["inventory_sha256"]:
        fails.append(
            f"R6 pin-drift: the snapshot was measured against inventory "
            f"{str(doc.get('inventory_sha256'))[:16]}… and the generator now "
            f"pins {pins['inventory_sha256'][:16]}…. The headroom describes a "
            f"pool the generator will not draw from.")
    if str(doc.get("inventory_records")) != str(pins["inventory_records"]):
        fails.append(
            f"R6 pin-drift: snapshot records {doc.get('inventory_records')!r} "
            f"against the generator's {pins['inventory_records']!r}")

    # R2 -- staleness. This is what stops the snapshot being an assertion: the
    # screens it was measured through are files in this tree, and if any has
    # moved the survivor count is about a vocabulary that no longer exists.
    recorded = doc.get("input_digests")
    if not isinstance(recorded, dict):
        fails.append("R2 stale-snapshot: no `input_digests`, so freshness "
                     "cannot be re-derived and the counts are an assertion")
    else:
        current = input_digests()
        for label, value in sorted(current.items()):
            if recorded.get(label) != value:
                fails.append(
                    f"R2 stale-snapshot: `{label}` has changed since the "
                    f"headroom was measured ({str(recorded.get(label))[:12]}… "
                    f"-> {value[:12]}…). Re-run --remeasure; the ready-family "
                    f"list is about a screen this tree no longer has.")

    ready = doc.get("ready_families")
    if not isinstance(ready, dict):
        die(f"{SNAPSHOT}: no `ready_families` map")
    ready_count = len(ready)

    # R5 -- vacuity, both directions. An "everything is ready" snapshot and an
    # empty one are indistinguishable from a working one by exit status alone.
    modules_total = doc.get("modules_in_inventory")
    if not isinstance(modules_total, int) or modules_total <= 0:
        fails.append("R5 vacuous-snapshot: `modules_in_inventory` is not a "
                     "positive count, so the ready fraction cannot be judged")
    elif ready_count > modules_total * MAX_READY_MODULE_FRACTION:
        fails.append(
            f"R5 vacuous-snapshot: {ready_count} of {modules_total} modules "
            f"are 'ready' ({ready_count / modules_total:.0%}). The screens "
            f"reject roughly 70% of candidates; a fraction this high means "
            f"they did not run, and the proposal would be noise.")
    if doc.get("survivors") in (None, 0) and ready_count:
        fails.append("R5 vacuous-snapshot: zero survivors but a non-empty "
                     "ready-family list; these cannot both be true")

    # R4 -- a module already owned by a family must not be proposed. The
    # generator's `module_family` is a flat dict, so a duplicate module silently
    # reassigns every candidate in it to whichever family is built last.
    owned = drawn_modules()
    collisions = sorted(set(ready) & owned)
    if collisions:
        fails.append(
            f"R4 module-already-drawn: {len(collisions)} proposed module(s) are "
            f"already owned by a family ({', '.join(collisions[:3])}). The "
            f"generator's module->family map is flat, so drawing one twice "
            f"reassigns its candidates rather than adding any.")

    floor = pins["frontier_floor"]
    need = families_needed(floor)
    yielded = dispatchable_yield(ready_count)

    if verbose:
        print(f"pinned inventory   {doc.get('inventory_records')} records, "
              f"{doc.get('inventory_sha256', '')[:16]}…")
        rej = doc.get("screen_rejections") or {}
        print(f"screened out       "
              f"{sum(v for v in rej.values() if isinstance(v, int))}")
        for k, v in sorted(rej.items(), key=lambda kv: -kv[1]):
            print(f"    {v:6d}  {k}")
        print(f"survivors          {doc.get('survivors')} across "
              f"{doc.get('modules_with_survivors')} module(s)")
        print(f"READY FAMILIES     {ready_count} "
              f"(module(s) with >= {pins['per_family']} unused survivors, "
              f"not already owned)")
        for module, count in sorted(ready.items(), key=lambda kv: (-kv[1], kv[0]))[:15]:
            print(f"    {count:4d}  {module}")
        if ready_count > 15:
            print(f"    … and {ready_count - 15} more")
        print(f"a draw of all {ready_count} would add "
              f"{yielded} dispatchable row(s) "
              f"(held-out takes ceil(n/3), not a third)")
        print(f"the frontier floor is {floor}, so a draw needs "
              f"{need} new family(ies)")

    # R3 -- the finding. This is the whole reason the script has an exit status.
    if ready_count < need:
        fails.append(
            f"R3 cannot-refill: {ready_count} ready family(ies) yield "
            f"{yielded} dispatchable row(s), below the frontier floor of "
            f"{floor} which needs {need}. The pinned pool cannot refill the "
            f"queue. This is NOT fixable by authoring a draw -- see "
            f"`sole_blocker_note`: growing the pool means growing the statable "
            f"vocabulary, and the bridge cannot bootstrap a new constant "
            f"because S2 requires a settled mirror to witness it. Escalate; do "
            f"not spend held-out rows to make this pass.")

    for line in fails:
        print(f"FAIL: {line}", file=sys.stderr)
    if fails:
        return 1
    print(f"\nOK -- {ready_count} ready family(ies) available, enough for a "
          f"draw of {need} that clears the floor of {floor}. Author it in "
          f"{GENERATOR.name}'s FAMILY_MODULES and FAMILY_ROUTES, then re-run "
          f"the generator.")
    return 0


def show_names(module: str, pins: dict[str, Any]) -> int:
    """The candidates in one module -- for the human authoring the draw.

    Deliberately NOT written into any tracked artifact: these are the exact
    propositions a future draw may assign to held-out, and a tracked file naming
    them would leak the population it is meant to grow.
    """
    if not INVENTORY.is_file():
        die(f"--names needs the pinned inventory at {INVENTORY}")
    used = used_source_names()
    registry = load_registry_forms()
    snapshot = json.loads(ENV_SNAPSHOT.read_text())
    vocabulary = json.loads(VOCABULARY.read_text())
    admissible = set(snapshot["declarations"]) | set(vocabulary["bridge"])
    found = []
    for line in INVENTORY.open():
        if not line.strip():
            continue
        record = json.loads(line)
        if record.get("module") != module:
            continue
        name = record["name"]
        if name in used or HYGIENE_RE.search(name):
            continue
        statement = record.get("type") or ""
        if blocked_by_registry(statement, registry):
            continue
        if set(CONST_RE.findall(record.get("type_repr", ""))) - admissible:
            continue
        if GLYPH_RE.search(statement):
            continue
        found.append((name, statement))
    for name, statement in sorted(found):
        print(f"  {name}\n      {statement}")
    print(f"\n{len(found)} screened unused candidate(s) in {module} "
          f"(PER_FAMILY is {pins['per_family']})")
    if not found:
        print(f"\nFAIL: no screened candidate in {module}. Either the module "
              f"name is wrong or every candidate is drawn or rejected.",
              file=sys.stderr)
        return 1
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--remeasure", action="store_true",
                    help="recompute the headroom snapshot from the pinned "
                         "inventory (needs /nas3) and rewrite it")
    ap.add_argument("--names", metavar="MODULE",
                    help="print the screened unused candidates in one Mathlib "
                         "module, for authoring a draw (needs /nas3)")
    args = ap.parse_args()

    pins = read_pins()
    if int(pins["per_family"]) != PER_FAMILY:
        print(f"note: PER_FAMILY is {pins['per_family']} in the generator, "
              f"this script's mirrored default is {PER_FAMILY}; using the "
              f"generator's.", file=sys.stderr)
    if pins["partition_cycle_len"] != PARTITION_CYCLE_LEN:
        die(f"PARTITION_CYCLE has {pins['partition_cycle_len']} entries, this "
            f"gate's yield model assumes {PARTITION_CYCLE_LEN}")

    if args.names:
        return show_names(args.names, pins)
    if args.remeasure:
        doc = remeasure(pins)
        SNAPSHOT.write_text(json.dumps(doc, indent=1, sort_keys=True) + "\n")
        print(f"wrote {SNAPSHOT.relative_to(ROOT)}: {doc['survivors']} "
              f"survivor(s), {doc['ready_family_count']} ready family(ies)")
        return check(pins)
    return check(pins)


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Kernel theorem pages: the trusted base, rendered from the inventory tools.

WHY THIS PRODUCER EXISTS, AND WHY IT SHELLS OUT.

You cannot read this kernel's theorem inventory from source text.  Declarations
go through a ``.theorem(name, ...)`` helper over interned ``NameId`` fields, so
grepping ``.theorem("...")`` returns ZERO matches and ``Declaration::Theorem``
returns 1 against the real population.  Three separate counts of this
repository's theorems were wrong before anyone built the environment to look.
So every number, name, type and axiom footprint on the pages this script emits
comes from RUNNING the inventory examples in
``crates/axeyum-lean-kernel/examples/`` and parsing their output.  Nothing here
is read from source, and nothing here is typed by a human.

WHAT IT RUNS (and what each tool does NOT cover -- see ``coverage_prose``):

  nat_theorem_inventory      the Nat prelude's theorems, name + canonical type
  int_theorem_inventory      the ``Int.*`` declarations, with footprints
  theorem_axiom_footprint    per-declaration axiom footprints, nat/integer/real
  nat_axiom_inventory        the TRUSTED SURFACE (axiom + opaque + quotient)
                             across all five ``build_*_prelude`` builders

THE EXIT STATUS DEPENDS ON THE FINDING.  Three of the four tools take
expectation flags (``--expect-count``, ``--expect-derived/--expect-asserted``,
``--require-axiom-free``/``--expect-axioms``) and this producer always passes
them, because a census tool that prints a number and exits 0 whatever the number
is cannot distinguish an axiom-free kernel from one that grew twenty axioms
overnight -- which is exactly what this repository shipped 40 times.  The fourth
(``theorem_axiom_footprint``) has NO such flag: its ``main`` returns ``()`` and
its exit status is completion-only.  That record therefore carries NO claims and
says so in its ``notes``; the finding-dependent evidence for axiom-freedom is
the cross-check this script performs itself (``R:kernel-inventory-cross-check``),
which refuses to write anything when two independently-built kernels disagree.

STATUS IS COPIED, NEVER INFERRED.  A census is a finite computation over one
build of one commit, so every claim emitted here carries ``evidence`` -- the
badge the vocabulary reserves for exactly that ("a finite computation, carrying
no universal credit").  The per-theorem ``statement`` blocks get their status
from assembly, which reports ``proved``/``kernel-lean`` for a kernel reference.
THAT IS ONLY TRUE FOR A THEOREM ROW: ``assemble.rs`` stamps those two values on
every kernel reference regardless of declaration kind, so an ``axiom`` row
referenced from a ``statement`` block would render as ``proved``.  This producer
therefore keeps the two populations in two files -- ``kernel-inventory.json``
holds theorem rows and is the only snapshot any ``statement`` block references;
``kernel-assumptions.json`` holds the trusted surface and is referenced by
nothing.  The wish list for upstream is in
``docs/render-2026-08/19-adr-kernel-diary.md``.

Determinism: no wall clock.  ``epoch`` is SOURCE_DATE_EPOCH, or the commit that
last touched the kernel crate, or an explicit ``--epoch-unix``.

Usage:

    python3 render/producers-kernel/kernel_to_docir.py
    python3 render/producers-kernel/kernel_to_docir.py --no-validate
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
OUT_DIR = ROOT / "render" / "examples-input" / "kernel"
EXAMPLES = ROOT / "crates" / "axeyum-lean-kernel" / "examples"
VALIDATE_DOCIR = ROOT / "scripts" / "validate-docir.py"
DOCIR_SCHEMA = ROOT / "artifacts" / "ontology" / "docir.schema.json"

GENERATOR = "render/producers-kernel/kernel_to_docir.py"
COMMAND = "python3 render/producers-kernel/kernel_to_docir.py"
SLUG_RE = re.compile(r"^[a-z0-9]+(-[a-z0-9]+)*$")

INVENTORY_REL = "render/examples-input/kernel/kernel-inventory.json"
ASSUMPTIONS_REL = "render/examples-input/kernel/kernel-assumptions.json"

# The expectations this producer pins. Every one of them is a number MEASURED by
# the tool on the previous run and re-asserted on this one; a drift in either
# direction fails the tool, which fails this producer, which writes nothing.
EXPECT_NAT_THEOREMS = 139
EXPECT_INT_DERIVED = 57
EXPECT_INT_ASSERTED = 0
EXPECT_TRUSTED = {"logic": 0, "nat": 0, "real": 30, "integer": 0, "string": 1}


# --- small helpers -----------------------------------------------------------

def rel(path: Path) -> str:
    try:
        return str(Path(path).resolve().relative_to(ROOT))
    except ValueError:
        return str(path)


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def slugify(name: str) -> str:
    s = re.sub(r"[^a-z0-9]+", "-", name.lower()).strip("-")
    return re.sub(r"-+", "-", s)


def write_json(path: Path, doc: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(doc, sort_keys=True, indent=2, ensure_ascii=True) + "\n"
    path.write_text(text, encoding="ascii")


# --- running the tools -------------------------------------------------------

class Run:
    """One execution of one inventory example, kept whole."""

    def __init__(self, example: str, args: list[str], quiet: bool):
        self.example = example
        self.args = args
        self.source = EXAMPLES / f"{example}.rs"
        self.command = (
            "cargo run --release -q -p axeyum-lean-kernel --example "
            + example
            + (" -- " + " ".join(args) if args else "")
        )
        argv = [
            "cargo", "run", "--release", "-q", "-p", "axeyum-lean-kernel",
            "--example", example,
        ]
        if args:
            argv += ["--"] + args
        proc = subprocess.run(argv, cwd=str(ROOT), capture_output=True, text=True)
        self.exit_status = proc.returncode
        self.stdout = proc.stdout
        self.stderr = proc.stderr
        if not quiet:
            print(f"  ran {example}: exit={self.exit_status} "
                  f"stdout_lines={len(self.stdout.splitlines())}")

    def rows(self) -> list[list[str]]:
        return [ln.split("\t") for ln in self.stdout.splitlines() if ln.strip()]

    def provenance(self, epoch: dict) -> dict:
        return {
            "generator": f"crates/axeyum-lean-kernel/examples/{self.example}.rs",
            "command": self.command,
            "inputs": [{
                "path": rel(self.source),
                "sha256": sha256_file(self.source),
                "role": "source",
            }],
            "exit_status": self.exit_status,
            "epoch": epoch,
        }

    def replay(self) -> dict:
        return {
            "line": self.command,
            "cwd": ".",
            "expected_exit_status": 0,
            "expected_seconds": 1,
        }


# --- parsers (defensive: the tools' formats are TSV and undeclared) ----------

def parse_nat_theorems(run: Run) -> list[dict]:
    """`name<TAB>binders<TAB>canonical-type`."""
    out = []
    for i, row in enumerate(run.rows(), 1):
        if len(row) != 3:
            raise ValueError(f"nat_theorem_inventory line {i}: expected 3 "
                             f"tab-separated fields, got {len(row)}: {row[:1]}")
        name, binders, ty = row
        if not binders.isdigit():
            raise ValueError(f"nat_theorem_inventory line {i}: field 2 is not a "
                             f"count: {binders!r}")
        out.append({"name": name, "binders": int(binders), "type": ty})
    return out


def parse_int_declarations(run: Run) -> list[dict]:
    """`kind<TAB>name<TAB>comma-footprint<TAB>canonical-type`."""
    out = []
    for i, row in enumerate(run.rows(), 1):
        if len(row) != 4:
            raise ValueError(f"int_theorem_inventory line {i}: expected 4 fields, "
                             f"got {len(row)}")
        kind, name, footprint, ty = row
        if kind not in ("theorem", "axiom"):
            raise ValueError(f"int_theorem_inventory line {i}: unknown kind {kind!r}")
        out.append({
            "name": name,
            "kind": kind,
            "type": ty,
            "axiom_footprint": [a for a in footprint.split(",") if a],
        })
    return out


def parse_footprints(run: Run) -> dict[str, dict[str, list[str]]]:
    """`prelude<TAB>name<TAB>size<TAB>comma-footprint` -> prelude -> name -> fp."""
    by_prelude: dict[str, dict[str, list[str]]] = {}
    for i, row in enumerate(run.rows(), 1):
        # The final column is EMPTY for an axiom-free declaration, and a trailing
        # empty field survives `split("\t")` -- but only if the tool printed the
        # tab. Accept both widths rather than trusting that it always does.
        if len(row) == 3:
            row = row + [""]
        if len(row) != 4:
            raise ValueError(f"theorem_axiom_footprint line {i}: expected 4 fields, "
                             f"got {len(row)}")
        prelude, name, size, footprint = row
        axioms = [a for a in footprint.split(",") if a]
        if not size.isdigit() or int(size) != len(axioms):
            raise ValueError(f"theorem_axiom_footprint line {i}: declared size "
                             f"{size!r} disagrees with {len(axioms)} listed axioms "
                             f"for {name!r}")
        by_prelude.setdefault(prelude, {})[name] = axioms
    return by_prelude


def parse_trusted_surface(run: Run) -> list[dict]:
    """`prelude<TAB>kind<TAB>name<TAB>type-utf8-as-hex`."""
    out = []
    for i, row in enumerate(run.rows(), 1):
        if len(row) != 4:
            raise ValueError(f"nat_axiom_inventory line {i}: expected 4 fields, "
                             f"got {len(row)}")
        prelude, kind, name, hexed = row
        try:
            ty = bytes.fromhex(hexed).decode("utf-8")
        except ValueError as exc:
            raise ValueError(f"nat_axiom_inventory line {i}: field 4 is not "
                             f"hex-encoded UTF-8 ({exc})") from exc
        out.append({"name": name, "kind": kind, "prelude": prelude, "type": ty})
    return out


SUMMARY_RE = re.compile(
    r"^(\w+): axiom=(\d+) opaque=(\d+) quotient=(\d+) total_trusted=(\d+)$")
FOOTPRINT_SUMMARY_RE = re.compile(
    r"^(\w+): (\d+) theorems, (\d+) axiom-free, footprint min=(\d+) mean=([\d.]+) "
    r"max=(\d+), environment has (\d+) trusted declarations$")


def parse_stderr_summaries(run: Run, pattern: re.Pattern) -> list[tuple]:
    """The per-prelude summary lines the tools print to stderr.

    Parsed rather than recomputed on purpose: these are the numbers the tool
    ASSERTS, and a table that recomputed them from stdout would be a second
    opinion wearing the tool's name.
    """
    out = []
    for line in run.stderr.splitlines():
        m = pattern.match(line.strip())
        if m:
            out.append(m.groups())
    return out


# --- Doc-IR construction -----------------------------------------------------

def producer_provenance(inputs: list[Path], epoch: dict) -> dict:
    """Provenance for content THIS script produced.

    `exit_status: 0` is honest because nothing is written unless every tool
    expectation held and every cross-check passed: the status depends on the
    finding, not on completion.
    """
    return {
        "generator": GENERATOR,
        "command": COMMAND,
        "inputs": [{"path": rel(p), "sha256": sha256_file(p)} for p in inputs],
        "exit_status": 0,
        "epoch": epoch,
    }


def block(bid: str, tag: str, kind: dict, prov: dict | None = None,
          title: str | None = None) -> dict:
    assert SLUG_RE.match(bid), f"block id {bid!r} is not a slug"
    b = {"id": bid, "tag": tag, "kind": kind}
    if title:
        b["title"] = title
    if prov is not None:
        b["provenance"] = prov
    return b


def prose(bid: str, text: str, level: int | None = None, tag: str = "essential",
          title: str | None = None) -> dict:
    kind = {"type": "prose", "text": text}
    if level:
        kind["heading_level"] = level
    return block(bid, tag, kind, title=title)


def table_from_run(bid: str, record: str, record_id: str, table: str,
                   caption: str, tag: str = "essential",
                   title: str | None = None) -> dict:
    return block(bid, tag, {
        "type": "table",
        "caption": {"text": caption},
        "from_run": {"run_record": record, "table": table, "record_id": record_id},
    }, title=title)


def claim(bid: str, label: str, statement: str, record: str, record_id: str,
          claim_key: str, note: str, tag: str = "essential") -> dict:
    return block(bid, tag, {
        "type": "claim",
        "label": label,
        "statement": {"source": "text", "text": statement},
        "status": "evidence",
        "evidence": [{
            "run_record": record,
            "record_id": record_id,
            "claim_key": claim_key,
            "role": "primary",
        }],
        "note": {"text": note},
    })


def statement_block(bid: str, name: str, prov: dict, tag: str = "detail") -> dict:
    return block(bid, tag, {
        "type": "statement",
        "ref": {"kind": "kernel", "name": name, "inventory": INVENTORY_REL},
        "show": ["title", "formal", "status", "proof_route", "axiom_footprint"],
    }, prov=prov, title=name)


# --- coverage prose (charge item 3: state coverage, never imply it) ----------

COVERAGE = (
    "**What these numbers cover, and what they do not.** Every figure on this "
    "page came out of running an inventory example; none of it was read from "
    "source text, because this kernel's declarations go through a "
    "`.theorem(name, ...)` helper over interned name ids and are invisible to "
    "grep. Coverage is not uniform across the four tools and the differences "
    "matter: `nat_axiom_inventory` enumerates the trusted surface (axiom + "
    "opaque + quotient, not `Declaration::Axiom` alone) for all five prelude "
    "builders in the crate -- `logic`, `nat`, `real`, `integer`, `string` -- "
    "with the string prelude built at width 2; `theorem_axiom_footprint` "
    "covers `nat`, `integer` and `real` ONLY, so it says nothing about the "
    "string prelude, and it folds the logic prelude into `nat` because "
    "`build_nat_prelude` builds logic first; `nat_theorem_inventory` covers "
    "the Nat prelude alone; `int_theorem_inventory` filters to names prefixed "
    "`Int.`, so the whole Nat development the integer construction rests on is "
    "excluded from its counts and covered by its own inventory. A fifth tool, "
    "`prelude_axiom_inventory`, was run as a control: it covers `real`, "
    "`integer` and `string` only, so its zero Nat rows mean *never "
    "enumerated*, not *axiom-free* -- the two are indistinguishable in that "
    "output and the difference is the whole claim."
)

STATUS_NOTE = (
    "**Why every claim here reads `evidence` and not `proved`.** A census is a "
    "finite computation over one build of one commit; the badge vocabulary "
    "reserves `evidence` for exactly that. The individual theorems ARE kernel-"
    "admitted, and each per-theorem page renders the `proved` badge assembly "
    "computes for a kernel reference. The statement that *there are 139 of them "
    "and none rests on an assumption* is a measurement, and it is pinned by "
    "expectation flags rather than asserted by this prose: the runs behind it "
    "fail on drift in either direction."
)

ASSEMBLY_CAVEAT = (
    "**Only theorem rows are referenced.** `render/src/assemble.rs` resolves a "
    "kernel reference to `epistemic_status: proved` and `proof_route: "
    "kernel-lean` for every declaration in the snapshot, without consulting the "
    "`kind` column -- so an axiom row referenced from a statement block would "
    "render as proved. The two populations are therefore kept in two snapshots: "
    "`kernel-inventory.json` holds theorem rows and is the only file any "
    "statement block on any of these pages resolves against, and "
    "`kernel-assumptions.json` holds the trusted surface and is referenced by "
    "no statement block anywhere. The assumptions are rendered as a table, "
    "which carries no status at all."
)


# --- the build ---------------------------------------------------------------

def resolve_epoch(args) -> tuple[dict | None, str | None]:
    """Epoch as INPUT, never observed."""
    if args.epoch_unix is not None:
        e = {"unix": args.epoch_unix, "source": args.epoch_source}
        if args.epoch_commit:
            e["commit"] = args.epoch_commit
        return e, None
    sde = os.environ.get("SOURCE_DATE_EPOCH")
    if sde and sde.isdigit():
        return {"unix": int(sde), "source": "source-date-epoch"}, None
    try:
        out = subprocess.run(
            ["git", "-C", str(ROOT), "log", "-1", "--format=%ct %H", "--",
             "crates/axeyum-lean-kernel"],
            capture_output=True, text=True, check=False)
        parts = out.stdout.split()
        if out.returncode == 0 and len(parts) == 2 and parts[0].isdigit():
            return {"unix": int(parts[0]), "source": "commit", "commit": parts[1]}, None
    except OSError:
        pass
    return None, ("no epoch: SOURCE_DATE_EPOCH is unset and git could not date "
                  "crates/axeyum-lean-kernel. Pass --epoch-unix N "
                  "[--epoch-source fixed]; the renderer never reads the clock.")


def cross_check(nat_theorems, int_decls, footprints) -> list[str]:
    """Two independently-built kernels must agree. Findings, not completion."""
    errors: list[str] = []

    nat_names = {t["name"] for t in nat_theorems}
    fp_nat = footprints.get("nat", {})
    if not fp_nat:
        errors.append("theorem_axiom_footprint reported no `nat` rows at all; an "
                      "empty result from a tool that was never pointed at the "
                      "subject is indistinguishable from a strong negative")
    missing = sorted(nat_names - set(fp_nat))
    extra = sorted(set(fp_nat) - nat_names)
    if missing:
        errors.append(f"{len(missing)} Nat theorem(s) have no footprint row: "
                      f"{missing[:5]}")
    if extra:
        errors.append(f"{len(extra)} footprint row(s) name no Nat theorem: "
                      f"{extra[:5]}")
    non_free = sorted(n for n, fp in fp_nat.items() if fp)
    if non_free:
        errors.append(f"{len(non_free)} Nat declaration(s) carry a non-empty axiom "
                      f"footprint: {non_free[:5]}")

    fp_int = footprints.get("integer", {})
    for d in int_decls:
        recorded = fp_int.get(d["name"])
        if recorded is None:
            errors.append(f"Int declaration {d['name']} has no footprint row in "
                          f"theorem_axiom_footprint's `integer` group")
        elif sorted(recorded) != sorted(d["axiom_footprint"]):
            errors.append(f"footprint disagreement for {d['name']}: "
                          f"{sorted(d['axiom_footprint'])} vs {sorted(recorded)}")
    return errors


def build(args) -> int:
    quiet = args.quiet
    epoch, err = resolve_epoch(args)
    if epoch is None:
        print(f"error: {err}", file=sys.stderr)
        return 2

    print("running the kernel inventory examples (the only way to read this "
          "inventory):")
    runs = {
        "nat": Run("nat_theorem_inventory",
                   ["--expect-count", str(EXPECT_NAT_THEOREMS)], quiet),
        "int": Run("int_theorem_inventory",
                   ["--expect-derived", str(EXPECT_INT_DERIVED),
                    "--expect-asserted", str(EXPECT_INT_ASSERTED)], quiet),
        "footprint": Run("theorem_axiom_footprint", [], quiet),
        "trusted": Run("nat_axiom_inventory",
                       ["--require-axiom-free", "logic",
                        "--require-axiom-free", "nat",
                        "--expect-axioms", f"real={EXPECT_TRUSTED['real']}",
                        "--expect-axioms", f"integer={EXPECT_TRUSTED['integer']}",
                        "--expect-axioms", f"string={EXPECT_TRUSTED['string']}"],
                       quiet),
    }

    failed = [k for k, r in runs.items() if r.exit_status != 0]
    if failed:
        for k in failed:
            print(f"error: {runs[k].example} exited {runs[k].exit_status}",
                  file=sys.stderr)
            for line in runs[k].stderr.splitlines()[-6:]:
                print(f"  {line}", file=sys.stderr)
        print("refusing to emit: a census whose expectation failed is a finding, "
              "not a page", file=sys.stderr)
        return 1

    try:
        nat_theorems = parse_nat_theorems(runs["nat"])
        int_decls = parse_int_declarations(runs["int"])
        footprints = parse_footprints(runs["footprint"])
        trusted = parse_trusted_surface(runs["trusted"])
    except ValueError as exc:
        print(f"error: parsing an inventory tool's output failed: {exc}",
              file=sys.stderr)
        return 1

    errors = cross_check(nat_theorems, int_decls, footprints)
    if errors:
        for e in errors:
            print(f"error: {e}", file=sys.stderr)
        print("refusing to emit: two independently-built kernels disagree",
              file=sys.stderr)
        return 1

    surface_rows = [list(g) for g in
                    parse_stderr_summaries(runs["trusted"], SUMMARY_RE)]
    fp_rows = [list(g) for g in
               parse_stderr_summaries(runs["footprint"], FOOTPRINT_SUMMARY_RE)]
    if not surface_rows or not fp_rows:
        print("error: a tool's stderr summary did not match the expected shape; "
              "the tables would be empty and an empty table is not a finding",
              file=sys.stderr)
        return 1
    seen = {r[0] for r in surface_rows}
    unexpected = seen ^ set(EXPECT_TRUSTED)
    if unexpected:
        print(f"error: nat_axiom_inventory enumerated {sorted(seen)}, expected "
              f"{sorted(EXPECT_TRUSTED)} -- coverage changed and the prose that "
              f"states it is now stale", file=sys.stderr)
        return 1

    # --- snapshots -----------------------------------------------------------
    # Theorem rows only. See ASSEMBLY_CAVEAT.
    decls = []
    for t in nat_theorems:
        decls.append({
            "name": t["name"], "kind": "theorem", "prelude": "nat",
            "type": t["type"], "binders": t["binders"],
            "axiom_footprint": footprints["nat"][t["name"]],
        })
    for d in int_decls:
        if d["kind"] != "theorem":
            continue
        decls.append({
            "name": d["name"], "kind": "theorem", "prelude": "integer",
            "type": d["type"], "axiom_footprint": d["axiom_footprint"],
        })
    decls.sort(key=lambda d: (d["prelude"], d["name"]))

    inventory = {
        "note": ("Kernel inventory snapshot: THEOREM ROWS ONLY. Produced by "
                 "running the inventory examples, never by reading source. "
                 "Assembly resolves a kernel reference to `proved`/`kernel-lean` "
                 "without consulting `kind`, so assumptions live in "
                 + ASSUMPTIONS_REL + " and are referenced by no statement block."),
        "generator": GENERATOR,
        "commands": [runs["nat"].command, runs["int"].command,
                     runs["footprint"].command],
        "epoch": epoch,
        "declarations": decls,
    }
    write_json(OUT_DIR / "kernel-inventory.json", inventory)

    assumptions = {
        "note": ("The TRUSTED SURFACE: declarations admitted without a checked "
                 "proof body (axiom + opaque + quotient). Referenced by no "
                 "statement block; rendered only as a table, which carries no "
                 "status."),
        "generator": GENERATOR,
        "commands": [runs["trusted"].command],
        "epoch": epoch,
        "declarations": [{"name": r["name"], "kind": r["kind"],
                          "prelude": r["prelude"], "type": r["type"]}
                         for r in trusted],
    }
    write_json(OUT_DIR / "kernel-assumptions.json", assumptions)

    # --- run records ---------------------------------------------------------
    records: dict[str, tuple[str, dict]] = {}

    records["nat"] = ("run-nat-theorem-inventory.json", {
        "schema_version": 1,
        "id": "R:kernel-nat-theorem-inventory",
        "provenance": runs["nat"].provenance(epoch),
        "summary": (f"The Nat prelude admits {len(nat_theorems)} theorems; the run "
                    f"was pinned with --expect-count {EXPECT_NAT_THEOREMS} and "
                    f"fails on drift in either direction."),
        "outcome": "established",
        "claims": [{
            "key": "nat-theorem-population",
            "status": "evidence",
            "statement": (f"The Nat prelude, built by build_nat_prelude, admits "
                          f"exactly {len(nat_theorems)} theorems."),
            "note": ("--expect-count makes the exit status depend on the finding: "
                     "a shrink means something previously proved is gone, a growth "
                     "means the expectation is stale."),
        }],
        "stats": {"theorems": len(nat_theorems)},
        "replay": runs["nat"].replay(),
    })

    int_free = sum(1 for d in int_decls if d["kind"] == "theorem"
                   and not d["axiom_footprint"])
    records["int"] = ("run-int-theorem-inventory.json", {
        "schema_version": 1,
        "id": "R:kernel-int-theorem-inventory",
        "provenance": runs["int"].provenance(epoch),
        "summary": (f"{EXPECT_INT_DERIVED} Int.* declarations are derived and "
                    f"{EXPECT_INT_ASSERTED} still asserted; {int_free} of the "
                    f"derived ones have an empty axiom footprint."),
        "outcome": "established",
        "claims": [
            {
                "key": "int-derived-population",
                "status": "evidence",
                "statement": (f"The integer prelude carries {EXPECT_INT_DERIVED} "
                              f"derived Int.* declarations and "
                              f"{EXPECT_INT_ASSERTED} still asserted."),
                "note": ("--expect-derived/--expect-asserted pin both halves; a "
                         "GROWTH in the asserted count is the failure that matters "
                         "most, since it means something previously proved is now "
                         "assumed."),
            },
            {
                "key": "int-footprints-empty",
                "status": "evidence",
                "statement": (f"{int_free} of the {EXPECT_INT_DERIVED} derived "
                              f"Int.* declarations have an empty axiom footprint "
                              f"(Kernel::axiom_footprint, this kernel's #print "
                              f"axioms)."),
                "note": ("The footprint column is printed by the tool per row; the "
                         "count here is over those rows, and it is cross-checked "
                         "against theorem_axiom_footprint in "
                         "R:kernel-inventory-cross-check."),
            },
        ],
        "stats": {"derived": EXPECT_INT_DERIVED, "asserted": EXPECT_INT_ASSERTED,
                  "axiom_free": int_free},
        "replay": runs["int"].replay(),
    })

    records["footprint"] = ("run-theorem-axiom-footprint.json", {
        "schema_version": 1,
        "id": "R:kernel-theorem-axiom-footprint",
        "provenance": runs["footprint"].provenance(epoch),
        "summary": ("Per-declaration axiom footprints for the nat, integer and "
                    "real preludes, with the per-prelude spread the tool reports."),
        "outcome": "inconclusive",
        "stats": {"rows": len(runs["footprint"].stdout.splitlines())},
        "tables": {
            "footprint-summary": {
                "columns": ["prelude", "declarations", "axiom-free", "min",
                            "mean", "max", "trusted declarations in environment"],
                "rows": fp_rows,
            },
        },
        "replay": {"line": runs["footprint"].command, "cwd": ".",
                   "expected_exit_status": 0, "expected_seconds": 1},
        "notes": ("THIS RECORD CARRIES NO CLAIMS, DELIBERATELY. "
                  "theorem_axiom_footprint has no expectation flag: its main "
                  "returns () and its exit status is 0 on completion whatever the "
                  "numbers are, so nothing in the command makes the status depend "
                  "on what the run found. Its output is used here as DATA (the "
                  "spread table, and the per-theorem footprints in the inventory "
                  "snapshot) and never as the evidence for a claim; the "
                  "finding-dependent evidence is R:kernel-nat-axiom-inventory and "
                  "R:kernel-inventory-cross-check. `outcome: inconclusive` records "
                  "that this run establishes nothing on its own. Upstream wish: an "
                  "--expect-axiom-free <prelude> flag."),
    })

    records["trusted"] = ("run-nat-axiom-inventory.json", {
        "schema_version": 1,
        "id": "R:kernel-nat-axiom-inventory",
        "provenance": runs["trusted"].provenance(epoch),
        "summary": ("The trusted surface (axiom + opaque + quotient) of all five "
                    "prelude builders: logic 0, nat 0, integer 0, string 1, "
                    "real 30 -- each number pinned by a flag that fails on drift."),
        "outcome": "established",
        "claims": [
            {
                "key": "nat-axiom-free",
                "status": "evidence",
                "statement": ("The Nat prelude's trusted surface is empty: 0 "
                              "axioms, 0 opaque declarations, 0 quotient "
                              "declarations."),
                "note": ("--require-axiom-free nat turns the printed zero into a "
                         "check, and a prelude the tool does not enumerate is an "
                         "ERROR rather than a silent pass -- so this zero means "
                         "`enumerated and found empty`, not `never enumerated`."),
            },
            {
                "key": "logic-axiom-free",
                "status": "evidence",
                "statement": ("The logic prelude's trusted surface is empty, "
                              "enumerated separately from Nat so its share is "
                              "attributable rather than folded in."),
                "note": "--require-axiom-free logic.",
            },
            {
                "key": "integer-axiom-free",
                "status": "evidence",
                "statement": ("The integer prelude's trusted surface is empty: the "
                              "Int development is derived, not assumed."),
                "note": ("--expect-axioms integer=0. This number was 34, then 1; "
                         "the expectation is re-asserted on every run precisely "
                         "because it moves."),
            },
            {
                "key": "real-assumes-thirty",
                "status": "evidence",
                "statement": ("The Real prelude asserts 30 declarations outright. "
                              "It is NOT axiom-free, by design, and every one of "
                              "them is named in the assumptions table."),
                "note": ("--expect-axioms real=30 fails on drift in either "
                         "direction; the honest expectation for a prelude that "
                         "assumes by design is the committed number, not zero."),
            },
            {
                "key": "string-assumes-one",
                "status": "evidence",
                "statement": ("The string prelude, built at width 2, asserts one "
                              "declaration."),
                "note": "--expect-axioms string=1; width 2 is the enumerated width.",
            },
        ],
        "stats": {f"{p}_trusted": n for p, n in sorted(EXPECT_TRUSTED.items())},
        "tables": {
            "trusted-surface": {
                "columns": ["prelude", "axiom", "opaque", "quotient",
                            "total trusted"],
                "rows": surface_rows,
            },
            "assumptions": {
                "columns": ["prelude", "kind", "declaration"],
                "rows": [[r["prelude"], r["kind"], r["name"]] for r in trusted],
            },
        },
        "replay": runs["trusted"].replay(),
    })

    cross_inputs = [r.source for r in runs.values()]
    records["cross"] = ("run-inventory-cross-check.json", {
        "schema_version": 1,
        "id": "R:kernel-inventory-cross-check",
        "provenance": producer_provenance(cross_inputs, epoch),
        "summary": ("Two independently built kernels agree: the Nat theorem names "
                    "and every Int.* footprint match across two tools, and no Nat "
                    "declaration carries a non-empty footprint."),
        "outcome": "established",
        "claims": [
            {
                "key": "nat-names-agree",
                "status": "evidence",
                "statement": (f"The {len(nat_theorems)} names nat_theorem_inventory "
                              f"prints are exactly the "
                              f"{len(footprints.get('nat', {}))} nat rows "
                              f"theorem_axiom_footprint prints -- neither tool has "
                              f"a row the other lacks."),
                "note": ("Set equality both ways. The producer writes nothing when "
                         "it fails, so this record's exit status depends on the "
                         "finding even though one of the two tools' own does not."),
            },
            {
                "key": "nat-footprints-empty",
                "status": "evidence",
                "statement": ("Every Nat declaration's axiom footprint is empty, "
                              "checked row by row rather than read off a summary "
                              "line."),
                "note": ("Checked against the per-row footprint column, and the "
                         "declared size of each row is checked against the number "
                         "of axioms actually listed on it."),
            },
            {
                "key": "int-footprints-agree",
                "status": "evidence",
                "statement": (f"All {EXPECT_INT_DERIVED} Int.* footprints agree "
                              f"between int_theorem_inventory and "
                              f"theorem_axiom_footprint, as sets."),
                "note": "Two separately built Int kernels, compared name by name.",
            },
        ],
        "stats": {
            "nat_theorems": len(nat_theorems),
            "nat_footprint_rows": len(footprints.get("nat", {})),
            "int_declarations": len(int_decls),
            "inventory_declarations": len(decls),
            "trusted_declarations": len(trusted),
        },
        "replay": {"line": COMMAND, "cwd": ".", "expected_exit_status": 0,
                   "expected_seconds": 20},
        "notes": ("The cross-check is the reason this producer can attach a "
                  "finding-dependent exit status to the axiom-free claim without "
                  "relying on theorem_axiom_footprint, whose own exit status is "
                  "completion-only."),
    })

    for _, (fname, rec) in records.items():
        write_json(OUT_DIR / fname, rec)

    # --- documents -----------------------------------------------------------
    snapshot_paths = [OUT_DIR / "kernel-inventory.json",
                      OUT_DIR / "kernel-assumptions.json"]
    record_paths = [OUT_DIR / fname for fname, _ in records.values()]
    doc_prov = producer_provenance(snapshot_paths + record_paths, epoch)
    stmt_prov = producer_provenance([OUT_DIR / "kernel-inventory.json"], epoch)

    repo = {"url": "https://github.com/mjbommar/axeyum", "root": ""}
    if epoch.get("commit"):
        repo["commit"] = epoch["commit"]
    options = {"latex": {"detail": "appendix", "package": "axeyum"},
               "markdown": {"badge_style": "text"}}

    def meta(doc_id: str, title: str, subtitle: str, abstract: str) -> dict:
        return {
            "doc_id": doc_id,
            "title": title,
            "subtitle": subtitle,
            "genre": "result",
            "authors": ["Axeyum render strand (prose only; every name, type, "
                        "count and footprint is machine-produced)"],
            "abstract": {"text": abstract},
            "epoch": epoch,
            "repo": repo,
            "options": options,
        }

    docs: list[tuple[Path, dict]] = []

    # 1. The index page.
    index_blocks = [
        prose("intro", (
            "This page is a census of what this project's kernel has actually "
            "admitted, and of what it still assumes. It is generated by running "
            "the inventory examples and parsing their output; the numbers below "
            "exist in exactly one place, and it is not this sentence."), level=None),
        prose("coverage", COVERAGE, title="Coverage"),
        prose("status-vocabulary", STATUS_NOTE, tag="detail",
              title="On the badges"),
        prose("assembly-caveat", ASSEMBLY_CAVEAT, tag="detail",
              title="Theorem rows and assumption rows"),
        prose("what-is-trusted", "What counts as trusted", level=2),
        prose("what-is-trusted-body", (
            "The trusted base is the set of declarations admitted WITHOUT a "
            "checked proof body -- axioms, opaque declarations, and the quotient "
            "primitives. `Declaration::Axiom` alone is not it: an opaque "
            "declaration has no proof body to check and the quotient constructor "
            "admits `Quot.sound`, one of the three axioms Lean's own `#print "
            "axioms` reports. The census below counts all three kinds.")),
        table_from_run("trusted-surface", "run-nat-axiom-inventory.json",
                       "R:kernel-nat-axiom-inventory", "trusted-surface",
                       "Trusted surface by prelude (axiom + opaque + quotient)",
                       title="The trusted surface"),
        claim("claim-nat-axiom-free",
              "The Nat development rests on nothing",
              "The Nat prelude's trusted surface is empty: no axiom, no opaque "
              "declaration, no quotient primitive.",
              "run-nat-axiom-inventory.json", "R:kernel-nat-axiom-inventory",
              "nat-axiom-free",
              "Pinned by --require-axiom-free nat, which errors on a prelude the "
              "tool does not enumerate, so the zero cannot be the zero of a "
              "question that was never asked."),
        claim("claim-logic-axiom-free",
              "The logic prelude rests on nothing",
              "The logic prelude's trusted surface is empty, enumerated "
              "separately so its share is attributable rather than folded into "
              "Nat's.",
              "run-nat-axiom-inventory.json", "R:kernel-nat-axiom-inventory",
              "logic-axiom-free",
              "build_nat_prelude builds logic first, so a Nat proof rests on both; "
              "the split exists so the two can be reported apart."),
        claim("claim-integer-axiom-free",
              "The integer development is derived, not assumed",
              "The integer prelude's trusted surface is empty.",
              "run-nat-axiom-inventory.json", "R:kernel-nat-axiom-inventory",
              "integer-axiom-free",
              "This count was 34, then 1, now 0: it is re-asserted by flag on "
              "every run precisely because it is the number that moves."),
        claim("claim-real-assumes",
              "The Real prelude is not axiom-free, and says so",
              "The Real prelude asserts 30 declarations outright.",
              "run-nat-axiom-inventory.json", "R:kernel-nat-axiom-inventory",
              "real-assumes-thirty",
              "Reported here rather than omitted: a trusted-base page that showed "
              "only the axiom-free preludes would be a page about the tool's "
              "coverage, not about the kernel."),
        prose("population-heading", "Theorem population", level=2),
        prose("population-body", (
            "How many theorems there are, and how many of them rest on an "
            "assumption. The footprint is `Kernel::axiom_footprint`, this "
            "kernel's `#print axioms`.")),
        table_from_run("footprint-summary", "run-theorem-axiom-footprint.json",
                       "R:kernel-theorem-axiom-footprint", "footprint-summary",
                       "Declarations, axiom-free count, and footprint spread "
                       "(nat, integer and real only)",
                       title="Footprint spread"),
        claim("claim-nat-population",
              "The Nat prelude admits 139 theorems",
              "The Nat prelude, built by build_nat_prelude, admits exactly 139 "
              "theorems, each with a canonical type this page can quote.",
              "run-nat-theorem-inventory.json", "R:kernel-nat-theorem-inventory",
              "nat-theorem-population",
              "Pinned with --expect-count, which fails on drift in either "
              "direction."),
        claim("claim-int-population",
              "The integer prelude derives 57 Int declarations and asserts none",
              "57 Int.* declarations are derived and 0 are still asserted.",
              "run-int-theorem-inventory.json", "R:kernel-int-theorem-inventory",
              "int-derived-population",
              "Pinned with --expect-derived and --expect-asserted; a growth in "
              "the asserted count is the failure that matters most."),
        claim("claim-cross-check",
              "Two independently built kernels agree on the population",
              "The Nat theorem names printed by one tool are exactly the nat "
              "footprint rows printed by another, and every Int.* footprint "
              "matches between the two.",
              "run-inventory-cross-check.json", "R:kernel-inventory-cross-check",
              "nat-names-agree",
              "This is the finding-dependent check behind the axiom-free "
              "statement: theorem_axiom_footprint's own exit status is "
              "completion-only, so it is used as data and never as evidence."),
        claim("claim-nat-footprints-empty",
              "Every Nat declaration has an empty axiom footprint",
              "Checked row by row against the per-declaration footprint column, "
              "not read off a summary line.",
              "run-inventory-cross-check.json", "R:kernel-inventory-cross-check",
              "nat-footprints-empty",
              "Each row's declared footprint size is also checked against the "
              "number of axioms actually listed on it, so a truncated column is a "
              "parse error rather than an axiom-free row."),
        prose("assumptions-heading", "What is assumed", level=2),
        prose("assumptions-body", (
            "The declarations this kernel takes on trust, named. A count is not "
            "an audit; the list is.")),
        table_from_run("assumptions", "run-nat-axiom-inventory.json",
                       "R:kernel-nat-axiom-inventory", "assumptions",
                       "Every declaration admitted without a checked proof body",
                       tag="detail", title="The assumptions, named"),
        block("kernel-admission", "essential", {
            "type": "certificate",
            "cert_kind": "kernel-admission",
            "summary": {"text": (
                "The pages under this index resolve every theorem name against "
                "the inventory snapshot below, which was produced by running the "
                "examples -- never by searching source, which returns zero "
                "matches for this kernel's declarations. Replay the census with "
                "the command shown; it re-asserts every number on this page and "
                "exits non-zero if any of them moved.")},
            "artifact_refs": [
                {"path": INVENTORY_REL,
                 "sha256": sha256_file(OUT_DIR / "kernel-inventory.json"),
                 "label": "theorem inventory snapshot",
                 "bytes": (OUT_DIR / "kernel-inventory.json").stat().st_size,
                 "media_type": "application/json"},
                {"path": ASSUMPTIONS_REL,
                 "sha256": sha256_file(OUT_DIR / "kernel-assumptions.json"),
                 "label": "trusted-surface snapshot",
                 "bytes": (OUT_DIR / "kernel-assumptions.json").stat().st_size,
                 "media_type": "application/json"},
                {"path": GENERATOR,
                 "sha256": sha256_file(Path(__file__).resolve()),
                 "label": "producer source",
                 "bytes": Path(__file__).resolve().stat().st_size,
                 "media_type": "text/x-python"},
            ],
            "replay": {"line": runs["trusted"].command, "cwd": ".",
                       "expected_exit_status": 0, "expected_seconds": 1},
            "evidence": [
                {"run_record": "run-nat-axiom-inventory.json",
                 "record_id": "R:kernel-nat-axiom-inventory", "role": "primary"},
                {"run_record": "run-inventory-cross-check.json",
                 "record_id": "R:kernel-inventory-cross-check",
                 "role": "replication",
                 "note": "Same kernel implementation, two independently built "
                         "environments and two tools; independence is in the "
                         "tools, not in the implementation."},
            ],
        }, prov=doc_prov, title="Replay the census"),
    ]
    docs.append((OUT_DIR / "kernel-trusted-base.doc.json", {
        "schema_version": 1,
        "meta": meta("kernel-trusted-base", "The trusted base",
                     "What this kernel has admitted, and what it still assumes",
                     "A census of the Axeyum kernel's preludes: 139 Nat theorems "
                     "and 57 derived Int declarations, all with empty axiom "
                     "footprints; an empty trusted surface for the logic, nat and "
                     "integer preludes; and 31 declarations that are assumed -- 30 "
                     "in the Real prelude and one in the string prelude -- listed "
                     "by name. Every figure is resolved from a recorded run of an "
                     "inventory example, because this kernel's declarations cannot "
                     "be read from source text."),
        "blocks": index_blocks,
        "provenance": doc_prov,
    }))

    # 2 and 3. The per-theorem pages.
    def theorem_page(doc_id: str, title: str, subtitle: str, abstract: str,
                     prelude: str, lead: str, rows: list[dict]) -> dict:
        blocks = [
            prose("intro", lead),
            prose("coverage", COVERAGE, tag="detail", title="Coverage"),
            prose("assembly-caveat", ASSEMBLY_CAVEAT, tag="detail",
                  title="Theorem rows only"),
            prose("statements-heading", "The statements", level=2),
            prose("statements-body",
                  "Each entry below is a checked reference into the inventory "
                  "snapshot: the type shown is the type the kernel admitted, "
                  "rendered by `Kernel::render_lean`, and a name the snapshot does "
                  "not carry is a build error rather than a blank."),
        ]
        seen_ids: dict[str, str] = {}
        for r in rows:
            bid = "thm-" + slugify(r["name"])
            if bid in seen_ids:
                raise ValueError(f"block id collision: {r['name']} and "
                                 f"{seen_ids[bid]} both slugify to {bid}")
            seen_ids[bid] = r["name"]
            blocks.append(statement_block(bid, r["name"], stmt_prov))
        return {
            "schema_version": 1,
            "meta": meta(doc_id, title, subtitle, abstract),
            "blocks": blocks,
            "provenance": doc_prov,
        }

    nat_rows = [d for d in decls if d["prelude"] == "nat"]
    int_rows = [d for d in decls if d["prelude"] == "integer"]

    docs.append((OUT_DIR / "kernel-nat-theorems.doc.json", theorem_page(
        "kernel-nat-theorems",
        "The Nat prelude, theorem by theorem",
        f"{len(nat_rows)} kernel-admitted theorems, each with the canonical type "
        f"the kernel accepted",
        f"Every theorem the Nat prelude admits, with the type as the kernel "
        f"holds it. All {len(nat_rows)} have an empty axiom footprint.",
        "nat",
        "The Nat development is where this project makes its strongest claim: a "
        "prelude with an empty trusted surface, every law derived. This page is "
        "that development enumerated. The types are quoted from the kernel, not "
        "from doc comments -- transcribing them from comments once produced three "
        "ledger entries the kernel would have rejected, two of them unparseable.",
        nat_rows)))

    docs.append((OUT_DIR / "kernel-int-theorems.doc.json", theorem_page(
        "kernel-int-theorems",
        "The integer prelude, declaration by declaration",
        f"{len(int_rows)} derived Int declarations, none of them asserted",
        f"Every derived Int.* declaration, with the type the kernel accepted. "
        f"The integer prelude asserted 34 of these once, then 1; it now asserts "
        f"none.",
        "integer",
        "The integer prelude used to be a list of assumptions. It is now a "
        "development: 57 declarations, all derived from the axiom-free Nat "
        "construction. The Nat development the construction rests on is not "
        "repeated here -- `int_theorem_inventory` filters to `Int.` names, and "
        "the rest is on the Nat page.",
        int_rows)))

    for path, doc in docs:
        write_json(path, doc)

    print(f"wrote {len(docs)} document(s), {len(records)} run record(s) and "
          f"2 snapshot(s) to {rel(OUT_DIR)}")
    for path, _ in docs:
        print(f"  {rel(path)}")
    for fname, _ in records.values():
        print(f"  {rel(OUT_DIR / fname)}")

    if args.no_validate:
        print("NOTICE: --no-validate given; the emitted files were NOT checked "
              "against the Doc-IR schema")
        return 0
    return validate(docs, records)


def validate(docs, records) -> int:
    if not VALIDATE_DOCIR.is_file() or not DOCIR_SCHEMA.is_file():
        print(f"error: {rel(VALIDATE_DOCIR)} or {rel(DOCIR_SCHEMA)} is missing, so "
              f"nothing was validated -- an unchecked emit is not a passing emit",
              file=sys.stderr)
        return 1
    doc_paths = [str(p) for p, _ in docs]
    rec_paths = [str(OUT_DIR / f) for f, _ in records.values()]
    status = 0
    for kind, paths in (("document", doc_paths), ("run-record", rec_paths)):
        proc = subprocess.run(
            [sys.executable, str(VALIDATE_DOCIR), "--kind", kind, *paths],
            capture_output=True, text=True)
        for line in (proc.stdout or "").splitlines()[-6:]:
            print(f"  validate-docir[{kind}]: {line}")
        if proc.returncode != 0:
            status = 1
            for line in (proc.stderr or proc.stdout).splitlines()[:20]:
                print(f"  {line}", file=sys.stderr)
            print(f"error: scripts/validate-docir.py exited {proc.returncode} on "
                  f"the emitted {kind}s", file=sys.stderr)
    return status


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--epoch-unix", type=int, default=None)
    ap.add_argument("--epoch-source", default="fixed",
                    choices=["commit", "source-date-epoch", "fixed"])
    ap.add_argument("--epoch-commit", default=None)
    ap.add_argument("--no-validate", action="store_true")
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args()
    try:
        return build(args)
    except (ValueError, AssertionError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Generate ledger facts for already-proved kernel theorems that nobody registered.

WHY THIS EXISTS. `scripts/gen-ledger-coverage.py` measured the gap on
2026-08-27: **1,397 kernel theorems, 474 registered, 923 unregistered.** Six
ledger batches before it each hand-picked and hand-wrote 12-30 facts. At that
rate the backlog is thirty more batches and it grows every time a lane lands a
theorem, so the deficiency is the registration PROCESS, not the queue length.

WHAT IS ACTUALLY FORMULAIC. For a `kernel-lean` fact about a theorem the kernel
has already admitted, nearly every field is a transcription of something a tool
already prints:

  * `formal.statement`   -- `kernel_declaration_projection`'s unfiltered emit
                            prints `Kernel::render_lean(declaration.ty())` as
                            the last TSV field of every declaration's row.
  * `formal.kernel_theorem` / `free_symbols` -- the same row's display name and
                            the binder names in that rendered type.
  * `depends_on`         -- the same row's DIRECT theorem-dependency column,
                            mapped through the ledger's own join and kept only
                            where the dependency is itself registered (the
                            convention the six hand-written batches already
                            use).
  * `axiom_footprint`    -- the same row's footprint size, cross-checked by a
                            whole-prelude `nat_axiom_inventory` run.
  * `epistemic_status`, `proof_route`, the two evidence rows and their
                            `checker_command`s -- one settled shape.

WHAT IS NOT FORMULAIC, AND IS THEREFORE REFUSED RATHER THAN FAKED
-----------------------------------------------------------------

This is the whole design problem. Bulk-generating 923 facts with formulaic
checkers is *precisely* how this repository's central audit finding gets
reproduced at scale: 40 of 162 checker runs exiting 0 on completion alone,
manufacturing unfalsifiable claims at full speed. Three things are withheld,
and each withholding is visible in the emitted file rather than implied:

1. **The mathematical characterisation.** A hand-written fact says "this bound
   is loose and does not pin the sign", "the global version is FALSE for an
   arbitrary witness", "domain-restricted". A generator cannot invent those and
   must not appear to. So generated `title` and `statement` are held to a
   TRANSCRIPTION vocabulary: they may name the theorem, its prelude, its
   admission gate and its measured footprint, and they may point at
   `formal.statement`. They may not characterise what the theorem SAYS. The
   generated `statement` states this restriction in its own text, so a reader
   who never opens this file still learns that no characterisation was
   attempted.

2. **The commentary.** `notes` says, in the emitted file, that no curated
   commentary exists and that its absence means nobody has looked -- not that
   there is nothing to say. Silence about a caveat is the failure mode; an
   explicit "unexamined" is not.

3. **`external_status`.** Whether mathematics-at-large knows a statement is a
   judgement about the literature, and this project has already cited Zenodo
   self-deposits as refereed results. The key is OMITTED, never guessed. The
   schema's own reading of an absent `external_status` -- "nobody has looked" --
   is exactly correct here.

THE PROVENANCE MARKER
---------------------

Every emitted fact carries, inside `provenance` (the one object in the schema
that is `additionalProperties: true`, and the semantically right home):

    "generated_by": "scripts/gen-kernel-facts.py"
    "curation":     "generated-unreviewed"

Two keys, not one, because they answer different questions and they DECOUPLE.
`generated_by` records what wrote the skeleton and stays true forever.
`curation` records whether a human or lane has vouched for the prose and the
notes. A later lane that enriches a generated fact with a real characterisation
flips `curation` to `curated` while `generated_by` remains accurate. Collapsing
the two into one key would force that lane either to delete a true provenance
statement or to leave an enriched fact indistinguishable from an unreviewed
one; both are worse.

`--audit` is the gate that makes the marker load-bearing rather than decorative.
For every fact marked `generated-unreviewed` it re-derives the prose this
generator would emit and requires a byte-identical match, requires
`external_status` to be absent, and requires each `checker_command` to match one
of the two shapes below. So hand-edited prose CANNOT sit under a
`generated-unreviewed` marker: enrichment is required to declare itself.

THE CHECKERS MUST BE ABLE TO FAIL
---------------------------------

Two evidence rows, both with an exit status that depends on the finding:

  * `theorem_dependency_inventory -- <Name> | grep -cE '^<Name>[[:space:]]'`
    Two independent failure modes. The example exits non-zero when a NAMED
    filter matches nothing (its own documented contract), and `grep -c` exits 1
    printing `0` when the anchored line is absent. `grep -c` is used rather than
    `grep -q` deliberately: `-q` exits at the first match and SIGPIPEs the
    producer, which under `set -o pipefail` reads as "not found". The anchor is
    the FULL display name followed by `[[:space:]]`, never `\t` -- in a scripted
    (GNU) grep `\t` is a literal `t`, and 54 facts / 68 checkers in this ledger
    were once wrong for exactly that reason.

  * `nat_axiom_inventory --require-axiom-free <prelude>`
    Exits non-zero if the prelude's trusted surface is not empty, and errors
    rather than silently passing for a prelude this run never built.

Neither is assumed. `--emit` is expected to be followed by running every emitted
command; `--print-checkers` prints them for exactly that purpose.

REFUSALS
--------

A theorem is DECLINED, with a reason printed, when:

  * its measured axiom footprint is non-zero -- this projection prints the
    footprint SIZE, not the names, so `axiom_footprint` could only be filled by
    guessing, and the whole point of the field is that it is measured;
  * the prelude is not in `PRELUDE_CONTRACT` -- that table is what says a
    falsifiable whole-prelude footprint checker exists for this label under
    `nat_axiom_inventory`'s own `ALWAYS_BUILT_PRELUDES`/`CONSTRUCTED_PRELUDES`;
  * its slug collides with an existing fact id, or with another theorem in the
    same batch;
  * its display name contains a numeric component (so `lean_pp` renders it with
    an `_` prefix in the type body) and the derived `_`-form namespace does NOT
    occur in that body -- meaning this script cannot confirm how the declaration
    is spelled inside its own statement;
  * its rendered type is empty, or its display name is not a plausible
    declaration name.

Refusals are counted and printed. A smaller honest batch beats a large
unfalsifiable one.

DETERMINISM
-----------

No wall-clock: `--date` is REQUIRED for `--emit`, so re-running the generator on
the same tree with the same date produces byte-identical files. Ordering is by
display name throughout; `depends_on` is sorted; JSON is written with a fixed
indent and a trailing newline.

USAGE
-----

    python3 scripts/gen-kernel-facts.py --prelude string --dry-run
    python3 scripts/gen-kernel-facts.py --prelude string --date 2026-08-27 --emit
    python3 scripts/gen-kernel-facts.py --prelude string --print-checkers
    python3 scripts/gen-kernel-facts.py --audit

`--projection-tsv <path>` substitutes a captured projection for the cargo call
and exists for tests and demonstrations; production usage never passes it.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
FACTS_DIR = ROOT / "artifacts" / "facts"

GENERATOR_ID = "scripts/gen-kernel-facts.py"
CURATION_GENERATED = "generated-unreviewed"
CURATION_CURATED = "curated"
CURATION_VALUES = (CURATION_GENERATED, CURATION_CURATED)

# Reuse the ledger's own join rather than re-deriving "which theorem is this
# fact about". Two copies of that question would silently diverge, which is the
# defect `gen-ledger-coverage.py` itself avoided by importing `theorem_of` from
# `check-fact-depends-derived.py`.
_COVERAGE_SPEC = importlib.util.spec_from_file_location(
    "_axeyum_ledger_coverage", ROOT / "scripts" / "gen-ledger-coverage.py"
)
assert _COVERAGE_SPEC is not None and _COVERAGE_SPEC.loader is not None
COVERAGE = importlib.util.module_from_spec(_COVERAGE_SPEC)
_COVERAGE_SPEC.loader.exec_module(COVERAGE)

PROJECTION_COMMAND = (
    "cargo run -q --release -p axeyum-lean-kernel "
    "--example kernel_declaration_projection"
)

# What this script knows how to write a FALSIFIABLE whole-prelude footprint
# checker for. The keys are `nat_axiom_inventory`'s own prelude labels; the
# `constructed` flag says whether that label needs `--include-constructed`.
# `fragment` is the fact schema's `formal.fragment` -- the theory that decides
# the statement.
#
# A prelude absent from this table is REFUSED rather than guessed at: without a
# label `nat_axiom_inventory` recognises, `--require-axiom-free <label>` errors,
# and a checker that errors for the wrong reason is not evidence.
PRELUDE_CONTRACT: dict[str, dict[str, Any]] = {
    "string": {
        "constructed": False,
        "fragment": "Str",
        "prelude_prose": "the free-monoid (string) prelude",
        "builder": "build_string_prelude",
        "source_dir": "crates/axeyum-lean-kernel/src/string_prelude/",
    },
    "logic": {
        "constructed": False,
        "fragment": "Prop",
        "prelude_prose": "the logic prelude",
        "builder": "build_logic_prelude",
        "source_dir": "crates/axeyum-lean-kernel/src/prelude/",
    },
    "nat": {
        "constructed": False,
        "fragment": "Nat",
        "prelude_prose": "the Nat prelude",
        "builder": "build_nat_prelude",
        "source_dir": "crates/axeyum-lean-kernel/src/nat_prelude/",
    },
    "integer": {
        "constructed": False,
        "fragment": "Int",
        "prelude_prose": "the Int prelude",
        "builder": "build_int_prelude",
        "source_dir": "crates/axeyum-lean-kernel/src/int_prelude/",
    },
    "rat": {
        "constructed": False,
        "fragment": "Rat",
        "prelude_prose": "the Rat prelude",
        "builder": "build_rat_prelude",
        "source_dir": "crates/axeyum-lean-kernel/src/rat_prelude/",
    },
    "creal": {
        "constructed": True,
        "fragment": "CReal",
        "prelude_prose": "the constructed-reals prelude",
        "builder": "build_creal_prelude",
        "source_dir": "crates/axeyum-lean-kernel/src/creal/",
    },
    "complex": {
        "constructed": True,
        "fragment": "Complex",
        "prelude_prose": "the constructed-complex prelude",
        "builder": "build_complex_prelude",
        "source_dir": "crates/axeyum-lean-kernel/src/complex/",
    },
    "cpoint": {
        "constructed": True,
        "fragment": "CPoint",
        "prelude_prose": "the constructed-plane prelude",
        "builder": "build_cpoint_prelude",
        "source_dir": "crates/axeyum-lean-kernel/src/cpoint/",
    },
}

DECLARATION_NAME_RE = re.compile(r"^[A-Za-z][A-Za-z0-9_.']*$")
BINDER_RE = re.compile(r"\(\s*([A-Za-z_][A-Za-z0-9_']*)\s*:")


class Declined(Exception):
    """A theorem this generator refuses to write a fact for, with the reason."""


# --------------------------------------------------------------------------
# projection
# --------------------------------------------------------------------------


class Row:
    """One `kernel_declaration_projection` TSV row, for a Theorem."""

    __slots__ = (
        "prelude",
        "kind",
        "name",
        "footprint",
        "type_deps",
        "decl_deps",
        "theorem_deps",
        "rendered_type",
    )

    def __init__(self, fields: list[str]) -> None:
        (
            self.prelude,
            self.kind,
            self.name,
            footprint,
            type_deps,
            decl_deps,
            theorem_deps,
            self.rendered_type,
        ) = fields
        self.footprint = int(footprint)
        self.type_deps = [d for d in type_deps.split(",") if d]
        self.decl_deps = [d for d in decl_deps.split(",") if d]
        self.theorem_deps = [d for d in theorem_deps.split(",") if d]


def parse_projection(stdout: str) -> list[Row]:
    """Parse the unfiltered projection into Theorem rows.

    Refuses zero rows. An empty projection is what a debug build's SIGABRT, a
    missing binary, or a silently-failed cargo invocation looks like, and
    "measured, and there was nothing to report" is the single most dangerous
    reading available here.
    """
    rows: list[Row] = []
    seen: dict[str, Row] = {}
    total = 0
    for line in stdout.splitlines():
        if not line.strip():
            continue
        fields = line.split("\t")
        if len(fields) != 8:
            raise SystemExit(
                f"gen-kernel-facts: ERROR: projection row has {len(fields)} fields, "
                f"expected 8: {line[:160]!r}"
            )
        total += 1
        if fields[1] != "theorem":
            continue
        row = Row(fields)
        previous = seen.get(row.name)
        if previous is not None:
            # The same theorem is reachable from several nested preludes. The
            # rendered type and footprint must agree; if they do not, the
            # underlying tool's output is internally inconsistent and this
            # script must not pick one arbitrarily.
            if (
                previous.rendered_type != row.rendered_type
                or previous.footprint != row.footprint
            ):
                raise SystemExit(
                    f"gen-kernel-facts: ERROR: {row.name} appears with disagreeing "
                    f"type or footprint across prelude groups "
                    f"({previous.prelude} vs {row.prelude})"
                )
            continue
        seen[row.name] = row
        rows.append(row)
    if total == 0:
        raise SystemExit(
            "gen-kernel-facts: ERROR: the declaration projection produced zero rows. "
            "That is what a debug build's stack overflow (exit 134) looks like, and "
            "it must not read as 'measured, nothing to report'. Run "
            f"`{PROJECTION_COMMAND}` directly and check its exit status."
        )
    rows.sort(key=lambda r: r.name)
    return rows


def run_projection() -> str:
    completed = subprocess.run(  # noqa: S603
        PROJECTION_COMMAND.split(),
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    if completed.returncode != 0:
        raise SystemExit(
            f"gen-kernel-facts: ERROR: `{PROJECTION_COMMAND}` exited "
            f"{completed.returncode}\n{completed.stderr[-4000:]}"
        )
    return completed.stdout


# --------------------------------------------------------------------------
# derivation
# --------------------------------------------------------------------------


def slug_for(name: str) -> str:
    """`axeyum.string.2.append_assoc` -> `F:string-append-assoc`.

    The `F:` id pattern is `[a-z0-9]+(-[a-z0-9]+)*`, so every non-alphanumeric
    run collapses to a single hyphen and the whole thing lowercases. The
    `axeyum.string.2.` namespace prefix carries no information a reader needs
    in an id -- every fact in the batch would repeat it -- so it collapses to
    `string`. Collisions are DETECTED, never silently merged.
    """
    trimmed = re.sub(r"^axeyum\.string\.\d+\.", "string.", name)
    body = re.sub(r"[^A-Za-z0-9]+", "-", trimmed).strip("-").lower()
    body = re.sub(r"-+", "-", body)
    return f"F:{body}"


def rendered_name_for(name: str) -> str:
    """The spelling `Kernel::render_lean` uses for `name` inside a type body.

    `lean_pp` prefixes an all-digit name component with `_`, because `foo.2`
    parses as a projection. This is a RULE, so it is applied and then CHECKED
    against the body (see `derive`), never trusted on its own.
    """
    return ".".join(
        f"_{part}" if part.isdigit() else part for part in name.split(".")
    )


def free_symbols_of(rendered_type: str) -> list[str]:
    """Binder names, in first-appearance order, deduplicated."""
    out: list[str] = []
    for match in BINDER_RE.finditer(rendered_type):
        symbol = match.group(1)
        if symbol not in out:
            out.append(symbol)
    return out


def checker_commands(name: str, prelude: str) -> tuple[str, str]:
    """The two evidence commands, both of which can FAIL.

    Anchored with `[[:space:]]`, never `\\t`: in a scripted (GNU) grep `\\t` is
    a literal `t`, and this ledger has already had 54 facts whose checkers were
    wrong for that reason. `grep -c` rather than `grep -q`, because `-q` exits
    on the first match and SIGPIPEs the producer.
    """
    contract = PRELUDE_CONTRACT[prelude]
    anchored = re.sub(r"([.\\^$*+?()\[\]{}|])", r"\\\1", name)
    kernel_cmd = (
        f"cargo run -q --release -p axeyum-lean-kernel --example "
        f"theorem_dependency_inventory -- {name} 2>/dev/null | "
        f"grep -cE '^{anchored}[[:space:]]'"
    )
    constructed = " --include-constructed" if contract["constructed"] else ""
    footprint_cmd = (
        f"cargo run -q --release -p axeyum-lean-kernel --example "
        f"nat_axiom_inventory --{constructed} --require-axiom-free {prelude}"
    )
    return kernel_cmd, footprint_cmd


def generated_title(name: str, prelude: str) -> str:
    return (
        f"[generated] kernel theorem {name} "
        f"({prelude} prelude, axiom-free, prose not curated)"
    )


def generated_statement(name: str, prelude: str) -> str:
    contract = PRELUDE_CONTRACT[prelude]
    return (
        f"MECHANICALLY GENERATED, UNREVIEWED PROSE -- this sentence deliberately "
        f"makes NO mathematical characterisation of the theorem. What is asserted, "
        f"and all that is asserted, is this: the kernel declaration `{name}` is a "
        f"`Declaration::Theorem` admitted into the environment by "
        f"`{contract['builder']}` through the trusted `Kernel::add_declaration` "
        f"gate, which re-derives its type from its proof term; its type is "
        f"recorded verbatim in `formal.statement`; and its axiom footprint, as "
        f"computed by `Kernel::axiom_footprint`, is empty. The authoritative "
        f"content of this fact is `formal.statement`. A human-readable "
        f"characterisation of what {name} SAYS has not been supplied, because a "
        f"generator cannot supply one honestly -- see `notes`."
    )


def generated_notes(name: str, prelude: str, rendered_name: str) -> str:
    contract = PRELUDE_CONTRACT[prelude]
    spelling = ""
    if rendered_name != name:
        spelling = (
            f" NAME SPELLING: `formal.statement`'s header names this declaration "
            f"`{name}` (its `Kernel::display_name`), while the type body spells the "
            f"same namespace `{rendered_name.rsplit('.', 1)[0]}.` -- `lean_pp` "
            f"prefixes an all-digit name component with `_` on export, since "
            f"`foo.2` would otherwise parse as a projection. The two spellings "
            f"denote one declaration; this was verified by requiring the `_`-form "
            f"namespace to occur in the rendered type, not assumed."
        )
    return (
        f"NO CURATED COMMENTARY EXISTS FOR THIS FACT. Its absence means nobody has "
        f"looked, NOT that there is nothing to say. A hand-written fact in this "
        f"ledger typically records what a generator cannot invent -- that a bound "
        f"is loose and does not pin a sign, that the global version of a statement "
        f"is false for an arbitrary witness, that a hypothesis is domain-restricted, "
        f"which of several attempted slices finally closed a gap. None of that has "
        f"been assessed here. `provenance.curation` is `{CURATION_GENERATED}`; a "
        f"lane that enriches this fact must flip it to `{CURATION_CURATED}`, which "
        f"`gen-kernel-facts.py --audit` enforces by re-deriving this prose and "
        f"requiring a byte-identical match while the marker says generated. "
        f"`external_status` is deliberately ABSENT rather than guessed: whether "
        f"mathematics-at-large knows this statement is a judgement about the "
        f"literature, and the schema reads an absent `external_status` as 'nobody "
        f"has looked', which is exactly the case. Source: "
        f"{contract['source_dir']}.{spelling}"
    )


def derive(
    row: Row,
    prelude: str,
    date: str,
    registered_ids: dict[str, str],
) -> dict[str, Any]:
    """Build one fact document, or raise `Declined` with the reason.

    `registered_ids` maps a kernel theorem name to the fact id registering it,
    and must already include this batch, so within-batch dependency edges
    resolve.
    """
    contract = PRELUDE_CONTRACT.get(prelude)
    if contract is None:
        raise Declined(
            f"prelude {prelude!r} is not in PRELUDE_CONTRACT, so no falsifiable "
            f"whole-prelude footprint checker is known for it"
        )
    if not DECLARATION_NAME_RE.match(row.name):
        raise Declined(f"display name {row.name!r} is not a plausible declaration name")
    if not row.rendered_type.strip():
        raise Declined("rendered type is empty, so formal.statement would be a stub")
    if row.footprint != 0:
        raise Declined(
            f"axiom footprint size is {row.footprint}, not 0. This projection prints "
            f"the SIZE, not the axiom NAMES, so axiom_footprint could only be filled "
            f"by guessing -- and the whole value of that field is that it is measured"
        )

    rendered_name = rendered_name_for(row.name)
    if rendered_name != row.name:
        namespace = rendered_name.rsplit(".", 1)[0] + "."
        if namespace not in row.rendered_type:
            raise Declined(
                f"display name {row.name!r} has a numeric component, so the type body "
                f"should spell its namespace {namespace!r}, but that string does not "
                f"occur in the rendered type -- this script cannot confirm how the "
                f"declaration is spelled inside its own statement"
            )

    fact_id = slug_for(row.name)
    kernel_cmd, footprint_cmd = checker_commands(row.name, prelude)

    depends_on = sorted(
        {
            registered_ids[dep]
            for dep in row.theorem_deps
            if dep in registered_ids and registered_ids[dep] != fact_id
        }
    )
    omitted = sorted(d for d in row.theorem_deps if d not in registered_ids)

    notes = generated_notes(row.name, prelude, rendered_name)
    if omitted:
        notes += (
            f" DEPENDENCY EDGES OMITTED: {', '.join(omitted)} are direct theorem "
            f"dependencies per this projection's own theorem-dependency column, but "
            f"none is registered in this ledger, and `depends_on` may only name facts "
            f"that exist. They are unregistered {prelude}-prelude theorems, not "
            f"axioms -- the prelude's trusted surface is 0, per the footprint "
            f"evidence below."
        )

    return {
        "schema_version": 1,
        "id": fact_id,
        "title": generated_title(row.name, prelude),
        "statement": generated_statement(row.name, prelude),
        "formal": {
            "language": "lean4",
            "statement": f"theorem {row.name} : {row.rendered_type}",
            "fragment": contract["fragment"],
            "free_symbols": free_symbols_of(row.rendered_type),
            "kernel_theorem": row.name,
        },
        "epistemic_status": "proved",
        "proof_route": "kernel-lean",
        "depends_on": depends_on,
        "axiom_footprint": [],
        "evidence": [
            {
                "id": f"kernel-{row.name}",
                "kind": "kernel-term",
                "supports": (
                    f"{row.name} is admitted by the trusted kernel gate with the type "
                    f"recorded in formal.statement."
                ),
                "check_status": "checked",
                "checkers": [
                    "producing-build (Kernel::add_declaration)",
                    "theorem_dependency_inventory re-list",
                ],
                "checker_command": kernel_cmd,
                "checker_seconds": 10,
                "kernel_declaration": row.name,
                "notes": (
                    "Two independent failure modes, so the exit status depends on the "
                    "finding rather than on the run completing: "
                    "theorem_dependency_inventory exits non-zero when a NAMED filter "
                    "matches nothing, and grep -c exits 1 printing 0 when the anchored "
                    "line is absent. Anchored with [[:space:]], never \\t -- in a "
                    "scripted (GNU) grep \\t is a literal t. grep -c rather than "
                    "grep -q, which would SIGPIPE the producer under pipefail. "
                    "--release is MANDATORY: this tool builds creal/complex/cpoint, "
                    "which overflow the default debug thread stack."
                ),
            },
            {
                "id": f"footprint-{row.name}",
                "kind": "exhaustive-enumeration",
                "supports": (
                    f"axiom_footprint: [] -- the {prelude} prelude's trusted surface is "
                    f"empty, which bounds {row.name}."
                ),
                "check_status": "checked",
                "checkers": [
                    "Kernel::axiom_footprint",
                    "environment-wide trusted-surface enumeration",
                ],
                "checker_command": footprint_cmd,
                "checker_seconds": 12,
                "notes": (
                    f"--require-axiom-free exits non-zero when the named prelude's "
                    f"trusted surface (Axiom + Opaque + Quotient) is not empty, and "
                    f"errors rather than silently passing for a prelude the run never "
                    f"built. A declaration cannot depend on a trusted declaration the "
                    f"environment does not contain, so an empty {prelude} surface "
                    f"bounds every declaration in it, including {row.name}. This is a "
                    f"whole-prelude bound, not a per-declaration measurement; the "
                    f"per-declaration figure is the footprint column of "
                    f"kernel_declaration_projection, measured 0 for this row."
                ),
            },
        ],
        "provenance": {
            "date": date,
            "curation": CURATION_GENERATED,
            "generated_by": GENERATOR_ID,
            "established_by": (
                f"axeyum-lean-kernel {contract['builder']} "
                f"({contract['source_dir']})"
            ),
            "source": (
                f"Derived mechanically from the unfiltered emit of "
                f"`{PROJECTION_COMMAND}`, which prints one TSV row per declaration "
                f"whose fields are (prelude, kind, display name, axiom-footprint size, "
                f"direct type declarations, direct declarations, direct theorems, "
                f"Kernel::render_lean(declaration.ty())). formal.statement is that "
                f"last field verbatim; depends_on is the direct-theorem column "
                f"intersected with this ledger's registered facts; axiom_footprint is "
                f"the footprint-size column, cross-checked by the whole-prelude "
                f"nat_axiom_inventory run recorded in the second evidence row. No "
                f"field was hand-transcribed and no prose was authored."
            ),
        },
        "notes": notes,
    }


# --------------------------------------------------------------------------
# batch
# --------------------------------------------------------------------------


def registered_map() -> dict[str, str]:
    """kernel theorem name -> fact id, for facts the ledger already registers.

    Uses `gen-ledger-coverage.py`'s own three-tier resolution, so "which theorem
    is this fact about" has exactly one definition in this repository.
    """
    out: dict[str, str] = {}
    for fact in COVERAGE.load_facts().values():
        if fact.get("proof_route") not in COVERAGE.KERNEL_ROUTES:
            continue
        if fact.get("epistemic_status") not in COVERAGE.OURS_ESTABLISHED:
            continue
        name, _tier = COVERAGE.resolve_theorem_name(fact)
        if name:
            out.setdefault(name, fact["id"])
    return out


def fact_path(fact_id: str) -> Path:
    return FACTS_DIR / (fact_id.replace("F:", "F-", 1) + ".json")


def render(fact: dict[str, Any]) -> str:
    return json.dumps(fact, indent=2, ensure_ascii=False, sort_keys=False) + "\n"


def build_batch(
    rows: list[Row], prelude: str, date: str
) -> tuple[list[dict[str, Any]], list[tuple[str, str]]]:
    """Return (facts, declined) for `prelude`, in display-name order."""
    already = registered_map()
    existing_ids = {p.stem.replace("F-", "F:", 1) for p in FACTS_DIR.glob("*.json")}

    candidates = [r for r in rows if COVERAGE.prelude_of(r.name) == prelude]
    unregistered = [r for r in candidates if r.name not in already]

    declined: list[tuple[str, str]] = []

    # Two passes. The first fixes the batch's id assignment (so within-batch
    # dependency edges resolve); the second builds the documents against it.
    # A theorem declined in pass one must not appear in pass two's id map, or a
    # surviving fact would declare a dependency on a file that was never
    # written.
    planned: dict[str, str] = {}
    claimed: dict[str, str] = {}
    survivors: list[Row] = []
    for row in unregistered:
        try:
            fact_id = slug_for(row.name)
            if fact_id in existing_ids:
                raise Declined(
                    f"slug {fact_id} collides with an existing fact file; a generated "
                    f"fact must never overwrite a curated one"
                )
            if fact_id in claimed:
                raise Declined(
                    f"slug {fact_id} collides with {claimed[fact_id]} in this same "
                    f"batch; two theorems cannot share one fact id"
                )
            # Everything else that can decline, decided now, so the id map holds
            # only theorems that will actually be written.
            derive(row, prelude, date, {})
        except Declined as exc:
            declined.append((row.name, str(exc)))
            continue
        claimed[fact_id] = row.name
        planned[row.name] = fact_id
        survivors.append(row)

    registered_ids = dict(already)
    registered_ids.update(planned)

    facts = [derive(row, prelude, date, registered_ids) for row in survivors]
    facts.sort(key=lambda f: f["id"])
    return facts, declined


# --------------------------------------------------------------------------
# audit
# --------------------------------------------------------------------------

ALLOWED_CHECKER_SHAPES = (
    re.compile(
        r"^cargo run -q --release -p axeyum-lean-kernel --example "
        r"theorem_dependency_inventory -- \S+ 2>/dev/null \| grep -cE "
        r"'\^\S+\[\[:space:\]\]'$"
    ),
    re.compile(
        r"^cargo run -q --release -p axeyum-lean-kernel --example "
        r"nat_axiom_inventory --( --include-constructed)? --require-axiom-free "
        r"[a-z]+$"
    ),
)


def audit() -> list[str]:
    """Re-assert the invariants every `generated-unreviewed` fact must hold.

    This is what makes the provenance marker load-bearing. Without it the marker
    is a string nobody reads, and hand-written prose could sit under it
    indefinitely -- which would make "generated" and "curated" indistinguishable
    again, the exact thing the marker exists to prevent.
    """
    problems: list[str] = []
    generated = 0
    curated_from_generated = 0
    for path in sorted(FACTS_DIR.glob("*.json")):
        try:
            fact = json.loads(path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as exc:
            problems.append(f"{path.name}: not valid JSON ({exc})")
            continue
        provenance = fact.get("provenance") or {}
        if provenance.get("generated_by") != GENERATOR_ID:
            if provenance.get("curation") in CURATION_VALUES:
                problems.append(
                    f"{fact.get('id')}: provenance.curation is set but "
                    f"provenance.generated_by is not {GENERATOR_ID!r} -- the curation "
                    f"marker is defined only for generated facts"
                )
            continue
        curation = provenance.get("curation")
        if curation not in CURATION_VALUES:
            problems.append(
                f"{fact.get('id')}: provenance.curation {curation!r} is not one of "
                f"{list(CURATION_VALUES)}"
            )
            continue
        if curation == CURATION_CURATED:
            curated_from_generated += 1
            continue
        generated += 1
        fid = fact.get("id")

        name = (fact.get("formal") or {}).get("kernel_theorem")
        prelude = COVERAGE.prelude_of(name) if name else None
        if not name or prelude not in PRELUDE_CONTRACT:
            problems.append(
                f"{fid}: generated fact must name formal.kernel_theorem in a prelude "
                f"this generator contracts for (got {name!r})"
            )
            continue

        rendered_name = rendered_name_for(name)
        expected_title = generated_title(name, prelude)
        expected_statement = generated_statement(name, prelude)
        expected_notes_head = generated_notes(name, prelude, rendered_name).split(
            " DEPENDENCY EDGES OMITTED:"
        )[0]
        if fact.get("title") != expected_title:
            problems.append(
                f"{fid}: title is not what the generator emits, but "
                f"provenance.curation is still {CURATION_GENERATED!r}. Enriched prose "
                f"must declare itself by flipping curation to {CURATION_CURATED!r}."
            )
        if fact.get("statement") != expected_statement:
            problems.append(
                f"{fid}: statement is not what the generator emits, but "
                f"provenance.curation is still {CURATION_GENERATED!r}."
            )
        if not (fact.get("notes") or "").startswith(expected_notes_head):
            problems.append(
                f"{fid}: notes no longer carry the generated no-curation disclosure, "
                f"but provenance.curation is still {CURATION_GENERATED!r}."
            )
        if "external_status" in fact:
            problems.append(
                f"{fid}: a generated fact must not carry external_status -- whether "
                f"mathematics-at-large knows a statement is a judgement about the "
                f"literature and this generator does not make it."
            )
        for ev in fact.get("evidence", []):
            cmd = ev.get("checker_command") or ""
            if not any(shape.match(cmd) for shape in ALLOWED_CHECKER_SHAPES):
                problems.append(
                    f"{fid}: evidence {ev.get('id')!r} checker_command does not match "
                    f"a shape whose exit status depends on the finding: {cmd!r}"
                )
    print(
        f"gen-kernel-facts --audit: {generated} generated-unreviewed, "
        f"{curated_from_generated} generated-then-curated, "
        f"{len(problems)} problem(s)"
    )
    return problems


# --------------------------------------------------------------------------
# main
# --------------------------------------------------------------------------


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--prelude", help="prelude label to generate for")
    parser.add_argument(
        "--date",
        help="provenance date, YYYY-MM-DD. REQUIRED for --emit: no wall-clock is "
        "read, so the generator is reproducible.",
    )
    parser.add_argument(
        "--projection-tsv",
        type=Path,
        help="use a captured kernel_declaration_projection emit instead of running "
        "cargo. For tests and demonstrations; production never passes it.",
    )
    parser.add_argument("--emit", action="store_true", help="write the fact files")
    parser.add_argument(
        "--print-checkers",
        action="store_true",
        help="print each planned fact's checker_commands, one per line, so they can "
        "be executed rather than assumed",
    )
    parser.add_argument(
        "--audit",
        action="store_true",
        help="re-assert the invariants of every generated fact already on disk",
    )
    args = parser.parse_args()

    if args.audit:
        problems = audit()
        for problem in problems:
            print(f"  {problem}", file=sys.stderr)
        return 1 if problems else 0

    if not args.prelude:
        parser.error("--prelude is required unless --audit is given")
    if args.prelude not in PRELUDE_CONTRACT:
        print(
            f"gen-kernel-facts: ERROR: prelude {args.prelude!r} is not in "
            f"PRELUDE_CONTRACT ({', '.join(sorted(PRELUDE_CONTRACT))}). A prelude with "
            f"no falsifiable whole-prelude footprint checker is refused, not guessed.",
            file=sys.stderr,
        )
        return 2
    if args.emit and not args.date:
        parser.error("--emit requires --date (no wall-clock is read)")

    stdout = (
        args.projection_tsv.read_text(encoding="utf-8")
        if args.projection_tsv
        else run_projection()
    )
    rows = parse_projection(stdout)
    facts, declined = build_batch(rows, args.prelude, args.date or "0000-00-00")

    if args.print_checkers:
        for fact in facts:
            for ev in fact["evidence"]:
                print(ev["checker_command"])
        return 0

    total = sum(1 for r in rows if COVERAGE.prelude_of(r.name) == args.prelude)
    print(
        f"gen-kernel-facts: prelude={args.prelude} kernel_theorems={total} "
        f"planned={len(facts)} declined={len(declined)}"
    )
    for name, reason in declined:
        print(f"  DECLINED {name}: {reason}")

    if not args.emit:
        for fact in facts:
            print(f"  would write {fact_path(fact['id']).name}")
        return 0

    for fact in facts:
        fact_path(fact["id"]).write_text(render(fact), encoding="utf-8")
    print(f"gen-kernel-facts: wrote {len(facts)} fact(s) to {FACTS_DIR}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

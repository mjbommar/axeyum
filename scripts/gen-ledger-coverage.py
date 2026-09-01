#!/usr/bin/env python3
"""Measure how far `artifacts/facts/` trails the kernel's own theorem inventory.

WHY THIS EXISTS. `docs/plan/status/141-ledger-6-backlog.md` registered its
12-fact backlog and then said, explicitly: nobody has run the full diff of
`prelude_theorem_inventory --include-constructed`'s theorem list against the
ledger's registered names, and a future lane should -- "report its size as
the headline trailing-the-kernel measurement". Six ledger batches before that
one each hand-picked a short list to register and none of them measured the
gap between "proved" and "claimed". This script is that measurement, made
permanent rather than taken once: `--check` fails when the gap changes
without the ledger changing to match, so a newly-admitted kernel theorem
cannot silently stay unregistered forever.

# The denominator -- the design content, not a detail

The population counted is **every distinct `Declaration::Theorem` in the
kernel**, across every constructed prelude (`prelude_theorem_inventory
--include-constructed`, which already excludes `Axiom`, `Definition`,
`Opaque`, `Inductive`, `Constructor`, `Recursor` and `Quotient` by
construction -- see that tool's own module doc). That exclusion is
deliberate and is the rule this script inherits rather than re-derives:

* `Axiom` -- not proved by us; the opposite of what this ledger claims.
* `Definition` -- a construction (`CReal.integral`, `CReal.e`), not a
  proposition. A referee is shown a definition exists, not that it is
  "true"; `formal.kernel_theorem` on the fact schema is itself named for
  theorems, and a definition-shaped fact (rare) is out of scope here.
* `Inductive` / `Constructor` / `Recursor` -- structural scaffolding the
  kernel generates from a type declaration. Nobody would register
  `Nat.rec` as a claimed result.

So `Declaration::Theorem` is the population "a referee would expect to see
claimed": every named lemma and theorem this kernel has type-checked,
axiom-free, with nothing excluded on any OTHER basis (no size cutoff, no
namespace exclusion, no "internal-looking name" heuristic -- measured
2026-08-27, the distinct theorem set contains no `_proof_*`-shaped
auto-generated names, so no such filter is needed or applied).

This is a **conservative** denominator, not a generous one: an ADR-0509-style
package fact (`external_status`-shaped, `formal.kernel_theorem: null`) can
cover several kernel theorems worth of ground behind one registration, and
that population intersects the denominator through the SAME extraction path
as everything else. The gap this script reports is therefore, if anything,
an overcount of what remains -- consistent with the finding being trusted
downward, not exaggerated.

# Per-prelude bucketing -- by NAMESPACE, not by which `build_*_prelude`
# happened to be asked for it

`prelude_theorem_inventory`'s own per-group counts are cumulative: `creal`,
`complex` and `cpoint` each build the FULL nested prelude stack from scratch,
so a `Nat.*` theorem appears in six of the nine printed groups and using the
raw `label` column would count it six times. The tool's own "origination"
attribution (minimal-count group, ties broken by build order) fixes that, but
replicating it here would mean re-deriving a second, more fragile copy of an
algorithm this script does not own.

Bucketing by the theorem's own dotted namespace prefix is simpler, owned
entirely by this file, and arguably MORE legible to a reader: it says which
package's development produced the name printed in the fact itself
(`formal.kernel_theorem`), not which prelude build order happened to reach it
first. See `NAMESPACE_TO_PRELUDE` below for the exact map; anything with no
recognised namespace (the `logic` prelude's bare names -- `mt`,
`demorgan_not_or`, `Or.inl`, `Decidable.em`, ...) buckets to `logic`, and the
`string` prelude's `axeyum.string.2.*` names get their own case since they
carry no capitalised namespace segment at all.

# The join -- three tiers, because the first two both undercount alone

A fact is "about" a kernel theorem through the first of these that applies:

1. `formal.kernel_theorem`, when the KEY IS PRESENT (including an explicit
   `null`, meaning "no single subject" -- see
   `check-fact-depends-derived.py::theorem_of`'s own docstring for the two
   collisions that motivated the field). A present `null` stops here: it
   must NOT fall through to the tiers below.
2. The declared name at the HEAD of `formal.statement`, when
   `formal.language == "lean4"` -- `Kernel::render_lean` renders a theorem
   as `theorem <Name> : <type>` (and a definition as `def <Name> : <type>`,
   which legitimately will not appear in the theorem denominator -- see
   `registered_kernel_theorems_not_in_denominator`), and some facts drop the
   `theorem `/`def ` keyword and store `<Name> : <type>` directly. Both
   shapes are matched. THIS TIER WAS NECESSARY, NOT OPTIONAL: measured on
   this tree, using only tier 1 + the borrowed tier-3 regex left the
   `logic` prelude at 2/32 "registered" and `string` at 0/64 -- both
   fictitious near-zeroes. The cause is that tier 3's namespace allowlist
   (below) omits `And`, `Or`, `Iff`, `Decidable`, `Eq` and every BARE
   (non-namespaced) logic-prelude name (`mt`, `demorgan_not_or`, ...), so a
   fact like `F:logic-and-left` (subject `And.left`) could never resolve
   through it. Parsing the fact's own declared name sidesteps the allowlist
   entirely.
3. The first dotted theorem name matched in the fact's own
   `evidence[].checker_command`s -- the exact `theorem_of` function
   `check-fact-depends-derived.py` already uses, imported here rather than
   re-implemented so the two checkers cannot silently diverge on what "the
   fact's subject" means when tiers 1-2 both come up empty (e.g. a
   `lean4-surface` statement using Unicode notation, or a `formal.statement`
   that is the raw type body with no leading name at all).

A fact still unresolved after all three tiers is reported, not guessed at
-- see `join.unresolved_fact_ids`. Only facts with `proof_route ==
"kernel-lean"` and `epistemic_status` in `{proved, computed}` are joined at
all -- an `open` or `smt-term-level` fact makes no claim this kernel's
environment could corroborate.

Regenerate with `python3 scripts/gen-ledger-coverage.py`; `--check` fails when
the committed artifact differs from a fresh generation, mirroring
`scripts/gen-plan.py --check` / `scripts/gen-import-backlog.py --check`.

# Testing hook -- `--theorem-tsv`

Invoking the real measurement means a `--release` cargo build of every
constructed prelude (`prelude_theorem_inventory --include-constructed`,
~10s warm). `--theorem-tsv <path>` substitutes a file in that tool's own
TSV shape for the cargo call, so unit tests (and the demonstration that
`--check` goes red on a newly-admitted, unregistered theorem -- see
`docs/autogenesis/297-ledger-coverage-gate.md`) never need a build.
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
OUTPUT = ROOT / "artifacts" / "ledger-coverage.json"

INVENTORY_COMMAND = (
    "cargo run --quiet --release -p axeyum-lean-kernel "
    "--example prelude_theorem_inventory -- --include-constructed"
)

# Reuse the sibling checker's fact-to-theorem extraction verbatim, rather than
# re-typing the regex and the `formal.kernel_theorem`-precedence rule -- a
# second, slightly different implementation of "which theorem is this fact
# about" is exactly the kind of silent divergence CLAUDE.md warns about.
_DEPENDS_SPEC = importlib.util.spec_from_file_location(
    "check_fact_depends_derived", ROOT / "scripts" / "check-fact-depends-derived.py"
)
assert _DEPENDS_SPEC is not None and _DEPENDS_SPEC.loader is not None
DEPENDS_DERIVED = importlib.util.module_from_spec(_DEPENDS_SPEC)
_DEPENDS_SPEC.loader.exec_module(DEPENDS_DERIVED)

KERNEL_ROUTES = DEPENDS_DERIVED.KERNEL_ROUTES
THEOREM_OF_CHECKER_COMMAND = DEPENDS_DERIVED.theorem_of
OURS_ESTABLISHED = {"proved", "computed"}

# Tier 2: the declared name at the head of a `lean4` `formal.statement`.
# Optional `theorem `/`def `/`axiom ` keyword, then the identifier, then the
# top-level `:`. See module docstring for why this tier is load-bearing
# rather than a nicety.
STATEMENT_NAME_RE = re.compile(r"^(?:theorem\s+|def\s+|axiom\s+)?([A-Za-z][A-Za-z0-9_.']*)\s*:")


def is_curated(fact: dict[str, Any]) -> bool:
    """True if the fact is curated (not marked as generated-unreviewed).

    Facts without a curation field are counted as curated (they were
    deliberately hand-written before the field was introduced).
    """
    provenance = fact.get("provenance") or {}
    curation = provenance.get("curation")
    # If curation field is missing or not "generated-unreviewed", it's curated
    return curation != "generated-unreviewed"


def resolve_theorem_name(fact: dict[str, Any]) -> tuple[str | None, str | None]:
    """`(name, tier)` -- `tier` is `"field"`, `"statement"` or
    `"checker_command"` when `name` is not None, else `None`.
    """
    formal = fact.get("formal") or {}
    if "kernel_theorem" in formal:
        value = formal["kernel_theorem"]
        return (value, "field") if isinstance(value, str) else (None, None)
    if formal.get("language") == "lean4":
        match = STATEMENT_NAME_RE.match(formal.get("statement", ""))
        # `F:real-lattice-is-constructed-axiom-free` carries the literal
        # placeholder statement "TODO: the formal statement, precise enough
        # to dispatch" -- which this regex otherwise happily parses as a
        # declared name "TODO". No real kernel declaration is rendered
        # ALL-CAPS (the shortest namespaces are `Nat`/`Int`/`Rat`, Titlecase),
        # so this guard is specific to the placeholder shape rather than to
        # one fact id.
        if match and not match.group(1).isupper():
            return match.group(1), "statement"
    name = THEOREM_OF_CHECKER_COMMAND(fact)
    if name is not None:
        return name, "checker_command"
    return None, None

SCHEMA_VERSION = 1

# Namespace prefix -> owning prelude label. See module doc: this is a
# deliberate, simpler substitute for `prelude_theorem_inventory`'s own
# cumulative-group "origination" attribution.
NAMESPACE_TO_PRELUDE = {
    "CReal": "creal",
    "Complex": "complex",
    "CPoint": "cpoint",
    "Nat": "nat",
    "Int": "integer",
    "Rat": "rat",
    "AxReal": "axreal",
}


class CoverageError(Exception):
    pass


def prelude_of(name: str) -> str:
    """Which prelude a kernel theorem NAME belongs to, by its own namespace.

    `axeyum.string.2.*` (the string prelude's own rendering, no capitalised
    namespace segment) is checked first since a plain `split(".", 1)` on it
    would yield `axeyum`, which matches nothing in `NAMESPACE_TO_PRELUDE` and
    would otherwise silently fall through to `logic` -- wrong, and exactly
    the kind of silent misclassification this function exists to avoid.

    `ipc_*` (the intuitionistic-propositional-calculus soundness package) is
    the same shape: flat, lowercase, no dotted namespace segment, so it too
    would fall through to `logic` unless checked explicitly. This prelude
    was added to `prelude_theorem_inventory` on 2026-08-31; before this fix
    its ~16 theorems were silently counted as `logic`'s.
    """
    if name.startswith("axeyum.string."):
        return "string"
    if name.startswith("ipc_"):
        return "ipc"
    head = name.split(".", 1)[0]
    return NAMESPACE_TO_PRELUDE.get(head, "logic")


def parse_theorem_inventory(stdout: str) -> dict[str, int]:
    """`{theorem name: axiom-footprint size}`, deduplicated over every printed
    row regardless of which (cumulative, nested) prelude group printed it.

    Each row is `label\\ttheorem\\tfootprint-size\\taxioms-csv`. A theorem's
    footprint size must agree everywhere it is printed -- it is the SAME
    kernel declaration reached through different nested prelude builds, and a
    disagreement would mean the tool's own output is internally inconsistent,
    not that this script should pick one arbitrarily.
    """
    footprints: dict[str, int] = {}
    for line in stdout.splitlines():
        if not line.strip():
            continue
        fields = line.split("\t")
        if len(fields) < 3:
            raise CoverageError(f"malformed theorem-inventory row: {line!r}")
        name = fields[1]
        try:
            size = int(fields[2])
        except ValueError as error:
            raise CoverageError(f"malformed footprint size in row: {line!r}") from error
        previous = footprints.get(name)
        if previous is not None and previous != size:
            raise CoverageError(
                f"{name}: footprint size disagrees across prelude groups "
                f"({previous} vs {size}) -- the inventory tool's own output "
                "is internally inconsistent"
            )
        footprints[name] = size
    if not footprints:
        raise CoverageError(
            "theorem inventory produced zero rows -- either the tool was not "
            "run with --include-constructed, or a debug build SIGABRTed "
            "(prelude_theorem_inventory MUST run --release)"
        )
    return footprints


def run_inventory() -> str:
    completed = subprocess.run(
        INVENTORY_COMMAND.split(),
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=1800,
        check=False,
    )
    if completed.returncode != 0:
        raise CoverageError(
            f"theorem inventory command failed ({completed.returncode}): "
            f"{INVENTORY_COMMAND}: {completed.stderr.strip()}"
        )
    return completed.stdout


def load_facts() -> dict[str, dict[str, Any]]:
    facts: dict[str, dict[str, Any]] = {}
    for path in sorted(FACTS_DIR.glob("*.json")):
        try:
            fact = json.loads(path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as exc:
            raise CoverageError(f"{path.name}: not valid JSON: {exc}") from exc
        fid = fact.get("id")
        if fid:
            facts[fid] = fact
    return facts


class JoinResult:
    def __init__(self) -> None:
        # theorem name -> sorted list of fact ids claiming it
        self.registered: dict[str, list[str]] = {}
        # theorem name -> sorted list of fact ids with curated provenance
        self.curated: dict[str, list[str]] = {}
        self.facts_scanned = 0
        self.kernel_route_established = 0
        self.via_field = 0
        self.via_statement = 0
        self.via_checker_command = 0
        self.unresolved: list[str] = []
        self.curated_facts = 0
        self.unreviewed_facts = 0


def join(facts: dict[str, dict[str, Any]]) -> JoinResult:
    result = JoinResult()
    for fid in sorted(facts):
        fact = facts[fid]
        result.facts_scanned += 1
        if fact.get("proof_route") not in KERNEL_ROUTES:
            continue
        if fact.get("epistemic_status") not in OURS_ESTABLISHED:
            continue
        result.kernel_route_established += 1
        name, tier = resolve_theorem_name(fact)
        if name is None:
            result.unresolved.append(fid)
            continue
        if tier == "field":
            result.via_field += 1
        elif tier == "statement":
            result.via_statement += 1
        else:
            result.via_checker_command += 1
        result.registered.setdefault(name, []).append(fid)

        # Track curated facts separately
        if is_curated(fact):
            result.curated.setdefault(name, []).append(fid)
            result.curated_facts += 1
        else:
            result.unreviewed_facts += 1

    for names in result.registered.values():
        names.sort()
    for names in result.curated.values():
        names.sort()
    return result


def build_document(footprints: dict[str, int], join_result: JoinResult) -> dict[str, Any]:
    by_prelude: dict[str, dict[str, Any]] = {}
    for name in footprints:
        by_prelude.setdefault(
            prelude_of(name), {"kernel_theorems": 0, "registered": [], "unregistered": []}
        )

    for name in sorted(footprints):
        bucket = by_prelude[prelude_of(name)]
        bucket["kernel_theorems"] += 1
        if name in join_result.registered:
            bucket["registered"].append(name)
        else:
            bucket["unregistered"].append(name)

    by_prelude_out: dict[str, Any] = {}
    for prelude in sorted(by_prelude):
        bucket = by_prelude[prelude]
        # Count curated facts within this prelude's registered
        curated_in_prelude = sum(
            1 for name in bucket["registered"]
            if name in join_result.curated
        )
        by_prelude_out[prelude] = {
            "kernel_theorems": bucket["kernel_theorems"],
            "registered_count": len(bucket["registered"]),
            "curated_count": curated_in_prelude,
            "unregistered_count": len(bucket["unregistered"]),
            "unregistered": sorted(bucket["unregistered"]),
        }

    registered_names = sorted(n for n in footprints if n in join_result.registered)
    curated_names = sorted(n for n in footprints if n in join_result.curated)
    unregistered_names = sorted(n for n in footprints if n not in join_result.registered)

    # Facts that named a kernel theorem the denominator does not contain --
    # a Definition, a stale/renamed name, or a typo. Diagnostic, not a
    # failure: a fact is allowed to name a Definition's subject.
    stray = sorted(
        name for name in join_result.registered if name not in footprints
    )

    document: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "generated_by": "scripts/gen-ledger-coverage.py",
        "generated_from": [
            "prelude_theorem_inventory --include-constructed (release)",
            "artifacts/facts/*.json",
        ],
        "denominator_rule": (
            "Every distinct Declaration::Theorem across every constructed "
            "prelude (prelude_theorem_inventory --include-constructed), "
            "which already excludes Axiom, Definition, Opaque, Inductive, "
            "Constructor, Recursor and Quotient declarations. See this "
            "script's module docstring for the full justification."
        ),
        "join_rule": (
            "A fact counts toward `registered` when proof_route == "
            "'kernel-lean', epistemic_status in {proved, computed}, and one "
            "of three tiers names a theorem in the denominator: (1) "
            "formal.kernel_theorem, when the key is present (an explicit "
            "null means no single subject and stops here); (2) the "
            "declared name at the head of a lean4 formal.statement "
            "('theorem <Name> :' / 'def <Name> :' / '<Name> :'); (3) the "
            "fallback dotted-theorem-name extraction from "
            "check-fact-depends-derived.py::theorem_of. See module "
            "docstring for why tier 2 is load-bearing, not optional."
        ),
        "counts": {
            "overall": {
                "kernel_theorems": len(footprints),
                "registered": len(registered_names),
                "curated": len(curated_names),
                "unregistered": len(unregistered_names),
            },
            "by_prelude": by_prelude_out,
        },
        "unregistered": unregistered_names,
        "registered_kernel_theorems_not_in_denominator": stray,
        "join": {
            "facts_scanned": join_result.facts_scanned,
            "kernel_route_established_facts": join_result.kernel_route_established,
            "resolved_via_kernel_theorem_field": join_result.via_field,
            "resolved_via_statement_name": join_result.via_statement,
            "resolved_via_checker_command_fallback": join_result.via_checker_command,
            "unresolved_fact_ids": sorted(join_result.unresolved),
            "curated_facts_claimed": join_result.curated_facts,
            "unreviewed_generated_facts": join_result.unreviewed_facts,
        },
    }
    return document


def render(document: dict[str, Any]) -> str:
    return json.dumps(document, indent=2, ensure_ascii=False, sort_keys=False) + "\n"


def display(path: Path) -> str:
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="fail when the committed artifact differs from a fresh generation",
    )
    parser.add_argument(
        "--theorem-tsv",
        type=Path,
        default=None,
        help=(
            "read the theorem inventory from this file instead of running "
            "cargo -- testing/demonstration hook, see module docstring"
        ),
    )
    args = parser.parse_args()

    try:
        stdout = (
            args.theorem_tsv.read_text(encoding="utf-8")
            if args.theorem_tsv is not None
            else run_inventory()
        )
        footprints = parse_theorem_inventory(stdout)
        facts = load_facts()
        join_result = join(facts)
        document = build_document(footprints, join_result)
        rendered = render(document)
    except CoverageError as error:
        print(f"gen-ledger-coverage: ERROR: {error}", file=sys.stderr)
        return 1

    if args.check:
        current = OUTPUT.read_text(encoding="utf-8") if OUTPUT.is_file() else None
        if current != rendered:
            print(
                f"gen-ledger-coverage: ERROR: {display(OUTPUT)} is not what "
                "scripts/gen-ledger-coverage.py produces. It is generated: "
                "rerun `python3 scripts/gen-ledger-coverage.py` and commit "
                "the result.",
                file=sys.stderr,
            )
            return 1
    else:
        OUTPUT.write_text(rendered, encoding="utf-8")

    overall = document["counts"]["overall"]
    print(
        "LEDGER-COVERAGE|"
        f"kernel_theorems={overall['kernel_theorems']}|"
        f"registered={overall['registered']}|"
        f"curated={overall['curated']}|"
        f"unregistered={overall['unregistered']}|"
        f"curation_convention=absent-field-is-curated|"
        f"bytes={len(rendered.encode('utf-8'))}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

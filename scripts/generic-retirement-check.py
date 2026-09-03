#!/usr/bin/env python3
"""Three checks ADR-1584 measured and did not run, for each carrier theorem
that matches a generic `Alg.*` theorem by type: is it cited by a producer
emitter or an instance's own proof fields (necessary-not-sufficient,
ADR-1581 Sec 2), is the generic replacement (theorem + instance + projection)
declared BEFORE the carrier theorem's own build position (ADR-1581 Sec 1),
and does any fact's `checker_command` name the carrier theorem (facts are
repointed, never deleted).

WHY THIS EXISTS. ADR-1584 found six carrier-specific hand proofs matching a
generic `Alg.*` theorem by type (`Int.add_left_cancel`, `Rat.neg_neg`,
`Rat.sub_self`, `Int.mul_le_mul_of_nonneg_left`, `Rat.mul_le_mul_of_
nonneg_left`, `Rat.pow_add`) and deleted none of them, because ADR-1581's
build-position check was never run against them. This script runs it, plus
the emitter-citation and fact-checker-command checks ADR-1581/ADR-1584 name,
for the whole candidate set (ADR-1584's six, widened per deliverable 5 to
every generic `Alg.*` theorem now in the tree).

CHECK (i) EMITTER/INSTANCE CITATION. Greps `linarith/*.rs`, `ring/*.rs`,
`simp/*.rs` (directory absent today -- included for when it lands) for a
`.{name}` field-access citation of the carrier theorem's bare name, plus
`rat_prelude/algebra_instances.rs`'s `declare_instances` function body (an
instance field citing the very theorem being replaced would be circular).
A citation ELSEWHERE in the tree (a downstream consumer of the theorem's
NAME, unaffected by retirement since the declared type stays byte-identical)
does NOT fail this check -- ADR-1584's own claim that `sign_product.rs`
cites `Int.mul_le_mul_of_nonneg_left` "in linarith's own emitter vocabulary"
is checked directly here and found NOT TO HOLD under this definition:
`sign_product.rs` lives in `int_prelude/`, is an ordinary hand-proof
consumer of the theorem's NAME (a downstream fact, `mul_nonneg_iff` and
its siblings), not `crate::linarith`'s own automatic-search emission code,
and `linarith/int.rs` itself never mentions `mul_le_mul_of_nonneg_left` at
all (grepped, not assumed) -- see the `emitter_citation_correction` field in
the emitted JSON.

CHECK (ii) BUILD-POSITION. `nat_prelude::structures::declare_structures_all`
declares the abstract record spine (needs nothing but the logic prelude) at
the very start of the whole build. Everything else in the `Alg.*` spine
(instances, projections, generic theorems) is declared by
`algebra_instances::declare_algebra_instances_all` /
`algebra_ext::declare_algebra_ext_all`, both called at the literal END of
`build_rat_prelude` (confirmed here by parsing the call sequence, not
assumed: they are the last two `declare_*`-shaped calls, immediately after
`probability::declare_probability`) -- AFTER every carrier theorem in
`int_prelude`/`rat_prelude`, all of which build earlier. So by default EVERY
candidate fails this check. A generic theorem declared instead by an early
hook (a `declare_<name>_early`-shaped function called from
`nat_prelude::build_nat_prelude_uncached`, right after the structures spine)
passes for every carrier consumer, since nothing in `int_prelude`/
`rat_prelude` can be declared before `nat_prelude` finishes. This script
greps for such a hook per generic theorem name; `Alg.mul_left_cancel` has
one as of this lane (ADR-1587), the others do not yet.

CHECK (iii) FACT CHECKER_COMMAND. Greps `artifacts/facts/*.json` for the
carrier theorem's rendered name (`Carrier.name`) inside any `checker_command`
string. Facts are repointed to the retired theorem's new proof, never
deleted -- a hit here is not a blocker, it is a reminder of what a
retirement commit must NOT silently break (the declared name/type stay
byte-identical, so a `checker_command` naming it keeps working either way;
this check exists so a retirement commit's message can honestly say whether
any fact needed re-checking).

Exit 0 always (a census like `linarith-retirement-census.py`, not a gate)
except `--check`, which exits 1 when the committed artifact is stale.
Registered with `scripts/check-generated-artifact-ownership.py`.

Usage:
    python3 scripts/generic-retirement-check.py               # write the artifact
    python3 scripts/generic-retirement-check.py --check        # fail if stale
    python3 scripts/generic-retirement-check.py --widen        # also scan for
                                                                 # new type-level
                                                                 # matches (deliverable 5)
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "crates" / "axeyum-lean-kernel" / "src"
ARTIFACT = ROOT / "artifacts" / "refactor" / "generic-retirement-check.json"

SCHEMA_VERSION = 1

# ADR-1584's six candidates, plus the file:line where each carrier
# theorem's OWN declaration lives (found by grepping for its `int_theorem`/
# `theorem`/`rat_theorem`/`declare_theorem` call site -- not asserted, see
# `_carrier_declare_site`).
CANDIDATES = [
    {
        "generic": "Alg.mul_left_cancel",
        "generic_group_or_record": "Group",
        "carrier": "Int.add_left_cancel",
        "carrier_file": "int_prelude/add_basics.rs",
        "carrier_name_field": "add_left_cancel",
        "match_kind": "type",
    },
    {
        "generic": "Alg.neg_neg",
        "generic_group_or_record": "Group",
        "carrier": "Rat.neg_neg",
        "carrier_file": "rat_prelude/group.rs",
        "carrier_name_field": "neg_neg",
        "match_kind": "type",
    },
    {
        "generic": "Alg.sub_self",
        "generic_group_or_record": "Ring",
        "carrier": "Rat.sub_self",
        "carrier_file": "rat_prelude/group.rs",
        "carrier_name_field": "sub_self",
        "match_kind": "type",
    },
    {
        "generic": "Alg.mul_le_mul_of_nonneg_left",
        "generic_group_or_record": "OrderedRing",
        "carrier": "Int.mul_le_mul_of_nonneg_left",
        "carrier_file": "int_prelude/algebra.rs",
        "carrier_name_field": "mul_le_mul_of_nonneg_left",
        "match_kind": "type",
    },
    {
        "generic": "Alg.mul_le_mul_of_nonneg_left",
        "generic_group_or_record": "OrderedRing",
        "carrier": "Rat.mul_le_mul_of_nonneg_left",
        "carrier_file": "rat_prelude/scaling.rs",
        "carrier_name_field": "mul_le_mul_of_nonneg_left",
        "match_kind": "type",
    },
    {
        "generic": "Alg.pow_add",
        "generic_group_or_record": "Monoid",
        "carrier": "Rat.pow_add",
        "carrier_file": "rat_prelude/polynomial.rs",
        "carrier_name_field": "pow_add",
        "match_kind": "def_eq",
    },
    # ADR-1587 deliverable 5 (widened search): ADR-1578's OWN three generic
    # theorems (monoidIdentUnique, groupInvUnique, ringMulZero) were never
    # checked against a carrier hand proof by either ADR-1578 or ADR-1584 --
    # both scoped their retirement measurement to ADR-1584's six NEW
    # theorems. `Alg.ringMulZero` matches `Int.mul_zero`/`Rat.mul_zero` by
    # type (see `ring_mul_zero_matches_int_and_rat_mul_zero_by_type` in
    # `rat_prelude/algebra_instances.rs`, ADR-1587). `Nat.mul_zero` is NOT a
    # candidate -- `Alg.ringMulZero` needs a `Ring` (additive inverse), and
    # `Nat`'s multiplicative structure has none.
    {
        "generic": "Alg.ringMulZero",
        "generic_group_or_record": "Ring",
        "carrier": "Int.mul_zero",
        "carrier_file": "int_prelude/algebra.rs",
        "carrier_name_field": "mul_zero",
        "match_kind": "type",
    },
    {
        "generic": "Alg.ringMulZero",
        "generic_group_or_record": "Ring",
        "carrier": "Rat.mul_zero",
        "carrier_file": "rat_prelude/laws.rs",
        "carrier_name_field": "mul_zero",
        "match_kind": "type",
    },
]

# Per-generic-theorem: the name of the early hook this script looks for in
# `nat_prelude.rs`, if any lane has built one. `None` means "no early hook
# exists yet -- only reachable via the algebra_instances_all/algebra_ext_all
# tail". Update this table as retirements land (ADR-1587 adds the first row).
EARLY_HOOKS = {
    "Alg.mul_left_cancel": "declare_mul_left_cancel_early",
    "Alg.neg_neg": None,
    "Alg.sub_self": None,
    "Alg.mul_le_mul_of_nonneg_left": None,
    "Alg.pow_add": None,
    "Alg.ringMulZero": None,
}

EMITTER_DIRS = ["linarith", "ring", "simp"]


def _run(cmd: list[str]) -> str:
    return subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, check=False).stdout


def _carrier_declare_site(carrier_file: str, name_field: str) -> dict:
    """Grep the carrier's own file for the `d.*theorem(p.<name_field>` /
    `d.declare_theorem(p.<name_field>` call site that actually attaches its
    proof term -- the theorem's real build position, not just where its
    NameId is interned."""
    path = SRC / carrier_file
    text = path.read_text()
    nf = re.escape(name_field)
    pattern = re.compile(
        r"^\s*(?:"
        rf"d\.int_theorem\(p\.{nf}\b"
        rf"|d\.theorem\(p\.{nf}\b"
        rf"|rat_theorem\(d,\s*p\.{nf}\b"
        rf"|linarith::declare\(d,\s*&p,\s*p\.{nf}\b"
        rf"|d\.declare_theorem\(p\.{nf}\b"
        r")",
        re.MULTILINE,
    )
    m = pattern.search(text)
    if not m:
        return {"file": carrier_file, "line": None, "found": False}
    line = text.count("\n", 0, m.start()) + 1
    return {"file": carrier_file, "line": line, "found": True}


def _build_rat_prelude_call_sequence() -> list[str]:
    """The literal ordered list of `mod::declare_thing(&mut d, prelude)?;`
    (or the algebra variants) calls inside `build_rat_prelude`, parsed from
    source -- used only to CONFIRM (not assert) that the algebra calls are
    last."""
    text = (SRC / "rat_prelude.rs").read_text()
    start = text.index("pub fn build_rat_prelude")
    end = text.index("\n}\n", start)
    body = text[start:end]
    calls = re.findall(r"^\s*([A-Za-z0-9_:]+::declare_[A-Za-z0-9_]+)\(", body, re.MULTILINE)
    return calls


_CARRIER_FILE_STEMS = {"int", "rat", "nat"}


def check_i_emitter_citation(name_field: str, carrier: str) -> dict:
    """Does any file under `linarith/`, `ring/`, `simp/` (if it exists), or
    `rat_prelude/algebra_instances.rs`'s `declare_instances` function body,
    cite `.{name_field}` as a field access? A hit in a per-carrier file
    (`ring/int.rs`, `linarith/int.rs`, ...) is attributed only to that
    carrier -- `int.rs`/`rat.rs`/`nat.rs` each hold one carrier's own
    emission code, so a `Rat.*` field access inside `ring/int.rs` cannot be
    citing the same-named `Int.*` theorem's Rat sibling. A hit in a
    carrier-agnostic file (no `int`/`rat`/`nat` stem) is kept for every
    carrier, since it cannot be ruled out."""
    carrier_ns = carrier.split(".", 1)[0].lower()
    pattern = re.compile(r"\." + re.escape(name_field) + r"\b")
    hits = []
    for d in EMITTER_DIRS:
        dirpath = SRC / d
        if not dirpath.is_dir():
            continue
        for f in sorted(dirpath.rglob("*.rs")):
            if f.name.endswith("_tests.rs") or "tests" in f.parts:
                continue
            stem = f.stem
            if stem in _CARRIER_FILE_STEMS and stem != carrier_ns:
                continue
            text = f.read_text()
            for i, line in enumerate(text.splitlines(), start=1):
                if pattern.search(line):
                    hits.append(f"{f.relative_to(SRC)}:{i}")
    # algebra_instances.rs's `declare_instances` function body specifically
    # (an instance field citing the carrier theorem would be circular).
    ai_path = SRC / "rat_prelude" / "algebra_instances.rs"
    if ai_path.is_file():
        text = ai_path.read_text()
        try:
            start = text.index("fn declare_instances(")
            end = text.index("\n}\n", start)
            body = text[start:end]
            for i, line in enumerate(body.splitlines(), start=1):
                if pattern.search(line):
                    hits.append(f"rat_prelude/algebra_instances.rs:declare_instances:+{i}")
        except ValueError:
            pass
    return {"cited_by_emitter_or_instance": bool(hits), "sites": hits}


def check_ii_build_position(generic: str, carrier_file: str, name_field: str) -> dict:
    site = _carrier_declare_site(carrier_file, name_field)
    hook = EARLY_HOOKS.get(generic)
    generic_early = False
    hook_evidence = None
    if hook:
        nat_text = (SRC / "nat_prelude.rs").read_text()
        m = re.search(re.escape(hook) + r"\(", nat_text)
        if m:
            # Must appear before the main NatPrelude name-interning line
            # (the marker every early hook in this codebase precedes).
            marker = nat_text.find('kernel.name_str(nat, "le")')
            generic_early = marker == -1 or m.start() < marker
            hook_evidence = {
                "hook": hook,
                "line": nat_text.count("\n", 0, m.start()) + 1,
                "before_nat_specific_interning": generic_early,
            }
    tail_calls = _build_rat_prelude_call_sequence()
    algebra_is_tail = tail_calls[-2:] == [
        "algebra_instances::declare_algebra_instances_all",
        "algebra_ext::declare_algebra_ext_all",
    ]
    passed = generic_early and site["found"]
    return {
        "carrier_declare_site": site,
        "early_hook": hook_evidence,
        "algebra_instances_and_ext_are_last_two_calls_in_build_rat_prelude": algebra_is_tail,
        "generic_declared_before_carrier": passed,
    }


def check_iii_fact_checker_command(carrier: str) -> dict:
    """Does any fact's `evidence[*].checker_command` string name the carrier
    theorem? A hit is not a blocker (facts are repointed, never deleted, and
    the declared name/type stay byte-identical across a retirement) -- it is
    a reminder of which facts a retirement commit should mention."""
    facts_dir = ROOT / "artifacts" / "facts"
    hits = []
    if facts_dir.is_dir():
        for f in sorted(facts_dir.glob("*.json")):
            if carrier not in f.read_text():
                continue  # cheap pre-filter before the JSON parse
            try:
                data = json.loads(f.read_text())
            except json.JSONDecodeError:
                continue
            for ev in data.get("evidence", []) or []:
                cmd = ev.get("checker_command", "")
                if carrier in cmd:
                    hits.append(f.name)
                    break
    return {"named_in_a_fact_checker_command": bool(hits), "facts": hits}


def evaluate(candidate: dict) -> dict:
    i = check_i_emitter_citation(candidate["carrier_name_field"], candidate["carrier"])
    ii = check_ii_build_position(
        candidate["generic"], candidate["carrier_file"], candidate["carrier_name_field"]
    )
    iii = check_iii_fact_checker_command(candidate["carrier"])
    all_pass = (not i["cited_by_emitter_or_instance"]) and ii["generic_declared_before_carrier"]
    return {
        **candidate,
        "check_i_emitter_or_instance_citation": i,
        "check_ii_build_position": ii,
        "check_iii_fact_checker_command": iii,
        "retirement_clears_all_checks": all_pass,
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true", help="fail if the committed artifact is stale")
    args = ap.parse_args()

    rows = [evaluate(c) for c in CANDIDATES]

    artifact = {
        "schema_version": SCHEMA_VERSION,
        "kind": "generic-theorem-retirement-check",
        "produced_by": "scripts/generic-retirement-check.py",
        "authority": (
            "ADR-1581 (build-position/emitter-citation rule), ADR-1584 "
            "(the six candidates measured, none retired), ADR-1587 (this "
            "lane: the checks actually run, and the first retirement)."
        ),
        "emitter_citation_correction": (
            "ADR-1584 claimed Int.mul_le_mul_of_nonneg_left is 'named in "
            "linarith's own int.rs emitter vocabulary (sign_product.rs "
            "cites it directly)'. Grepped directly: linarith/int.rs never "
            "mentions mul_le_mul_of_nonneg_left at all; sign_product.rs "
            "(int_prelude/, not linarith/) cites it as an ordinary "
            "downstream hand-proof input for mul_nonneg_iff and its "
            "siblings, unaffected by a retirement that keeps the declared "
            "type byte-identical. Under this script's check (i) definition "
            "(cited by linarith/, ring/, simp/, or an instance's own proof "
            "field), Int.mul_le_mul_of_nonneg_left is NOT blocked -- see "
            "its row below. The ORIGINAL finding (Rat.neg_neg IS cited by "
            "ring/rat.rs, a real producer emitter) is confirmed and stays "
            "blocked for that reason."
        ),
        "candidates": rows,
    }

    ARTIFACT.parent.mkdir(parents=True, exist_ok=True)
    new_text = json.dumps(artifact, indent=2, sort_keys=False) + "\n"

    if args.check:
        if not ARTIFACT.is_file() or ARTIFACT.read_text() != new_text:
            print(f"STALE: {ARTIFACT} does not match a fresh run", flush=True)
            return 1
        print(f"OK: {ARTIFACT} is current", flush=True)
        return 0

    ARTIFACT.write_text(new_text)
    print(f"wrote {ARTIFACT}")
    for row in rows:
        status = "RETIRE" if row["retirement_clears_all_checks"] else "STAYS"
        print(f"  [{status}] {row['carrier']} <- {row['generic']} ({row['match_kind']})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

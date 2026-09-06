#!/usr/bin/env python3
"""Cross-consistency gate for the CAS SymPy parity corpus
(`docs/plan/cas-parity-corpus-2026-09-05/`).

Why this exists
----------------
The parity corpus has THREE copies of the truth: `corpus.json` (the entries
and their tiers), the Rust harness `parity_corpus.rs` (what each entry
actually runs and what tier it is treated as), and the README's prose counts
(entries / core / decline_expected / known_defect). Twice in one week the
README's counts drifted from `corpus.json` (119 recorded against 123
present; then 125 against 126) and nothing failed -- no checker's exit status
depended on it. Per CLAUDE.md, a checker that cannot fail is worse than no
checker.

This script checks FIVE things, each independently falsifiable:

  (a) README counts.  The README carries one machine-generated block (see
      `README_MARKER_BEGIN`/`README_MARKER_END` below) stating the entries /
      core / decline_expected / known_defect counts. This script recomputes
      those counts from `corpus.json` and compares; `--write` regenerates
      the block in place instead of just checking it.
  (b) id parity.  Every id in `corpus.json` must have exactly one harness
      entry in `parity_corpus.rs`, and vice versa.
  (c) tier parity.  For every id present in both, the tier `corpus.json`
      records must match the tier the harness's `e!(...)` macro call gives
      it.
  (d) `corpus.json` integrity.  The file must parse as a JSON list of
      objects, each carrying a string `id` and a `tier` in
      {core, decline_expected, known_defect}, with no duplicate id.
  (e) ground truth coverage.  Every `core`-tier entry must have a
      corresponding independent claim in `ground_truth.py`.

Guard (b)/(c): parsing the Rust harness
----------------------------------------
`parity_corpus.rs` builds its entry table with one macro, `e!(id, area,
module, tier, run_fn)`, called positionally once per entry (see
`macro_rules! e` and the `let entries: Vec<Entry> = vec![...]` block in
`main()`). This script's `parse_harness_entries()` regexes over the WHOLE
file for `e!( "id" , <anything, DOTALL> , Tier , fn_name )` where `Tier` is
one of the three bare identifiers `Core` / `DeclineExpected` / `KnownDefect`
(imported via `use Tier::{Core, DeclineExpected};` at the top of `main`).
This is deliberately narrow: it assumes every `Entry` is built through the
`e!` macro with tier as the 4th positional argument, and that no other
`e!(` call exists elsewhere in the file. Both are true as of this writing
(count of `e!(` invocations equals `corpus.json`'s entry count, verified
2026-09-05); if the harness's macro shape changes, this regex must change
with it -- that is a deliberate coupling, not an oversight, because there is
no `rustc`-level structure available to a pure-Python checker here (unlike
`check-cas-trust-registry.py`'s brace-walker, which only needs to find
`pub fn`/`pub struct` headers -- this needs macro ARGUMENTS, which brace
walking alone does not separate from commas inside nested calls). The
non-greedy `.*?` between the id and the tier is safe here specifically
because the only commas between an entry's id and its tier are the two
`area`/`module` arguments (`None` or `Some("literal")`), which never
themselves contain a comma.

Guard (e): matching `ground_truth.py` to a `core` entry
--------------------------------------------------------
`ground_truth.py` is NOT indexed by `corpus.json`'s exact ids -- it is
organized by mathematical family/section (its own docstring says as much:
"It does not need to match corpus.json's structure line for line"). What it
DOES carry, in every `ok(...)`/`need_sympy(...)` message string, is the
entry's FAMILY PREFIX: `corpus.json`'s id `"d1-cubic"` and its control
`"d1-cubic-ctrl"` both reduce to the family token `"d1"`, and `ground_truth.py`
literally writes `"d1 d/dx(x^3-2x+1) = 3x^2-2"` as an `ok(...)` message.
This script derives each entry's family by stripping a trailing `-ctrl` and
keeping the segment before the first remaining `-`, then requires that exact
token appear at a word boundary somewhere in `ground_truth.py`'s source
text. This is deliberately FAMILY-level, not id-level: `ground_truth.py`
groups a main claim and its `-ctrl` control under the same family message
(often the same `section()`), and there is no finer-grained structure to
parse. Verified 2026-09-05: of 97 distinct families across all 123 entries,
exactly one (`prob7`, tier `decline_expected`) has no word-boundary match --
`ground_truth.py`'s own comment names it as the entry recording where the
mechanism does NOT reach, so there is nothing to independently re-derive
there. Because guard (e) only requires coverage for `core`-tier entries,
that is not a violation.

Usage
-----
    python3 scripts/check-cas-parity-corpus.py          # check (exit 1 on drift)
    python3 scripts/check-cas-parity-corpus.py --write   # regenerate the README block

`--write` touches ONLY the generated counts block; it does not silence
guards (b)-(e), which have no auto-fix (a tier/id mismatch is a finding
about the corpus, to be resolved by hand).
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys
from collections import Counter

REPO_ROOT = pathlib.Path(__file__).resolve().parent.parent
CORPUS_DIR = REPO_ROOT / "docs" / "plan" / "cas-parity-corpus-2026-09-05"
CORPUS_JSON = CORPUS_DIR / "corpus.json"
GROUND_TRUTH = CORPUS_DIR / "ground_truth.py"
README = CORPUS_DIR / "README.md"
HARNESS = (
    REPO_ROOT
    / "crates"
    / "axeyum-cas"
    / "examples"
    / "parity_corpus.rs"
)

TIER_ORDER = ("core", "decline_expected", "known_defect")
HARNESS_TIER_LABEL = {
    "Core": "core",
    "DeclineExpected": "decline_expected",
    "KnownDefect": "known_defect",
}

README_MARKER_BEGIN = (
    "<!-- BEGIN GENERATED: cas-parity-corpus-counts "
    "(scripts/check-cas-parity-corpus.py --write) -->"
)
README_MARKER_END = "<!-- END GENERATED: cas-parity-corpus-counts -->"

# Matches one `e!( "id", <area>, <module>, Tier, run_fn )` macro invocation,
# across newlines. See "Guard (b)/(c)" above for why the non-greedy middle
# group is safe.
HARNESS_ENTRY_RE = re.compile(
    r'e!\(\s*"([^"]+)"\s*,\s*(.*?)\s*,\s*'
    r"(Core|DeclineExpected|KnownDefect)\s*,\s*[A-Za-z0-9_]+\s*\)",
    re.DOTALL,
)


class SchemaError(Exception):
    """`corpus.json` does not even parse into the shape this gate needs."""


def load_corpus(text: str) -> list[dict]:
    """Parse `corpus.json`'s text into a list of entry dicts, raising
    `SchemaError` (never a bare exception) for anything this gate cannot
    make sense of -- guard (d)."""
    try:
        data = json.loads(text)
    except json.JSONDecodeError as exc:
        raise SchemaError(f"corpus.json does not parse as JSON: {exc}") from exc
    if not isinstance(data, list):
        raise SchemaError("corpus.json must be a JSON array of entry objects")
    for i, entry in enumerate(data):
        if not isinstance(entry, dict):
            raise SchemaError(f"corpus.json[{i}] is not a JSON object")
        if not isinstance(entry.get("id"), str) or not entry["id"]:
            raise SchemaError(f"corpus.json[{i}] has no string 'id'")
        if entry.get("tier") not in TIER_ORDER:
            raise SchemaError(
                f"corpus.json[{i}] (id={entry.get('id')!r}) has tier "
                f"{entry.get('tier')!r}, not one of {TIER_ORDER}"
            )
    return data


def find_duplicate_ids(entries: list[dict]) -> list[str]:
    counts = Counter(e["id"] for e in entries)
    return sorted(cid for cid, n in counts.items() if n > 1)


def parse_harness_entries(text: str) -> dict[str, str]:
    """Return {id: tier_label} for every `e!(...)` invocation in the Rust
    harness. Does not detect a duplicate id within the harness itself (no
    guard here requires that); a later occurrence simply overwrites an
    earlier one in the returned dict."""
    harness: dict[str, str] = {}
    for entry_id, _middle, tier in HARNESS_ENTRY_RE.findall(text):
        harness[entry_id] = HARNESS_TIER_LABEL[tier]
    return harness


def family_of(entry_id: str) -> str:
    """Reduce a corpus id to the family token `ground_truth.py` names in its
    claim messages -- see the "Guard (e)" note in the module docstring."""
    base = entry_id[: -len("-ctrl")] if entry_id.endswith("-ctrl") else entry_id
    return base.split("-", 1)[0]


def family_is_covered(family: str, ground_truth_src: str) -> bool:
    return re.search(r"\b" + re.escape(family) + r"\b", ground_truth_src) is not None


def tier_counts(entries: list[dict]) -> dict[str, int]:
    counts = Counter(e["tier"] for e in entries)
    return {tier: counts.get(tier, 0) for tier in TIER_ORDER}


def render_counts_block(counts: dict[str, int]) -> str:
    total = sum(counts.values())
    line = (
        f"Tiers: **{counts['core']} `core`**, "
        f"**{counts['decline_expected']} `decline_expected`**, "
        f"**{counts['known_defect']} `known_defect`**. "
        f"Total entries: **{total}**."
    )
    return f"{README_MARKER_BEGIN}\n{line}\n{README_MARKER_END}"


def extract_readme_block(readme_text: str) -> str | None:
    start = readme_text.find(README_MARKER_BEGIN)
    end = readme_text.find(README_MARKER_END)
    if start == -1 or end == -1 or end < start:
        return None
    return readme_text[start : end + len(README_MARKER_END)]


def write_readme_block(readme_text: str, counts: dict[str, int]) -> str:
    new_block = render_counts_block(counts)
    start = readme_text.find(README_MARKER_BEGIN)
    end = readme_text.find(README_MARKER_END)
    if start == -1 or end == -1 or end < start:
        raise SchemaError(
            f"README.md has no {README_MARKER_BEGIN!r} / "
            f"{README_MARKER_END!r} block to regenerate"
        )
    return readme_text[:start] + new_block + readme_text[end + len(README_MARKER_END) :]


def run_checks(
    corpus_text: str, harness_text: str, readme_text: str, ground_truth_src: str
) -> tuple[list[str], dict[str, int]]:
    """Run all five guards. Returns (violations, tier_counts). Raises
    `SchemaError` only for guard (d) failures severe enough that nothing
    else can be checked (unparseable JSON / wrong top-level shape) --
    duplicate ids and bad tier values are collected as ordinary
    violations instead, since the rest of the checks can still run around
    them where the id itself is fine."""
    violations: list[str] = []

    # --- guard (d): corpus.json integrity -----------------------------
    entries = load_corpus(corpus_text)
    dupes = find_duplicate_ids(entries)
    if dupes:
        violations.append(
            f"guard(d) duplicate id(s) in corpus.json: {', '.join(dupes)}"
        )

    counts = tier_counts(entries)

    # --- guard (a): README generated counts block ---------------------
    block = extract_readme_block(readme_text)
    if block is None:
        violations.append(
            "guard(a) README.md has no generated counts block "
            f"(expected markers {README_MARKER_BEGIN!r} / "
            f"{README_MARKER_END!r}); run --write"
        )
    else:
        expected_block = render_counts_block(counts)
        if block != expected_block:
            violations.append(
                "guard(a) README's generated counts block is stale:\n"
                f"    README has:    {block!r}\n"
                f"    corpus.json says: {expected_block!r}\n"
                "    run: python3 scripts/check-cas-parity-corpus.py --write"
            )

    # --- guards (b)/(c): harness id and tier parity --------------------
    harness = parse_harness_entries(harness_text)
    json_ids = {e["id"] for e in entries}
    harness_ids = set(harness.keys())
    only_in_json = sorted(json_ids - harness_ids)
    only_in_harness = sorted(harness_ids - json_ids)
    if only_in_json:
        violations.append(
            "guard(b) id(s) in corpus.json with no harness entry: "
            + ", ".join(only_in_json)
        )
    if only_in_harness:
        violations.append(
            "guard(b) id(s) in the harness with no corpus.json entry: "
            + ", ".join(only_in_harness)
        )

    tier_mismatches = []
    for entry in entries:
        eid = entry["id"]
        if eid in harness and harness[eid] != entry["tier"]:
            tier_mismatches.append(f"{eid} (json={entry['tier']}, harness={harness[eid]})")
    if tier_mismatches:
        violations.append(
            "guard(c) tier mismatch between corpus.json and the harness: "
            + "; ".join(tier_mismatches)
        )

    # --- guard (e): ground_truth.py coverage of core entries -----------
    missing_ground_truth = []
    for entry in entries:
        if entry["tier"] != "core":
            continue
        family = family_of(entry["id"])
        if not family_is_covered(family, ground_truth_src):
            missing_ground_truth.append(f"{entry['id']} (family={family})")
    if missing_ground_truth:
        violations.append(
            "guard(e) core entr(y/ies) with no ground_truth.py claim: "
            + ", ".join(missing_ground_truth)
        )

    return violations, counts


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--write",
        action="store_true",
        help="regenerate the README's generated counts block in place",
    )
    args = parser.parse_args(argv)

    if not CORPUS_JSON.is_file():
        print(f"CAS-PARITY-CORPUS|FAIL|reason=missing_corpus_json:{CORPUS_JSON}")
        return 1
    if not HARNESS.is_file():
        print(f"CAS-PARITY-CORPUS|FAIL|reason=missing_harness:{HARNESS}")
        return 1
    if not README.is_file():
        print(f"CAS-PARITY-CORPUS|FAIL|reason=missing_readme:{README}")
        return 1
    if not GROUND_TRUTH.is_file():
        print(f"CAS-PARITY-CORPUS|FAIL|reason=missing_ground_truth:{GROUND_TRUTH}")
        return 1

    corpus_text = CORPUS_JSON.read_text()
    try:
        entries_for_write = load_corpus(corpus_text)
    except SchemaError as exc:
        print(f"CAS-PARITY-CORPUS|FAIL|reason=schema_error:{exc}")
        return 1

    if args.write:
        counts = tier_counts(entries_for_write)
        readme_text = README.read_text()
        try:
            new_readme = write_readme_block(readme_text, counts)
        except SchemaError as exc:
            print(f"CAS-PARITY-CORPUS|FAIL|reason=write_error:{exc}")
            return 1
        if new_readme != readme_text:
            README.write_text(new_readme)
            print(
                "CAS-PARITY-CORPUS|WROTE|"
                f"entries={sum(counts.values())}|core={counts['core']}|"
                f"decline_expected={counts['decline_expected']}|"
                f"known_defect={counts['known_defect']}"
            )
        else:
            print("CAS-PARITY-CORPUS|WROTE|no_change")
        return 0

    harness_text = HARNESS.read_text()
    readme_text = README.read_text()
    ground_truth_src = GROUND_TRUTH.read_text()

    violations, counts = run_checks(corpus_text, harness_text, readme_text, ground_truth_src)

    summary = (
        f"CAS-PARITY-CORPUS|entries={sum(counts.values())}"
        f"|core={counts['core']}"
        f"|decline_expected={counts['decline_expected']}"
        f"|known_defect={counts['known_defect']}"
    )

    if violations:
        print(summary + f"|violations={len(violations)}|FAIL")
        for v in violations:
            print(f"  {v}")
        return 1

    print(summary + "|PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

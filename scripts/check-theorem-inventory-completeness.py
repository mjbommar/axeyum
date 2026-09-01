#!/usr/bin/env python3
"""Guard: `prelude_theorem_inventory`, `kernel_declaration_projection` and
`cross_prelude_collision_tests` must agree on the distinct set of `Declaration
::Theorem` names (the first two) AND on the set of prelude-group labels their
three separate `build_groups` implementations build (all three).

# Why this exists

2026-08-27: the two tools disagreed by exactly 32 theorems -- `Nat.Peano.*`
(9) and `Int.Characterization.*` (23) -- because `prelude_theorem_inventory`'s
`build_groups` never called `build_characterization`, the only place those
names are declared. Nothing failed: `gen-ledger-coverage.py`'s denominator
(which reads `prelude_theorem_inventory`) silently undercounted `nat` by 9 and
`integer` by 23, and 9 already-generated, `--audit`-passing facts could not
move the `registered` counter because the denominator never reached them. See
`docs/research/11-design-review/2026-08-27-rat-reindexing-and-the-denominator-gap.md`.

This was NOT one of `prelude_theorem_inventory`'s documented, deliberate
exclusions (`Axiom`, `Definition`, `Opaque`, `Inductive`, `Constructor`,
`Recursor`, `Quotient` -- see that tool's own module doc): those are
`Declaration` KINDS excluded on purpose, and `kernel_declaration_projection`
agrees with them (a `Definition` like `Nat.Peano.iter` is correctly absent
from BOTH tools' theorem sets). This was a whole prelude GROUP one tool never
built -- the same "empty answer from a tool that was never pointed at your
subject is indistinguishable from a strong negative result" trap CLAUDE.md
already documents, just short by 32 instead of empty, which is worse: a
partial answer is more convincing than a blank one.

`gen-ledger-coverage.py --check` (already gated in `check.sh`/`justfile`) only
catches the committed JSON drifting from a fresh regeneration -- regenerating
with a STILL-BROKEN inventory tool reproduces the same wrong number and
passes. This script is the check that would have caught the original defect:
it does not trust either tool's own module-doc claims about what it excludes
and why: it runs BOTH, in the SAME cargo build directory, and asserts their
theorem name sets are identical. Any name present in one and absent from the
other is a failure, in EITHER direction, because either tool omitting a
prelude group is the same defect class.

# A THIRD file has the identical shape, and this script did not cover it

`crates/axeyum-lean-kernel/src/cross_prelude_collision_tests.rs`'s own
`build_groups` -- a *third*, independent re-implementation of "build every
prelude this crate ships" -- had the SAME gap: its module doc claimed to
mirror `prelude_theorem_inventory`'s prelude list but never called
`build_characterization` either, so the 32 `characterization` declarations
had never been checked for a cross-prelude NAME COLLISION (a different
question from "is it in the theorem count", and one this script's `check()`
above cannot answer, since collision-checking covers every `Declaration`
kind, not just theorems). See `docs/plan/status/146-collision-gap.md`.

That file is a `#[test]`, not a binary with a TSV stdout, so it cannot be
compared by running it and parsing output the way `check()` above compares
`kdp`/`pti`. `check_group_labels` instead compares the three tools' PRELUDE
LABEL SETS (not theorem names): the labels `kernel_declaration_projection`
and `prelude_theorem_inventory` actually emitted in their TSV output, against
the labels used inside `cross_prelude_collision_tests.rs`'s own `build_groups`
literals, read directly from that file's source text (`collision_group_
labels`). A label present in one `build_groups` and absent from another is
the same defect class as `check()`'s theorem-name mismatch, in whichever of
the three tools omitted it.

# Testing hook

`--kdp-tsv` / `--pti-tsv` substitute a file in each tool's own TSV shape;
`--collision-source` substitutes a file for `cross_prelude_collision_tests
.rs`'s own source text. `scripts/tests/test_theorem_inventory_completeness.py`
exercises the comparison logic against these without paying a `--release`
cargo build of the whole constructed universe.

```sh
python3 scripts/check-theorem-inventory-completeness.py
```
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

KDP_COMMAND = (
    "cargo run --quiet --release -p axeyum-lean-kernel "
    "--example kernel_declaration_projection"
)
PTI_COMMAND = (
    "cargo run --quiet --release -p axeyum-lean-kernel "
    "--example prelude_theorem_inventory -- --include-constructed"
)
COLLISION_SOURCE = (
    ROOT / "crates" / "axeyum-lean-kernel" / "src" / "cross_prelude_collision_tests.rs"
)

# Two shapes, because the file has used both. `Group { label: "..." }` was the
# original struct literal; `Group::of("...", &kernel)` is the constructor it was
# refactored to, and after that refactor this regex matched ZERO occurrences.
# It refuses an empty result, so the checker went hard red rather than quietly
# comparing against an empty set -- which is the correct direction to fail, and
# is also why nobody noticed: it is registered in no aggregate gate, so the only
# way to see it was to run it by hand. Found 2026-08-31 while adding the `ipc`
# group, which is exactly the defect class this checker exists to catch.
_LABEL_RE = re.compile(
    r'(?:label:\s*"([A-Za-z0-9_]+)"|Group::of\(\s*"([A-Za-z0-9_]+)")'
)


class CompletenessError(Exception):
    pass


def kdp_theorem_names(stdout: str) -> set[str]:
    """Distinct `Declaration::Theorem` names from `kernel_declaration_projection`'s
    unfiltered TSV: `prelude\\tkind\\tname\\tfootprint\\t...`, 8 fields, every
    declaration of every kind across every prelude it builds.

    Refuses an empty result: an empty set here is what a broken tool, a
    missing binary, or a debug-build SIGABRT (this binary MUST run
    `--release`, see its own module doc) looks like, and "measured, and there
    was nothing to report" is the most dangerous reading available.
    """
    names: set[str] = set()
    for line in stdout.splitlines():
        if not line.strip():
            continue
        fields = line.split("\t")
        if len(fields) != 8:
            raise CompletenessError(
                f"kernel_declaration_projection row has {len(fields)} fields, "
                f"expected 8: {line[:160]!r}"
            )
        if fields[1] == "theorem":
            names.add(fields[2])
    if not names:
        raise CompletenessError(
            "kernel_declaration_projection reported ZERO theorems -- a broken "
            "tool or empty input, not a real measurement"
        )
    return names


def pti_theorem_names(stdout: str) -> set[str]:
    """Distinct theorem names from `prelude_theorem_inventory`'s TSV:
    `label\\ttheorem\\tfootprint-size\\taxioms-csv`. Every row is already a
    `Declaration::Theorem` by construction (that tool filters to it), so no
    kind check is needed here -- only `kernel_declaration_projection`'s
    unfiltered rows need one.
    """
    names: set[str] = set()
    for line in stdout.splitlines():
        if not line.strip():
            continue
        fields = line.split("\t")
        if len(fields) < 3:
            raise CompletenessError(
                f"prelude_theorem_inventory row malformed: {line[:160]!r}"
            )
        names.add(fields[1])
    if not names:
        raise CompletenessError(
            "prelude_theorem_inventory reported ZERO theorems -- a broken "
            "tool or empty input, not a real measurement"
        )
    return names


def kdp_prelude_labels(stdout: str) -> set[str]:
    """Distinct prelude labels (`kernel_declaration_projection`'s first TSV
    field) actually present in its output -- i.e. the label set its own
    `build_groups` produced, read from what it emitted rather than assumed
    from source. Reuses the same 8-field shape check as `kdp_theorem_names`;
    a malformed row is caught there in normal use since both are run over the
    same `stdout`, but this function re-validates independently so it also
    works standalone (as the tests exercise it).
    """
    labels: set[str] = set()
    for line in stdout.splitlines():
        if not line.strip():
            continue
        fields = line.split("\t")
        if len(fields) != 8:
            raise CompletenessError(
                f"kernel_declaration_projection row has {len(fields)} fields, "
                f"expected 8: {line[:160]!r}"
            )
        labels.add(fields[0])
    if not labels:
        raise CompletenessError(
            "kernel_declaration_projection reported ZERO prelude labels -- a "
            "broken tool or empty input, not a real measurement"
        )
    return labels


def pti_prelude_labels(stdout: str) -> set[str]:
    """Distinct prelude labels (`prelude_theorem_inventory`'s first TSV
    field) actually present in its output. Depends on every built prelude
    group producing at least one theorem row -- true for every group this
    crate ships today (even `logic` proves things) -- so a group with zero
    theorems would be invisible here; `collision_group_labels` below is read
    from source specifically because a `#[test]` cannot be probed this way at
    all, so this function's "read what it emitted" approach is the one
    that's actually available for the two runnable tools.
    """
    labels: set[str] = set()
    for line in stdout.splitlines():
        if not line.strip():
            continue
        fields = line.split("\t")
        if len(fields) < 3:
            raise CompletenessError(
                f"prelude_theorem_inventory row malformed: {line[:160]!r}"
            )
        labels.add(fields[0])
    if not labels:
        raise CompletenessError(
            "prelude_theorem_inventory reported ZERO prelude labels -- a "
            "broken tool or empty input, not a real measurement"
        )
    return labels


def collision_group_labels(source_text: str) -> set[str]:
    """Distinct prelude labels used in `cross_prelude_collision_tests.rs`'s
    `Group { label: "...", ... }` literals -- both `build_groups`'s real
    groups and the `negative_control` submodule's synthetic ones. Scanning
    the WHOLE file rather than isolating `build_groups`'s body is safe
    because `negative_control` only ever reuses labels `build_groups` already
    declares (`logic`, `nat`, `axreal`) as a subset for its injected-collision
    fixture -- it can shrink what a naive line-count would show, never
    introduce a label absent from the real group list, so it cannot produce a
    false MATCH by inventing an extra label that happens to agree with the
    other two tools.

    Refuses an empty result: if this file's `Group` construction shape ever
    changes away from BOTH `label: "..."` and `Group::of("...", ...)`, or the
    file is empty or missing, that
    must fail loudly rather than silently compare against an empty set (which
    `check_group_labels` would otherwise report as "every other tool's label
    is missing from this one" -- true, but for the wrong reason).
    """
    labels = {
        label
        for match in _LABEL_RE.findall(source_text)
        for label in match
        if label
    }
    if not labels:
        raise CompletenessError(
            "cross_prelude_collision_tests.rs: found ZERO `label: \"...\"` "
            "occurrences -- source shape changed, or the file is empty/"
            "missing, not a real measurement"
        )
    return labels


def check_group_labels(
    kdp_labels: set[str], pti_labels: set[str], collision_labels: set[str]
) -> int:
    """Raise `CompletenessError` naming any prelude-group label present in
    one of the three `build_groups` implementations
    (`kernel_declaration_projection`, `prelude_theorem_inventory`,
    `cross_prelude_collision_tests`) and absent from another, in ANY of the
    three pairwise directions. Returns the agreed label count on agreement.

    This is the general form of the exact 2026-08-27 defect: a group present
    in two tools' `build_groups` and silently missing from the third's is the
    same failure whichever tool is short, so all three are compared, not just
    the pair `check()` above already covers.
    """
    sets = {
        "kernel_declaration_projection": kdp_labels,
        "prelude_theorem_inventory": pti_labels,
        "cross_prelude_collision_tests": collision_labels,
    }
    all_labels = set().union(*sets.values())
    problems = []
    for label in sorted(all_labels):
        present = sorted(name for name, s in sets.items() if label in s)
        missing = sorted(name for name in sets if name not in present)
        if missing:
            problems.append(f"  {label!r}: present in {present}, MISSING from {missing}")
    if problems:
        raise CompletenessError(
            "prelude group label sets disagree across the three build_groups "
            "implementations (kernel_declaration_projection, "
            "prelude_theorem_inventory, cross_prelude_collision_tests) -- one "
            "of them never builds a prelude group the others do:\n"
            + "\n".join(problems)
        )
    return len(all_labels)


def _run(command: str) -> str:
    completed = subprocess.run(
        command, shell=True, cwd=ROOT, capture_output=True, text=True, check=False
    )
    if completed.returncode != 0:
        raise CompletenessError(f"{command!r} failed: {completed.stderr.strip()[-400:]}")
    return completed.stdout


def check(kdp_stdout: str, pti_stdout: str) -> tuple[int, int]:
    """Raise `CompletenessError` naming every theorem the two tools disagree
    on. Returns `(kdp_count, pti_count)` on agreement.

    Agreement is required in BOTH directions: a name `kernel_declaration_
    projection` sees that `prelude_theorem_inventory` does not is exactly the
    2026-08-27 defect (a whole prelude group `prelude_theorem_inventory`
    never built); the reverse would mean `kernel_declaration_projection` is
    now the one with a coverage gap. Neither is acceptable silently.
    """
    kdp = kdp_theorem_names(kdp_stdout)
    pti = pti_theorem_names(pti_stdout)
    kdp_only = sorted(kdp - pti)
    pti_only = sorted(pti - kdp)
    if kdp_only or pti_only:
        lines = [
            f"theorem inventories disagree: kernel_declaration_projection has "
            f"{len(kdp)} distinct theorems, prelude_theorem_inventory has "
            f"{len(pti)}."
        ]
        if kdp_only:
            shown = ", ".join(kdp_only[:10]) + (" ..." if len(kdp_only) > 10 else "")
            lines.append(
                f"  {len(kdp_only)} in kernel_declaration_projection only "
                f"(missing from prelude_theorem_inventory's build_groups): {shown}"
            )
        if pti_only:
            shown = ", ".join(pti_only[:10]) + (" ..." if len(pti_only) > 10 else "")
            lines.append(
                f"  {len(pti_only)} in prelude_theorem_inventory only "
                f"(missing from kernel_declaration_projection's build path): {shown}"
            )
        raise CompletenessError("\n".join(lines))
    return len(kdp), len(pti)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--kdp-tsv",
        type=Path,
        help="substitute file for kernel_declaration_projection's stdout (testing)",
    )
    parser.add_argument(
        "--pti-tsv",
        type=Path,
        help="substitute file for prelude_theorem_inventory's stdout (testing)",
    )
    parser.add_argument(
        "--collision-source",
        type=Path,
        help=(
            "substitute file for cross_prelude_collision_tests.rs's own "
            "source text (testing)"
        ),
    )
    args = parser.parse_args()
    try:
        kdp_stdout = (
            args.kdp_tsv.read_text(encoding="utf-8") if args.kdp_tsv else _run(KDP_COMMAND)
        )
        pti_stdout = (
            args.pti_tsv.read_text(encoding="utf-8") if args.pti_tsv else _run(PTI_COMMAND)
        )
        collision_source = (
            args.collision_source.read_text(encoding="utf-8")
            if args.collision_source
            else COLLISION_SOURCE.read_text(encoding="utf-8")
        )
        kdp_count, _pti_count = check(kdp_stdout, pti_stdout)
        kdp_labels = kdp_prelude_labels(kdp_stdout)
        pti_labels = pti_prelude_labels(pti_stdout)
        collision_labels = collision_group_labels(collision_source)
        label_count = check_group_labels(kdp_labels, pti_labels, collision_labels)
    except CompletenessError as error:
        print(f"THEOREM_INVENTORY_COMPLETENESS_ERROR: {error}", file=sys.stderr)
        return 1
    print(f"THEOREM_INVENTORY_COMPLETENESS_OK: {kdp_count} distinct theorem names agree")
    print(
        f"THEOREM_INVENTORY_COMPLETENESS_OK: {label_count} prelude-group labels "
        "agree across all three build_groups implementations"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Every control test must be executed by something.

CLAUDE.md: *"at N lanes the ledger IS the product, so a checker that cannot fail
is worse than no checker."* This is the layer below that. The controls under
`scripts/tests/` are what make the checkers falsifiable — each one drives a guard
to failure so we know the guard discriminates. A control that no gate runs is
worth exactly as much as a guard that cannot fail, and is far harder to notice:
the file exists, it is committed, it passes when you run it by hand, and nothing
anywhere runs it.

Measured 2026-08-17: **63 of 137 control modules are executed by nothing in the
repository.** Not by `justfile`, not by `scripts/check.sh`, not by any workflow,
not by any other script. Running the 51 that need no cargo found 264 tests, of
which 258 pass and would have been gated for free — and 7 do not pass.

Measured individually, the seven are less dramatic than the batch run suggested
and worth stating exactly: **five are pytest-style and `pytest` is not installed
here**, so they fail to import rather than having rotted; one
(`test_diagnose_maestro_llvm_root_drift`) passes in a batch and fails alone, so
it has an order dependency; and exactly one has genuinely rotted —
`test_validate_glaurung_llvm_loop_semantic_census` fails with
`ResultValidationError: producer drift: Cargo.lock`. One rotted control is a
smaller finding than "six broken", and it is the true one.

The cause is mechanical, not anyone's oversight. The runners name modules **one
by one** — `justfile` alone names 91 — so wiring a new control is a second,
separate, forgettable step. Nothing ever checked that the two lists agree.

# What this enforces

Only reachability: each `scripts/tests/test_*.py` must appear on a line that
also mentions `unittest` or `pytest`, in some tracked file outside
`scripts/tests/` — i.e. somebody actually runs it. It does NOT run the tests
(the gates that name them do that), and it does not care which runner claims a
module.

It is a **ratchet**: `ORPHAN_BASELINE` may only go DOWN. Wiring the existing 63
is real work with real failures to fix, and blocking every unrelated commit
until that is finished would just get the gate deleted. What it stops today is
the count going UP — a NEW control that nothing runs.

# What the remaining 14 are

Re-characterised 2026-08-25, after the count grew from 19 to 30 (ten new
`check-autogenesis-*` one-off audit/coverage controls landed and were never
wired, plus one lane's own many-control `test_lane_merge_additive` suite for
`scripts/lane-merge-additive.py` — that one adopted immediately, bringing 30
down to 29 before this pass) and was brought back down to 14. Of the 11 `tock-log2` /
`maestro-device-id` controls that were unregistered at the 2026-08-17
measurement, 7 turned out to be live, passing, unittest-based guards over
scripts that are still cross-referenced by later generations in the same
investigation chain (`prepare-tock-log2-cache-v2.py` imports
`capture-tock-log2.py` directly, for example) — deleting the "superseded"
generations would have broken the ones that import them, so all 7 are now
registered instead. The 5 `check-autogenesis-*` result/plan controls with live,
unchanged targets are registered too.

What remains at 14 is not a backlog of coverage, it is four distinct kinds of
resistance:

- **Seven are pytest-style, and a pytest interpreter is not installed here.**
  (`test_capture_maestro_device_id`, its `_v2`/`_v3` generations,
  `test_diagnose_maestro_llvm_root_drift`, `test_qf_linear_a5_census`,
  `test_qf_nia_a3_census`, `test_qf_uflia_a4_census`.) NB this paragraph
  deliberately keeps the module-import keyword and any module name off the
  SAME line — this scanner does not special-case its own docstring, so a line
  combining both would have silently credited the module as "run" the way a
  runner-line comment used to (see the note on comment lines below). Each of
  the seven does not import under the plain `python3 -m unittest` convention
  every other control in this repository uses, because they use `pytest`
  fixtures (`tmp_path`, `monkeypatch`, `pytest.raises`) that only a pytest
  collector provides. That collector is a declared dev dependency
  (`uv sync --dev` would put it in `.venv`), but no other `scripts/tests/`
  control has ever been wired through it; adopting these first would mean
  building a second gate pathway, which is a decision for whoever owns that
  investigation.
- **Four are `prove-tock-log2*` (all four generations)** — every one fails
  identically: their frozen registration
  (`bench-results/verify-tock-log2-20260721/proof-v1-registration.json`) pins a
  SHA-256 of `crates/axeyum-verify/tests/tock_log2_external.rs` that has
  drifted in committed history since the freeze. Re-freezing that registration
  is a decision for whoever owns the Tock proof, not something this gate can
  paper over.
- **Two are `check-autogenesis-*-plan` controls whose target fact has moved
  on**: `test_check_autogenesis_nat_fib_gcd_surface_plan` and
  `test_check_autogenesis_nat_gcd_greatest_plan` both fail closed with "target
  fact identity/open state changed" — the plan checker correctly refuses to
  validate a stale plan against a fact ledger entry that has since settled.
- **One is the single genuinely rotted control found in the 2026-08-17
  sweep, still rotted**: `test_validate_glaurung_llvm_loop_semantic_census`
  still fails with `ResultValidationError: producer drift: Cargo.lock`.

A module naming itself proves nothing, so `scripts/tests/` is excluded from the
search. `scripts/check-aggregate-scope.expected` is a pinned inventory of gate
steps rather than a runner, but it is derived from the runners and excluding it
would not change the count, so it is left in.
"""

from __future__ import annotations

import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
TESTS = ROOT / "scripts/tests"

# Measured 2026-08-25, after registering 15 of the 29 orphans this ratchet found
# red (`test_validate_facts`, `test_gen_autogenesis_knowledge_coverage`,
# `test_validate_autogenesis_capability_candidate_demand`, 5 live
# `check-autogenesis-*` result/plan controls, and 7 `tock-log2` capture/cache
# controls whose scripts are still cross-referenced by later generations). The
# remaining 14 are characterised above ("What the remaining 14 are") rather than
# left as a bare number. Previously 19, measured 2026-08-17.
# MAY ONLY GO DOWN.
ORPHAN_BASELINE = 14
# The controls exist; if this collapses, the glob is wrong and every count lies.
MIN_MODULES = 130

SKIP_SUFFIX = {".smt2", ".cnf", ".json", ".dimacs", ".drat", ".png", ".gz"}


def modules() -> set[str]:
    return {p.stem for p in TESTS.glob("test_*.py")}


def tracked() -> list[str]:
    out = subprocess.run(
        ["git", "ls-files"], cwd=ROOT, capture_output=True, text=True, check=True
    ).stdout.split()
    return [f for f in out if not f.startswith("scripts/tests/")]


def logical_lines(text: str) -> list[str]:
    r"""Join shell/`make` line continuations before scanning.

    A runner that lists forty modules writes one per line under a trailing `\`,
    so only the FIRST shares a physical line with the word `unittest`. Scanning
    physically counted 3 of 44 when this was measured — the gate would have
    reported the modules as orphaned while a gate was demonstrably running them,
    and the fix that suggests itself (reformat the runner onto one line) hides a
    scanner bug behind a style rule.
    """
    out: list[str] = []
    buf = ""
    for raw in text.splitlines():
        if raw.rstrip().endswith("\\"):
            buf += raw.rstrip()[:-1] + " "
            continue
        out.append(buf + raw)
        buf = ""
    if buf:
        out.append(buf)
    return out


def modules_run_by(mods: set[str], text: str) -> set[str]:
    """Which of `mods` this file actually RUNS.

    The discriminator: a module named on a line that also says `unittest` or
    `pytest` is executed; a module merely *mentioned* — in prose, in a comment,
    in a status table — is not. Without this distinction the gate would count a
    doc reference as coverage, which is the exact confusion it exists to catch.
    """
    hits: set[str] = set()
    for line in logical_lines(text):
        if line.lstrip().startswith("#"):
            # A COMMENT naming a module is a mention, however runner-ish it
            # looks. Found by this gate contradicting itself: the adopted-controls
            # script documents its exclusions with "pytest-style; `pytest` is not
            # installed", so those comment lines contained the word `pytest`,
            # qualified as runner lines, and vouched for the exact modules the
            # comment says are NOT run. Two modules were counted as covered
            # because a comment explained why they were not.
            continue
        if "unittest" not in line and "pytest" not in line:
            continue
        hits.update(mod for mod in mods if mod in line)
    return hits


def evaluate(mods: set[str], runs: dict[str, set[str]]) -> list[str]:
    """The ratchet decision, separated so it can be driven to failure in tests."""
    orphans = sorted(mods - set(runs))
    failures: list[str] = []
    if len(mods) < MIN_MODULES:
        failures.append(
            f"found only {len(mods)} control modules (floor {MIN_MODULES}); the glob has "
            "stopped matching and an orphan count of zero would mean nothing"
        )
    elif len(orphans) > ORPHAN_BASELINE:
        listing = "\n    ".join(orphans[:20])
        failures.append(
            f"{len(orphans)} control modules are executed by nothing, above the baseline "
            f"of {ORPHAN_BASELINE}. A control that no gate runs cannot fail, so it is not "
            "a control. Name it in `justfile`/`scripts/check.sh` on a line that runs it:"
            f"\n    {listing}"
        )
    return failures


def executed(mods: set[str], files: list[str]) -> dict[str, set[str]]:
    """`module -> {file that runs it}`, by looking for it on a runner line."""
    found: dict[str, set[str]] = {}
    for rel in files:
        path = ROOT / rel
        if path.suffix in SKIP_SUFFIX or not path.is_file():
            continue
        try:
            text = path.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            continue
        for mod in modules_run_by(mods, text):
            found.setdefault(mod, set()).add(rel)
    return found


def main(argv: list[str]) -> int:
    mods = modules()
    runs = executed(mods, tracked())
    orphans = sorted(mods - set(runs))

    if "--list" in argv:
        for name in orphans:
            print(f"  orphan: {name}")

    print(
        f"CONTROL_TESTS_REACHABLE|modules={len(mods)}|executed={len(runs)}|"
        f"orphaned={len(orphans)}|baseline={ORPHAN_BASELINE}"
    )

    failures = evaluate(mods, runs)
    for failure in failures:
        print(f"CONTROL_TESTS_REACHABLE_ERROR|{failure}", file=sys.stderr)
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))

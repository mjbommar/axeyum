#!/usr/bin/env python3
"""ADR-1050: the seven L0 safety gates must run in an AUTOMATED context.

Measured 2026-08-31, with positive controls in the same run so a zero could
not be a broken query (`ci.yml` names `scripts/` 44 times, `hooks/pre-push` 28,
`scripts/local-ci.sh` 10): **all seven L0 gates were referenced ZERO times** in
`.github/workflows/ci.yml`, `hooks/pre-push` and `scripts/local-ci.sh` alike.
They ran only from `scripts/check.sh` and the `justfile` -- that is, only when
a human typed a command. Nothing stopped a change that breaks statement
identity, admits a circular trust closure, contaminates the blind-evaluation
partition or silently drops a semantic control from reaching `main`.

This gate exists so that cannot silently come back. It checks WIRING, not the
gates' own findings -- those are each gate's job.

Eight guards, each of which fails naming the gate it is about:

  G1  every L0 gate appears in at least one CI `run:` step
  G2  no L0 CI step carries `continue-on-error: true`
  G3  no L0 step's command swallows its failure (`|| true`, `|| :`, `; true`)
  G4  the three sub-two-second gates appear in `hooks/pre-push`
  G5  the pre-push L0 block runs BEFORE the Rust/TOML early exit
  G6  the pre-push block reacts to a nonzero exit (it must not be a bare call
      whose failure `set -e` alone might not surface through the loop)
  G7  all seven gates appear in `scripts/local-ci.sh` -- the file ci.yml
      itself calls "the authoritative gate for main"
  G8  every L0 line in `scripts/local-ci.sh` actually feeds `rc` (`|| rc=$?`)
      rather than being a bare call `set -uo pipefail` won't catch, or a
      swallowed one (`|| true`)

G2 and G3 are separate on purpose. `ci.yml` legitimately carries
`continue-on-error: true` on two lean-parity steps for a documented reason, so
the property is not "this file has no continue-on-error" but "no L0 step has
one". G3 catches the same swallowing spelled inside the command instead.

G5 is the one that encodes the actual finding rather than a tidiness rule. The
hook exits early when no `*.rs`/`*.toml`/`Cargo.lock` changed, and every L0
gate guards JSON and documentation content -- `artifacts/facts/`, the
proposition corpus, the credit ledger, the nursery partition. Below that exit,
a push touching only the content these gates protect is gated by nothing.

G8 is the local-ci.sh analogue of G3/G6, and it has to check for something
different from either: `scripts/local-ci.sh` runs under `set -uo pipefail`,
not `set -e`, and every other step in it uses `run <cmd> || rc=$?` precisely
because a bare `run <cmd>` would let that step's nonzero return vanish without
touching `rc` at all -- no `||` needed for the swallow. So G8 requires the
`|| rc=$?` suffix on every L0 line, which refuses both that silent drop and an
explicit `|| true`.

Usage:
    scripts/check-l0-gate-enforcement.py            # run the gate
    scripts/check-l0-gate-enforcement.py --self-test # prove each guard fires
"""

from __future__ import annotations

import argparse
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
CI = ROOT / ".github/workflows/ci.yml"
PREPUSH = ROOT / "hooks/pre-push"
LOCAL_CI = ROOT / "scripts/local-ci.sh"

# The seven L0 trusted-library safety gates (ADR-0717 and successors).
L0_GATES = (
    "check-trust-closure",
    "check-settled-fact-statements",
    "check-semantic-control-fixtures",
    "check-kernel-differential",
    "check-credit-transaction-ledger",
    "check-proposition-duplication",
    "check-holdout-closed-evaluation",
)

# The subset cheap enough to run in front of every push. Measured warm on s4:
# 0.09s, 0.06s and 1.09s respectively, against a battery documented at ~545s.
# The other four cost 10.6s / 7-27s / 55-72s / 58s and run in CI instead.
PREPUSH_GATES = (
    "check-settled-fact-statements",
    "check-holdout-closed-evaluation",
    "check-semantic-control-fixtures",
)

# The line the L0 block must sit ABOVE in hooks/pre-push.
EARLY_EXIT = 'exit 0 # docs/bench-results/scripts-only push'

SWALLOW = re.compile(r"\|\|\s*(true|:)\s*$|;\s*true\s*$", re.MULTILINE)

# G8: the exact suffix scripts/local-ci.sh's own idiom requires. Every other
# step in that file is `run <cmd> || rc=$?`; anything else -- a bare call, or
# `|| true` -- lets the step's failure vanish under `set -uo pipefail`.
RC_CAPTURE = re.compile(r"\|\|\s*rc=\$\?\s*$")


def strip_comments(text: str) -> str:
    """Shell source with whole-line comments removed.

    Only full-line comments are dropped. A trailing `# ...` on a real command
    is left alone: it cannot make an absent gate look present, and removing it
    would need shell-aware quoting.
    """
    return "\n".join(
        ln for ln in text.splitlines() if not ln.lstrip().startswith("#"))


def ci_steps(text: str) -> list[tuple[str, bool]]:
    """`(run-command, carries-continue-on-error)` for every `- run:` step.

    Parsed by structure rather than with a YAML library so this gate has no
    dependency the CI runner might not have, and so a `run:` inside a block
    scalar is still seen. A step's `continue-on-error` may appear on either
    side of its `run:`, so the whole step block is scanned.
    """
    steps: list[tuple[str, bool]] = []
    lines = text.splitlines()
    starts = [i for i, ln in enumerate(lines) if re.match(r"\s*- (name|run|uses):", ln)]
    for idx, start in enumerate(starts):
        end = starts[idx + 1] if idx + 1 < len(starts) else len(lines)
        block = "\n".join(lines[start:end])
        if not re.search(r"^\s*-?\s*run:", block, re.MULTILINE):
            continue
        coe = re.search(r"^\s*continue-on-error:\s*true\s*$", block, re.MULTILINE) is not None
        steps.append((block, coe))
    return steps


def check(ci_text: str, prepush_text: str, local_ci_text: str) -> list[str]:
    failures: list[str] = []
    steps = ci_steps(ci_text)

    # A gate that examined zero steps would pass G1..G3 vacuously.
    if not steps:
        return ["VACUOUS: parsed zero CI run-steps -- the CI parser is broken, "
                "not the wiring"]

    for gate in L0_GATES:
        hits = [(block, coe) for block, coe in steps if gate in block]
        if not hits:                                              # GUARD:G1
            failures.append(
                f"G1 not-in-ci: `{gate}` appears in no CI run-step. The L0 "
                f"safety programme must run without a human typing a command.")
            continue
        for block, coe in hits:
            if coe:                                               # GUARD:G2
                failures.append(
                    f"G2 continue-on-error: `{gate}` is wired with "
                    f"`continue-on-error: true`. A safety gate whose failure "
                    f"is swallowed manufactures the appearance of enforcement.")
            if SWALLOW.search(block):                             # GUARD:G3
                failures.append(
                    f"G3 swallowed: `{gate}`'s CI command discards its exit "
                    f"status (`|| true` / `; true`).")

    # Comments do not gate anything. Matching the whole file would let a gate
    # that survives only in the block comment above the loop read as wired --
    # which is exactly what the first version of this script did, and its
    # own self-test caught it.
    code = strip_comments(prepush_text)

    for gate in PREPUSH_GATES:
        if gate not in code:                                      # GUARD:G4
            failures.append(
                f"G4 not-in-pre-push: `{gate}` is cheap enough to gate every "
                f"push and is absent from hooks/pre-push's executable lines.")

    exit_at = code.find(EARLY_EXIT)
    present = [g for g in PREPUSH_GATES if g in code]
    if present and exit_at == -1:
        failures.append(
            "G5 anchor-missing: the pre-push early-exit line was not found, "
            "so the L0 block's placement cannot be verified")
    elif present:
        # rindex, not index: the property is that EVERY invocation sits above
        # the early exit. With first-occurrence, adding a second call below it
        # would leave the guard silent -- and the self-test case for G5 is
        # exactly that shape, which is how this was caught.
        last = max(code.rindex(g) for g in present)
        if last > exit_at:                                        # GUARD:G5
            failures.append(
                "G5 below-early-exit: the L0 block runs AFTER the Rust/TOML "
                "early exit, so a push touching only artifacts/ or docs/ -- "
                "exactly the content these gates protect -- skips them.")

    if SWALLOW.search(prepush_text) or "L0 gate rejected this push" not in prepush_text:
        failures.append(                                          # GUARD:G6
            "G6 no-failure-path: the pre-push L0 block has no branch that "
            "fails the push on a nonzero gate exit.")

    # scripts/local-ci.sh -- the file ci.yml calls "the authoritative gate for
    # main" -- must run all seven, and each must feed `rc` the same way every
    # other step in that file does.
    lci_code = strip_comments(local_ci_text)
    lci_lines = lci_code.splitlines()

    for gate in L0_GATES:
        gate_lines = [ln for ln in lci_lines if gate in ln]
        if not gate_lines:                                        # GUARD:G7
            failures.append(
                f"G7 not-in-local-ci: `{gate}` appears in no executable line "
                f"of scripts/local-ci.sh.")
            continue
        if not any(RC_CAPTURE.search(ln) for ln in gate_lines):    # GUARD:G8
            failures.append(
                f"G8 not-captured-in-local-ci: `{gate}`'s scripts/local-ci.sh "
                f"invocation does not end in `|| rc=$?`, so its failure would "
                f"not reach the script's exit status under `set -uo pipefail` "
                f"(no `set -e`).")

    return failures


def self_test() -> list[str]:
    """Each guard must fire on the input that names it, and only then."""
    ci = CI.read_text(encoding="utf-8")
    pp = PREPUSH.read_text(encoding="utf-8")
    lci = LOCAL_CI.read_text(encoding="utf-8")
    bad: list[str] = []

    if check(ci, pp, lci):
        bad.append("all-clear: the committed tree must pass")

    cases = [
        ("G1", ci.replace("python3 scripts/check-trust-closure.py --quiet\n", "", 1), pp, lci),
        ("G2", ci.replace(
            "      - run: python3 scripts/check-proposition-duplication.py",
            "      - run: python3 scripts/check-proposition-duplication.py\n"
            "        continue-on-error: true", 1), pp, lci),
        ("G3", ci.replace(
            "- run: python3 scripts/check-settled-fact-statements.py",
            "- run: python3 scripts/check-settled-fact-statements.py || true", 1), pp, lci),
        ("G4", ci, pp.replace(
            '  "scripts/check-holdout-closed-evaluation.py" \\\n', "", 1), lci),
        ("G6", ci, pp.replace("L0 gate rejected this push", "all fine", 1), lci),
        ("G7", ci, pp, lci.replace(
            "run python3 scripts/check-trust-closure.py --quiet || rc=$?\n", "", 1)),
        ("G8", ci, pp, lci.replace(
            "run python3 scripts/check-holdout-closed-evaluation.py || rc=$?",
            "run python3 scripts/check-holdout-closed-evaluation.py || true", 1)),
    ]
    for tag, c, p, l in cases:
        hits = [f for f in check(c, p, l) if f.startswith(tag)]
        if not hits:
            bad.append(f"{tag}: guard did not fire on its own case")

    # G5: append a real (non-comment) reference to a pre-push gate BELOW the
    # early exit, so the last executable mention sits after it.
    moved = pp + f'\npython3 scripts/{PREPUSH_GATES[0]}.py\n'
    if not [f for f in check(ci, moved, lci) if f.startswith("G5")]:
        bad.append("G5: guard did not fire on its own case")

    if not [f for f in check("", pp, lci) if f.startswith("VACUOUS")]:
        bad.append("VACUOUS: the zero-steps guard did not fire")
    return bad


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true",
                        help="prove each guard fires on the case that names it")
    args = parser.parse_args()

    if args.self_test:
        bad = self_test()
        for item in bad:
            print(f"SELF-TEST FAILED: {item}", file=sys.stderr)
        print(f"L0_GATE_ENFORCEMENT|self-test|cases=9|failures={len(bad)}")
        return 1 if bad else 0

    failures = check(CI.read_text(encoding="utf-8"),
                     PREPUSH.read_text(encoding="utf-8"),
                     LOCAL_CI.read_text(encoding="utf-8"))
    steps = len(ci_steps(CI.read_text(encoding="utf-8")))
    print(f"L0_GATE_ENFORCEMENT|gates={len(L0_GATES)}|pre_push_gates="
          f"{len(PREPUSH_GATES)}|local_ci_gates={len(L0_GATES)}|"
          f"ci_run_steps={steps}|verdict={'FAIL' if failures else 'PASS'}")
    for item in failures:
        print(f"  {item}", file=sys.stderr)
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())

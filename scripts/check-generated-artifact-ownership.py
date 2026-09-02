#!/usr/bin/env python3
"""One producer per key: a generated artifact may have exactly one writer.

WHY THIS EXISTS (ADR-0652). `artifacts/autogenesis/
mathlib-statable-vocabulary-v1.json` had two.
`gen-autogenesis-statable-vocabulary.py` owns it and emits
`bridge_provenance` and `row_digest` -- ADR-0631's per-constant
classification, the measurement behind `elaboration 50 / expressed 2 /
elided 8 / unrendered 12`. `gen-autogenesis-nursery-refill.py` built a
poorer copy of the same document and wrote it over the top, deleting both
keys, AT EXIT 0. Its own `--check` then reported the file stale and advised
"regenerate without --check", whose only effect on that file was the
deletion. Reproduced at `main`: sha 096d8c85 -> 27205641.

That is this repository's shared-append-point failure -- the one CLAUDE.md
records for `PLAN.md` and the ADR index -- arriving in an artifact rather
than a document, and the remedy is the same: one owner, made structural.

WHAT THIS CHECKS, AND WHY IT IS EMPIRICAL RATHER THAN STATIC. The destroying
write was NOT `VOCABULARY.write_text(...)`. It was

    outputs = {VOCABULARY: render(vocabulary), EXTENSION: render(extension)}
    for path, text in outputs.items():
        path.write_text(text)

so the path constant reaches a write through a dict value, and any static
receiver analysis a person would actually write misses it. So the ownership
arm RUNS each non-owner producer in a sandboxed copy of the tree and
compares bytes. Static analysis appears only where it is decidable: a script
may be declared read-only only if it contains NO write call at all.

THE ARMS
  KEYS   the committed artifact carries every required key, top level and
         nested. This is the arm that would have gone red the moment
         `bridge_provenance` was dropped, whoever dropped it.
  READS  every script declared read-only really has no write call (AST).
  INVOKES a script that only STAGES the artifact and regenerates it by
         calling the OWNER. Verified by inspection, like READS: every line
         reaching the artifact's name is a git staging line, and the owner's
         path appears in the script.
  RUNS   every other producer, executed in a sandbox, leaves the guarded
         artifact byte-identical.
  OWNER  the owner, executed in the same sandbox over a PERTURBED copy,
         restores it byte-for-byte. This is the positive control for RUNS:
         without it, RUNS would pass on a sandbox that no script reached.
  KNOWN  every script mentioning a guarded artifact is classified, and every
         classified script still mentions it. Derived from the tree, so a
         NEW writer turns this red instead of being silently unmeasured.
  CTRL   a synthetic second writer is planted in the sandbox and RUNS must
         reject it. A check that cannot fail is worse than no check, so this
         runs on every invocation and is not opt-in.

Exit 0 when every arm passes, 1 on any FAIL.
"""

from __future__ import annotations

import argparse
import ast
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile
from typing import Any, NamedTuple

ROOT = pathlib.Path(__file__).resolve().parents[1]
SELF = "scripts/check-generated-artifact-ownership.py"

# This gate names the artifacts it guards, so DISCOVERY finds it and KNOWN
# demands it be classified. It is classified as a `runs` producer like any
# other -- the property "running this script does not rewrite the artifact" is
# exactly what needs measuring, and this script does perform writes (a sandbox
# tree, a perturbed copy, a planted control). Left unbounded that recurses: the
# sandbox copy would run its own copy for ever. So a nested invocation inherits
# this variable and skips only ITSELF, running every other arm unchanged.
NEST = "AXEYUM_ARTIFACT_OWNERSHIP_NESTED"
NESTED = os.environ.get(NEST) == "1"

# Directories the sandbox needs. Every guarded producer resolves its own ROOT
# as `parents[1]` of `__file__`, so a copy of these two under a scratch root
# is a complete working tree for them.
#
# `crates` joined them on 2026-09-02, for `frontier-shape-census-v1.json`. Its
# producer runs `fact-frontier.py --json`, which validates the operation
# registry, and that validation checks that every operation's
# `producer.implementation` / `checker.implementation` PATH EXISTS -- all of
# them under `crates/`. Without the tree the frontier exits 1, the census
# reports UNANSWERABLE (exit 2), and the OWNER arm reads that as "did not
# restore" -- a gate red because its sandbox was too small, which says nothing
# about ownership. Source only: 59 MB, one copy per run (the sandbox is built
# once), against the 333 MB the other two trees already cost.
SANDBOX_TREES = ("artifacts", "scripts", "crates")


class Producer(NamedTuple):
    """A script that is RUN in the sandbox, with the argv that makes it write."""

    path: str
    argv: tuple[str, ...]
    note: str


class ReadOnly(NamedTuple):
    """A script declared read-only. Verified: it must contain no write call."""

    path: str
    note: str


class Invoker(NamedTuple):
    """A script that only STAGES the artifact and regenerates it by calling
    the owner. Verified by inspection; never executed. See INVOKES below."""

    path: str
    note: str


class Artifact(NamedTuple):
    path: str
    owner: Producer
    required_keys: tuple[str, ...]
    required_nested: dict[str, tuple[str, ...]]
    runs: tuple[Producer, ...]
    reads: tuple[ReadOnly, ...]
    # Trailing and defaulted so an artifact with no orchestrator is written
    # exactly as before. An unclassified one is caught by KNOWN either way.
    invokes: tuple[Invoker, ...] = ()


GUARDED: tuple[Artifact, ...] = (
    Artifact(
        path="artifacts/autogenesis/mathlib-statable-vocabulary-v1.json",
        owner=Producer(
            "scripts/gen-autogenesis-statable-vocabulary.py",
            ("--write",),
            "ADR-0624. The sole writer. Emits bridge_provenance (ADR-0631) "
            "and row_digest, which no other producer derives.",
        ),
        # Every top-level key the owner emits. Named individually rather than
        # counted: a count cannot say WHICH key went missing, and the two that
        # went missing are the two that carry a published measurement.
        required_keys=(
            "bridge",
            "bridge_provenance",
            "coverage",
            "derivation",
            "environment_snapshot",
            "keyed_by",
            "kind",
            "row_digest",
            "schema_version",
            "settled",
            "source",
        ),
        required_nested={
            # The four tier counts behind "elaboration 50 / expressed 2 /
            # elided 8 / unrendered 12" and the conservative statable count.
            # The second writer dropped exactly these four and kept the rest,
            # so a top-level `coverage` key alone is not enough.
            "coverage": (
                "bridge_constants",
                "bridge_elaboration",
                "bridge_elided",
                "bridge_expressed",
                "bridge_unrendered",
                "catalogued_propositions",
                "distinct_constants",
                "open_propositions",
                "settled_propositions",
            ),
        },
        runs=(
            Producer(
                "scripts/gen-autogenesis-nursery-refill.py",
                (),
                "The former second writer. Bare argv is the DRAW invocation "
                "-- the one that destroyed the file -- not --check, which "
                "never writes and so would prove nothing.",
            ),
            Producer(
                "scripts/propose-nursery-refill.py",
                ("--remeasure",),
                "Writes refill-headroom-v1.json. Run in its WRITING mode so "
                "the sandbox is demonstrably reachable by this script while "
                "the guarded artifact stays untouched.",
            ),
            Producer(
                "scripts/tests/test-gen-autogenesis-statable-vocabulary.sh",
                (),
                "Deliberately mutates the tracked artifact and restores it. "
                "Run here so the restore is measured rather than trusted.",
            ),
            Producer(
                SELF,
                (),
                "This gate itself. It writes -- a sandbox, a perturbed copy, "
                "a planted control -- so it cannot be declared read-only, and "
                "`running it must not rewrite the artifact` is a property "
                "worth measuring. The nested run skips only itself.",
            ),
        ),
        reads=(
            ReadOnly(
                "scripts/check-autogenesis-holdout-isolation.py",
                "Resolves source_name through the catalog; no write call.",
            ),
            ReadOnly(
                "scripts/check-dispatchable-frontier.py",
                "Reads the bridge to decide statability; no write call.",
            ),
            ReadOnly(
                "scripts/measure-bridge-elision-radius.py",
                "Reads bridge_provenance to measure the elision radius; "
                "no write call.",
            ),
        ),
    ),
    Artifact(
        path="artifacts/autogenesis/frontier-shape-census-v1.json",
        owner=Producer(
            "scripts/frontier-shape-census.py",
            (),
            "The sole writer. Bare argv is the WRITING invocation; --check "
            "never writes and so would prove nothing about ownership.",
        ),
        # The keys a reader of this artifact reasons from. `population` and
        # `buckets` carry the measurement; `environment_snapshot` says which
        # kernel environment the declared-constant flags were read against, and
        # a census whose flags cannot be attributed to an environment is not
        # evidence about statability.
        required_keys=(
            "authority",
            "buckets",
            "environment_snapshot",
            "frontier",
            "kind",
            "ledger",
            "other",
            "population",
            "produced_by",
            "schema_version",
        ),
        required_nested={
            # The held-out accounting specifically. If `held_out_excluded` or
            # `held_out_authority` were ever dropped, the artifact would still
            # look complete while no longer showing that a blind evaluation
            # population was excluded at all -- which is the one property a
            # reader must be able to check without rerunning anything.
            "population": (
                "by_route_class",
                "censused_count",
                "held_out_authority",
                "held_out_excluded",
                "held_out_source_gap",
                "primary_count",
                "primary_mutation_control_count",
                "primary_targetable_count",
                "ready_count",
            ),
            "buckets": ("coarse", "fine"),
        },
        runs=(
            Producer(
                SELF,
                (),
                "This gate itself, for the same reason it is listed above: it "
                "writes a sandbox and a perturbed copy, so it cannot be "
                "declared read-only.",
            ),
            Producer(
                "scripts/check-merge-hygiene.sh",
                (),
                "Gates the artifact with --check and names it in its remedy "
                "line. A bash script cannot be proved write-free by AST, so "
                "the property is MEASURED here instead of asserted.",
            ),
            Producer(
                "scripts/tests/test_frontier_shape_census.py",
                (),
                "The census's own controls. They build throwaway trees and "
                "write census artifacts INSIDE them; that the real one is "
                "untouched is exactly what this arm measures.",
            ),
            Producer(
                "scripts/tests/test_check_merge_hygiene.py",
                (),
                "Names the artifact in its assertion on the gate's remedy "
                "line. Drives the shipped gate against a throwaway tree.",
            ),
        ),
        reads=(),
        invokes=(
            Invoker(
                "scripts/lane-merge-land.sh",
                "Names the artifact in `GENERATED` so a merge conflict on it "
                "is cleared with `git checkout --theirs` and the result "
                "staged, then regenerates it by running the OWNER. Running a "
                "merge driver in the ownership sandbox would measure nothing "
                "and `reads` is false (it redirects and stages), so the "
                "property is checked by inspection instead.",
            ),
        ),
    ),
    Artifact(
        path="artifacts/autogenesis/partition-edge-baseline-v1.json",
        owner=Producer(
            "scripts/check-partition-edges.py",
            ("--record-baseline",),
            "ADR-1550. The sole writer, and the only mode of it that writes: "
            "the default and --baseline modes never touch the file. The "
            "recorded edge set is what `--baseline` ratchets against, so a "
            "second writer here is not a stale artifact -- it is a partition "
            "breach that stops being reported.",
        ),
        # The provenance keys are named individually because they are the ones
        # a reader argues with. `edges` alone would still look like a baseline
        # after a rewrite that dropped what it was measured against, and a
        # baseline whose recording date and ledger digest are gone cannot be
        # checked for having only shrunk -- which is the ADR's whole rule.
        #
        # `schema_version` is LAST deliberately: the OWNER arm perturbs the
        # committed file by popping `required_keys[-1]` and then demands a
        # byte-identical restore, and the regenerator carries `recorded_date`,
        # `recorded_at_commit` and `ledger_sha256` forward from the file it
        # finds. Popping one of THOSE would make the restore honest and the
        # arm still red, for a reason about this list rather than about
        # ownership.
        required_keys=(
            "authority",
            "edge_count",
            "edge_set_sha256",
            "edges",
            "held_out_salt",
            "kind",
            "ledger_sha256",
            "manifests",
            "produced_by",
            "recorded_at_commit",
            "recorded_date",
            "rule",
            "schema_version",
        ),
        required_nested={},
        runs=(
            Producer(
                SELF,
                (),
                "This gate itself, for the same reason it is listed on the "
                "two artifacts above: it writes a sandbox and a perturbed "
                "copy, so it cannot be declared read-only.",
            ),
            Producer(
                "scripts/check-merge-hygiene.sh",
                (),
                "Runs `check-partition-edges.py --baseline` as its guard 9 "
                "and names this artifact in the comment explaining it. A "
                "bash script cannot be proved write-free by AST, so the "
                "property is MEASURED here instead of asserted.",
            ),
            Producer(
                "scripts/tests/test_check_partition_edges.py",
                (),
                "The gate's own controls. They build throwaway trees and "
                "write baselines INSIDE them -- including the "
                "--record-baseline scenarios, which are the only tests in "
                "the repository that exercise this artifact's writer. That "
                "the real one is untouched is exactly what this arm "
                "measures.",
            ),
        ),
        reads=(),
    ),
    Artifact(
        path="artifacts/refactor/private-helper-census.json",
        owner=Producer(
            "scripts/private-helper-census.py",
            (),
            "The sole writer. Bare argv is the WRITING invocation; --check "
            "never writes and so would prove nothing about ownership. This is "
            "also the THIRD registry entry the COVER note above asked for -- "
            "with one entry the CTRL arm tested one comparison against one "
            "file; each further entry exercises the same machinery over a "
            "different producer set.",
        ),
        # Every top-level key the owner emits. `by_body` and `by_name` are the
        # unrestricted groupings (test fixtures included, which is why they are
        # dominated by 29 copies of `fn kernel`); `inline_steps_by_*` are the
        # hiding-place population proper. Both are required, because dropping
        # the unrestricted pair would leave the narrow one with no denominator
        # and no way for a reader to see what was filtered out.
        required_keys=(
            "schema_version",
            "kind",
            "produced_by",
            "authority",
            "by_name",
            "by_body",
            "inline_steps_by_name",
            "inline_steps_by_body",
            "population",
        ),
        required_nested={
            # The counts a reader reasons from. `private_fns` is the
            # denominator; without it a group of 12 is a number with no scale.
            # `inline_step_fns` is the narrowed denominator, and
            # `sites_in_inline_step_body_groups` is the duplication total that
            # a unification lane is measured against before and after.
            "population": (
                "files_scanned",
                "private_fns",
                "private_fns_outside_tests",
                "distinct_names",
                "distinct_body_digests",
                "duplicated_name_groups",
                "duplicated_body_groups",
                "sites_in_duplicated_body_groups",
                "inline_step_fns",
                "inline_step_name_groups",
                "inline_step_body_groups",
                "sites_in_inline_step_body_groups",
            ),
        },
        runs=(
            Producer(
                SELF,
                (),
                "This gate itself, for the same reason it is listed on the "
                "artifacts above: it writes a sandbox, a perturbed copy and a "
                "planted control, so it cannot be declared read-only.",
            ),
            Producer(
                "scripts/tests/test_private_helper_census.py",
                (),
                "The census's own controls. They PERTURB and DELETE a copy of "
                "the artifact inside a throwaway tree to prove `--check` can "
                "go red; that the tracked one is untouched by that is exactly "
                "what this arm measures rather than trusts.",
            ),
        ),
        reads=(),
        invokes=(
            Invoker(
                "scripts/lane-merge-land.sh",
                "Names the artifact in `GENERATED` so a merge conflict on it is "
                "cleared and the result staged, then regenerates it by running "
                "the OWNER. Added 2026-09-02 after three kernel merges staled "
                "the census; same shape as the shape-census entry above.",
            ),
        ),
    ),
    Artifact(
        path="artifacts/autogenesis/drawn-population-component-census-v1.json",
        owner=Producer(
            "scripts/nursery-components.py",
            ("--record",),
            "ADR-1551. The sole writer, and the only mode of it that writes: "
            "the default, --propose and --check modes never touch the file. "
            "The census is what ADR-1551's refusal of option 1 rests on, so a "
            "second writer here is not a stale artifact -- it is a partition "
            "decision whose evidence stopped being derived.",
        ),
        # `ledger_block` is named because it is the half a reader argues with,
        # and `measured_date`/`measured_at_commit` because a snapshot with no
        # provenance cannot be told from a live measurement -- which is the
        # whole reason this artifact carries the ledger block forward rather
        # than re-deriving it. `schema_version` is LAST deliberately: the
        # OWNER arm pops `required_keys[-1]` from a perturbed copy and demands
        # a byte-identical restore, and the regenerator recomputes
        # `manifest_block` while carrying `ledger_block`, `measured_date` and
        # `measured_at_commit` forward from the file it finds. Popping one of
        # THOSE would leave the restore honest and the arm still red, for a
        # reason about this list rather than about ownership.
        required_keys=(
            "authority",
            "kind",
            "ledger_block",
            "manifest_block",
            "measured_at_commit",
            "measured_date",
            "note",
            "produced_by",
            "rule",
            "schema_version",
        ),
        required_nested={},
        runs=(
            Producer(
                SELF,
                (),
                "This gate itself, for the same reason it is listed on the "
                "artifacts above: it writes a sandbox and a perturbed copy, "
                "so it cannot be declared read-only.",
            ),
            Producer(
                "scripts/tests/test_nursery_components.py",
                (),
                "The tool's own controls. They build throwaway trees under "
                "AXEYUM_NURSERY_COMPONENTS_ROOT and write censuses INSIDE "
                "them -- including the --record scenarios, which are the only "
                "tests that exercise this artifact's writer. That the real "
                "one is untouched is exactly what this arm measures.",
            ),
        ),
        reads=(),
    ),
)

# A call is a write if it is any of these. Used only for the READS arm, where
# the question is decidable: a module containing none of them cannot write
# anything, whatever its dataflow looks like.
WRITE_METHODS = {
    "write_text",
    "write_bytes",
    "writelines",
    "write",
    "unlink",
    "mkdir",
    "touch",
    "rmdir",
}
WRITE_DOTTED = {
    "json.dump",
    "shutil.copy",
    "shutil.copy2",
    "shutil.copyfile",
    "shutil.copytree",
    "shutil.move",
    "shutil.rmtree",
    "os.replace",
    "os.rename",
    "os.remove",
    "os.unlink",
    "os.makedirs",
    "os.mkdir",
}


def dotted(node: ast.AST) -> str:
    """`json.dump` for an Attribute chain of plain Names, else ''."""
    parts: list[str] = []
    while isinstance(node, ast.Attribute):
        parts.append(node.attr)
        node = node.value
    if not isinstance(node, ast.Name):
        return ""
    parts.append(node.id)
    return ".".join(reversed(parts))


def write_calls(source: str) -> list[str]:
    """Every write-shaped call in a Python module, as `name:line` strings."""
    found: list[str] = []
    for node in ast.walk(ast.parse(source)):
        if not isinstance(node, ast.Call):
            continue
        func = node.func
        if isinstance(func, ast.Attribute) and func.attr in WRITE_METHODS:
            found.append(f"{func.attr}:{node.lineno}")
            continue
        name = dotted(func)
        if name in WRITE_DOTTED:
            found.append(f"{name}:{node.lineno}")
            continue
        if isinstance(func, ast.Name) and func.id == "open":
            mode = node.args[1] if len(node.args) > 1 else None
            for kw in node.keywords:
                if kw.arg == "mode":
                    mode = kw.value
            if isinstance(mode, ast.Constant) and isinstance(mode.value, str) \
                    and any(c in mode.value for c in "wax+"):
                found.append(f"open({mode.value!r}):{node.lineno}")
    return found


def referencing_scripts(basename: str) -> set[str]:
    """Every script under scripts/ whose TEXT names this artifact.

    Derived from the tree rather than from a list, so a script that starts
    touching a guarded artifact is discovered instead of being invisible --
    the "every X must derive its X from the authority" rule.

    Deliberately a SUBSTRING test, unlike COVER's `artifact_names_in`, and it
    should stay one. This feeds the KNOWN arm, which DEMANDS that anything
    naming a guarded artifact be classified, so over-matching costs a
    classification line and under-matching leaves a real writer unmeasured --
    the errors are not symmetric here. COVER's population is the opposite
    shape (a name it over-matches becomes a candidate row for a file nobody
    writes), which is why only that one was tightened.
    """
    hits: set[str] = set()
    for path in sorted((ROOT / "scripts").rglob("*")):
        if not path.is_file() or "__pycache__" in path.parts:
            continue
        if path.suffix not in (".py", ".sh"):
            continue
        try:
            text = path.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            continue
        if basename in text:
            hits.add(str(path.relative_to(ROOT)))
    return hits


def build_sandbox(work: pathlib.Path) -> pathlib.Path:
    root = work / "tree"
    root.mkdir()
    for name in SANDBOX_TREES:
        shutil.copytree(ROOT / name, root / name, symlinks=True)
    return root


def run_in(root: pathlib.Path, script: str, argv: tuple[str, ...],
           timeout: int = 900) -> subprocess.CompletedProcess[str]:
    target = root / script
    cmd = (["bash", str(target)] if target.suffix == ".sh"
           else [sys.executable, str(target)]) + list(argv)
    env = dict(os.environ)
    env[NEST] = "1"
    return subprocess.run(cmd, cwd=root, capture_output=True, text=True,
                          timeout=timeout, check=False, env=env)


def key_delta(before: str, after: str) -> str:
    """What a producer did to the artifact, in the terms that matter."""
    try:
        was, now = json.loads(before), json.loads(after)
    except json.JSONDecodeError:
        return "the file is no longer valid JSON"
    if not isinstance(was, dict) or not isinstance(now, dict):
        return "top level is not an object"
    lost = sorted(set(was) - set(now))
    gained = sorted(set(now) - set(was))
    changed = sorted(k for k in set(was) & set(now) if was[k] != now[k])
    bits = []
    if lost:
        bits.append(f"DELETED {lost}")
    if gained:
        bits.append(f"added {gained}")
    if changed:
        bits.append(f"changed {changed}")
    return "; ".join(bits) or "bytes differ with no key-level change"


SECOND_WRITER = '''#!/usr/bin/env python3
"""Planted by check-generated-artifact-ownership.py --- CTRL arm.

A synthetic second writer reproducing the ADR-0652 defect exactly: rewrite
the guarded artifact minus a key only its owner derives, and exit 0. The
RUNS arm must reject it. If it does not, RUNS is inert.

The dropped key is the artifact's OWN, taken from `required_keys`, not the
vocabulary's `bridge_provenance` hardcoded here. A control that names a key
the artifact does not carry writes the file back BYTE-IDENTICAL and is
accepted -- so the arm meant to prove RUNS can fail would itself have been
the thing that cannot. Found by this gate's own control suite, on the first
run, against a second guarded artifact that was purely hypothetical.
"""
import json, pathlib, sys
p = pathlib.Path(__file__).resolve().parents[1] / "%s"
d = json.loads(p.read_text())
d.pop("%s", None)
p.write_text(json.dumps(d, indent=2, sort_keys=True, ensure_ascii=False) + "\\n")
print("planted second writer: dropped %s")
sys.exit(0)
'''


def compare_after_run(root: pathlib.Path, artifact: Artifact,
                      producer: Producer) -> str | None:
    """Run a producer in the sandbox; return a failure reason or None."""
    target = root / artifact.path
    before = target.read_text()
    result = run_in(root, producer.path, producer.argv)
    if not target.is_file():
        return (f"{producer.path} {' '.join(producer.argv)} DELETED "
                f"{artifact.path} (exit {result.returncode})")
    after = target.read_text()
    if after != before:
        # Restore, so one finding does not cascade into every later arm.
        target.write_text(before)
        return (f"{producer.path} {' '.join(producer.argv)} rewrote "
                f"{artifact.path} at exit {result.returncode}: "
                f"{key_delta(before, after)}")
    return None


def keys_arm(doc: Any, artifact: Artifact) -> list[str]:
    """KEYS: the committed artifact carries every key its owner derives.

    The arm that would have gone red the moment `bridge_provenance` was
    dropped, whoever dropped it and by whatever route -- a second writer, a
    hand edit, a merge that took the wrong side.
    """
    owner = artifact.owner
    if not isinstance(doc, dict):
        return [f"KEYS {artifact.path}: top level is not an object"]
    fails = []
    missing = [k for k in artifact.required_keys if k not in doc]
    if missing:
        fails.append(
            f"KEYS {artifact.path}: missing {missing}. Only {owner.path} "
            f"derives these -- regenerate with `{owner.path} "
            f"{' '.join(owner.argv)}`, and find out what wrote the file "
            f"without them.")
    for parent, keys in artifact.required_nested.items():
        block = doc.get(parent)
        if not isinstance(block, dict):
            fails.append(f"KEYS {artifact.path}: `{parent}` is not an object")
            continue
        gone = [k for k in keys if k not in block]
        if gone:
            fails.append(
                f"KEYS {artifact.path}: `{parent}` missing {gone}. These are "
                f"ADR-0631's published tier counts.")
    return fails


def classified_paths(artifact: Artifact) -> set[str]:
    return ({artifact.owner.path}
            | {p.path for p in artifact.runs}
            | {r.path for r in artifact.reads}
            | {i.path for i in artifact.invokes})


def known_arm(artifact: Artifact, found: set[str]) -> list[str]:
    """KNOWN: the classification covers exactly the scripts that name it.

    `found` is passed in rather than looked up so this is testable without a
    tree -- and so the DISCOVERY it is checked against is the tree's, never a
    list somebody remembered to update.
    """
    classified = classified_paths(artifact)
    fails = []
    for path in sorted(found - classified):
        fails.append(
            f"KNOWN {artifact.path}: {path} names this artifact and is not "
            f"classified. Classify it in GUARDED as a `runs` producer (it "
            f"will be executed in a sandbox and must leave the file "
            f"byte-identical); or, only if it contains no write call at all, "
            f"as `reads`; or, if it only STAGES the artifact and regenerates "
            f"it by calling {artifact.owner.path}, as `invokes` (checked by "
            f"inspection, never run).")
    for path in sorted(classified - found):
        fails.append(
            f"KNOWN {artifact.path}: {path} is classified here but no longer "
            f"names the artifact. Drop the stale entry.")
    return fails


def reads_arm(artifact: Artifact, source_of: Any) -> list[str]:
    """READS: a script declared read-only really contains no write call."""
    fails = []
    for reader in artifact.reads:
        calls = write_calls(source_of(reader.path))
        if calls:
            fails.append(
                f"READS {reader.path} is declared read-only for "
                f"{artifact.path} but contains write call(s) {calls}. A "
                f"script that can write cannot be declared read-only by "
                f"inspection -- reclassify it as `runs`.")
    return fails


# --------------------------------------------------------------------------
# INVOKES -- the ORCHESTRATOR, which neither existing category describes.
#
# `scripts/lane-merge-land.sh` names the census artifact in its `GENERATED`
# array so that a merge conflict on it is cleared (with `--theirs`) and the
# regenerated file staged, and then rebuilds it by running
# `scripts/frontier-shape-census.py` -- the OWNER. Both existing
# classifications are dishonest for it, and the gate offered only those two in
# its own remedy line:
#
#   `runs`   would EXECUTE a merge driver inside the ownership sandbox. It
#            takes a branch argument, merges, resolves and commits; running it
#            there measures nothing about ownership.
#   `reads`  is false. The script writes -- redirections, and staging -- and
#            READS' decision procedure is an AST scan that does not apply to
#            bash at all.
#
# PLAN.md and the ADR index are handled by the same script in the same way;
# that never surfaced only because they are not guarded artifacts.
#
# So this is a third decision procedure, and like READS it is BY INSPECTION
# rather than by execution, because for this shape inspection is decidable:
#
#   (a) every line that reaches the artifact's name is a git STAGING line --
#       add, checkout, restore, rm, stage, update-index. A staging command
#       moves a file between the index, the working tree and a merge stage; it
#       cannot put content into the artifact that the owner did not produce.
#       A redirection into it, a copy or move onto it, a Python
#       `open(path, "w")` -- each reaches the name on a line that is not a
#       staging line, and fails.
#   (b) the owner's path appears in the script, which is what makes it an
#       INVOKER rather than merely a stager. A script that clears the conflict
#       and never regenerates leaves a stale artifact staged.
#
# "Reaches the name" is not "contains the name": the real script binds the
# path into an array and stages the array's elements in a loop, so an arm that
# judged only the naming LINE would accept an array later used to copy over
# the file -- a guard that cannot fail. So bindings are followed: a line that
# BINDS a name reaching the artifact (`VAR=`, `for VAR in`) contributes the new
# name instead of being judged, and the lines using that name are judged.
# --------------------------------------------------------------------------

# Git subcommands that move a file between the index, the working tree and a
# merge stage. Deliberately a small closed list: `git show` and `git cat-file`
# are NOT on it, because `git show :2:path` redirected into the path writes
# content -- which is what `redirects_into` exists to catch besides.
STAGING = re.compile(
    r"\bgit\b[^\n]*?\b(?:add|checkout|restore|rm|stage|update-index)\b")

# `VAR=`, `export VAR=`, `local VAR=`, and Python's `VAR = ...`. The trailing
# `[^=]` keeps `==` from reading as a binding.
NAME_BINDING = re.compile(
    r"^\s*(?:export\s+|local\s+|declare\s+(?:-\w+\s+)*)?"
    r"([A-Za-z_][A-Za-z0-9_]*)\s*=[^=]")
FOR_BINDING = re.compile(r"^\s*for\s+([A-Za-z_][A-Za-z0-9_]*)\s+in\b")

# A binding line is exempt from the staging shape because binding a name puts
# no bytes anywhere. `p = open("artifacts/x.json", "w")` binds a name too, and
# exempting it would make the follow-through a laundry: the write reaches the
# artifact on a line the arm declined to judge. So a binding that also carries
# a write construct is judged like any other use.
WRITE_SHAPE = re.compile(
    r"\bopen\s*\(|\.write(?:_text|_bytes)?\s*\(|\bshutil\.\w+\s*\(|"
    r"\b(?:cp|mv|tee|dd|install|truncate)\b")


def literal_pattern(basename: str) -> re.Pattern[str]:
    """The artifact named directly, with or without its directory prefix."""
    return re.compile(r"[A-Za-z0-9_./-]*" + re.escape(basename))


def var_pattern(name: str) -> re.Pattern[str]:
    """A bound name, expanded (`$g`, `${g[@]}`) or bare (Python's `P`)."""
    return re.compile(r"(?<![A-Za-z0-9_])\$?\{?" + re.escape(name) + r"\b")


def invoker_uses(text: str, basename: str,
                 max_depth: int = 4) -> dict[int, tuple[str, re.Pattern[str]]]:
    """`{lineno: (line, the pattern that matched)}` for every USE of the name.

    A binding line contributes a name and is not itself judged; every other
    line reaching the artifact is a use and must answer to the staging shape.
    Comment lines execute nothing and are skipped. `max_depth` bounds the
    follow-through, which is otherwise a fixpoint over the whole script.
    """
    lines = list(enumerate(text.splitlines(), start=1))
    frontier = [literal_pattern(basename)]
    bound: set[str] = set()
    uses: dict[int, tuple[str, re.Pattern[str]]] = {}
    for _ in range(max_depth):
        nxt: list[re.Pattern[str]] = []
        for pat in frontier:
            for lineno, line in lines:
                if line.lstrip().startswith("#") or not pat.search(line):
                    continue
                binding = FOR_BINDING.match(line) or NAME_BINDING.match(line)
                if binding and not WRITE_SHAPE.search(line):
                    name = binding.group(1)
                    if name not in bound:
                        bound.add(name)
                        nxt.append(var_pattern(name))
                    continue
                uses[lineno] = (line, pat)
        if not nxt:
            break
        frontier = nxt
    return uses


def redirects_into(line: str, pat: re.Pattern[str]) -> bool:
    """Is the artifact reference on this line the TARGET of a redirection?

    The one shape that carries a staging word and still writes the file:
    `git show :2:path > path`. Without this, (a) is satisfied by the mere
    presence of the word `git` somewhere on the line.
    """
    for match in pat.finditer(line):
        before = line[:match.start()].rstrip("\"'").rstrip()
        if before.endswith(">"):
            return True
    return False


def invokes_arm(artifact: Artifact, source_of: Any) -> list[str]:
    """INVOKES: an orchestrator only stages the artifact, and calls the owner.

    Verified by reading the script, never by running it -- running a merge
    driver inside the ownership sandbox is not a measurement of anything.
    """
    basename = pathlib.PurePath(artifact.path).name
    fails = []
    for inv in artifact.invokes:
        text = source_of(inv.path)
        uses = invoker_uses(text, basename)
        staged = 0
        for lineno in sorted(uses):
            line, pat = uses[lineno]
            if not STAGING.search(line):
                fails.append(
                    f"INVOKES {inv.path}:{lineno} is classified as an invoker "
                    f"for {artifact.path} but reaches it outside a git "
                    f"staging command: {line.strip()!r}. An invoker may name "
                    f"the artifact only to stage it, and must produce its "
                    f"content by calling {artifact.owner.path}. Writing it by "
                    f"any other route makes it a second writer -- reclassify "
                    f"it as `runs`.")
                continue
            if redirects_into(line, pat):
                fails.append(
                    f"INVOKES {inv.path}:{lineno} REDIRECTS into "
                    f"{artifact.path}: {line.strip()!r}. A staging word "
                    f"elsewhere on the line does not make this a staging "
                    f"operation; it puts content into the artifact that "
                    f"{artifact.owner.path} did not produce.")
                continue
            staged += 1
        if artifact.owner.path not in text:
            fails.append(
                f"INVOKES {inv.path} is classified as an invoker for "
                f"{artifact.path} but never names {artifact.owner.path}. An "
                f"invoker is what it is because it REGENERATES the artifact "
                f"by calling the owner; one that only clears the conflict "
                f"leaves a stale artifact staged.")
        if not staged:
            fails.append(
                f"INVOKES {inv.path} names {artifact.path} but no line "
                f"reaching it is a staging command, so the classification "
                f"asserts a property nothing here can fail. Either it is a "
                f"`reads` or a `runs` script, or the reference is a mention "
                f"this arm cannot see.")
    return fails


def runs_arm(root: pathlib.Path, artifact: Artifact,
             verbose: bool = False) -> tuple[list[str], int]:
    """RUNS: every non-owner producer leaves the artifact byte-identical."""
    fails: list[str] = []
    ran = 0
    for producer in artifact.runs:
        if NESTED and producer.path == SELF:
            if verbose:
                print(f"RUNS skip {SELF}: nested invocation, would recurse "
                      f"without bound")
            continue
        reason = compare_after_run(root, artifact, producer)
        ran += 1
        if reason:
            fails.append(f"RUNS {reason}")
        elif verbose:
            print(f"RUNS ok   {producer.path} {' '.join(producer.argv)}: "
                  f"{pathlib.PurePath(artifact.path).name} unchanged")
    return fails, ran


def ctrl_arm(root: pathlib.Path, artifact: Artifact,
             verbose: bool = False) -> list[str]:
    """CTRL: a planted second writer must be REJECTED by the RUNS machinery.

    On every invocation, never opt-in. Without it, `RUNS ok` on four
    producers is consistent with a comparison that can no longer fail --
    which is the exact defect this repository says is worse than no check.
    """
    planted = pathlib.PurePath("scripts") / "_ownership_control.py"
    # The LAST required key, so the planted writer drops something this
    # artifact really carries. See SECOND_WRITER's docstring for why a
    # hardcoded key name makes this control vacuous.
    victim = artifact.required_keys[-1]
    (root / planted).write_text(
        SECOND_WRITER % (artifact.path, victim, victim))
    verdict = compare_after_run(
        root, artifact, Producer(str(planted), (), "synthetic"))
    (root / planted).unlink()
    if verdict is None:
        return [f"CTRL {artifact.path}: the RUNS arm ACCEPTED a planted "
                f"second writer that deletes `{victim}`. The arm is inert; "
                f"nothing it reported above is evidence."]
    if verbose:
        print(f"CTRL ok   planted second writer rejected: "
              f"{verdict.split(': ', 1)[-1]}")
    return []


def owner_arm(root: pathlib.Path, artifact: Artifact,
              verbose: bool = False) -> list[str]:
    """OWNER: the owner restores a PERTURBED copy byte-for-byte.

    The positive control for RUNS. `nothing changed the file` is also what a
    sandbox no script can reach reports, and the two are indistinguishable
    from the RUNS output alone.
    """
    owner = artifact.owner
    target = root / artifact.path
    good = target.read_text()
    hurt = json.loads(good)
    hurt.pop(artifact.required_keys[-1], None)
    for key in ("row_digest", "bridge_provenance"):
        hurt.pop(key, None)
    target.write_text(
        json.dumps(hurt, indent=2, sort_keys=True, ensure_ascii=False) + "\n")
    result = run_in(root, owner.path, owner.argv)
    restored = target.read_text() if target.is_file() else ""
    if restored != good:
        target.write_text(good)
        return [f"OWNER {owner.path} {' '.join(owner.argv)} did not restore "
                f"{artifact.path} from a perturbed copy (exit "
                f"{result.returncode}). Either it is not the owner or the "
                f"sandbox is not reachable, and in both cases the RUNS arm "
                f"above proves nothing."]
    if verbose:
        print(f"OWNER ok  {owner.path} restored "
              f"{pathlib.PurePath(artifact.path).name} byte-for-byte from a "
              f"perturbed copy")
    return []


# --------------------------------------------------------------------------
# COVER -- the DENOMINATOR, which `GUARDED` alone cannot supply.
#
# The 2026-08-30 session audit's fourth finding, and it did not say this gate is
# wrong. Every one of its eleven registered mutants dies, an owner naming a
# nonexistent artifact is caught, and DISCOVERY (`referencing_scripts`) already
# derives the writers of a guarded artifact FROM THE TREE rather than from a
# list. What it could not answer is one level up: `GUARDED` is a hand-written
# literal of length one, reported as `artifacts=1` against 82 tracked
# `scripts/gen-*.py` and 3,889 tracked `artifacts/**/*.json`, so an artifact
# with a second writer and NO entry here is structurally invisible.
#
# That is the "any check named every X must derive its X from the authority"
# rule applied to the top of this gate rather than only inside it.
#
# What this arm does NOT do, stated plainly rather than implied. It does not
# guard 33 artifacts. The RUNS arm's guarantee comes from EXECUTING each
# candidate writer in a sandbox and comparing bytes, and that is the only
# reliable writer test here -- a static "contains a write call" scan cannot tell
# which file a script writes, and `nursery-v1.json` alone is named by 45
# scripts. Expanding the guarded set is real work per artifact and it is not
# what this change claims to have done.
#
# What it DOES is make the denominator visible and unable to grow in silence: a
# tracked artifact named by two or more `scripts/gen-*.py` producers must appear
# in `scripts/check-generated-artifact-ownership.candidates`, and a NEW one
# fails the gate until it is recorded. The summary then reads
# `guarded=1|multi_writer_candidates=33` instead of `artifacts=1`, which is the
# honest shape of the claim.
#
# WHAT WOULD MAKE THE ONE-OWNER GUARANTEE REAL, since the audit asked: a second
# artifact in `GUARDED` whose producers actually run in the sandbox. The CTRL
# arm plants a second writer and requires the RUNS machinery to reject it, and
# with one registry entry that is a test of one comparison against one file --
# the registering lane itself found its planted writer was vacuous against any
# other artifact. Two entries would exercise it twice over different producers,
# which is the difference between "this comparison works" and "this comparison
# works for artifacts in general". It needs a candidate whose producers are
# sandbox-runnable without the kernel, and that selection is the work.
CANDIDATES = ROOT / "scripts" / "check-generated-artifact-ownership.candidates"

CANDIDATES_HEADER = """\
# Tracked artifacts named by TWO OR MORE `scripts/gen-*.py` producers.
#
# Derived from the tree, never hand-listed: regenerate with
#   python3 scripts/check-generated-artifact-ownership.py --update-candidates
#
# A basename here is a one-owner question this gate has NOT answered. Being
# listed is not a guarantee; it is an acknowledgement, and the point is that the
# list cannot GROW without someone noticing. Guarding one of them means adding
# a `GUARDED` entry whose producers run in the sandbox (ADR-0652).
"""


_ARTIFACT_NAME = re.compile(r"(?<![A-Za-z0-9_.\-])([A-Za-z0-9_.\-]+\.json)(?![A-Za-z0-9_\-])")


def artifact_names_in(text: str) -> set[str]:
    """Every `*.json` path component `text` names, as whole components.

    Extracted from the TEXT once rather than by testing each of the tree's
    3,742 basenames against it: the pair-wise form is ~350,000 regex searches
    over ~94 producer sources and took the gate past a two-minute timeout,
    where this is one pass per producer.

    A bare `base in text` reads a basename as a substring, which is wrong for
    any basename that is a SUFFIX of another. Measured 2026-09-01: the only
    file in the tree literally called `schema.json` is
    `artifacts/declaration-spec/schema.json`, and the substring test attributed
    it to three producers -- but `gen-autogenesis-baseline.py` names
    `artifacts/ontology/fact.schema.json` and `gen-obstruction-dashboard.py`
    names `artifacts/ontology/obstruction-graph.schema.json`. Two different
    files, neither of them this one. So COVER demanded that a fiction be
    recorded as a known multi-writer candidate, which is worse than not asking:
    a ratchet whose population contains inventions trains people to record
    whatever it prints.

    Requiring a whole path component fixes exactly that and nothing else.
    Measured over 3,742 artifact basenames and 94 producers: the candidate set
    goes 35 -> 34, dropping `schema.json` alone, adding none, and removing none
    of the 32 already recorded -- so no genuine candidate is lost. It also
    narrows `obstruction-projection-v1.json` from 7 producers to 3, the other
    four naming `*-obstruction-projection-v1.json` variants.

    This does NOT narrow the arm from "names" to "writes", and must not. The
    module docstring's whole point is that the destroying write reached its
    path through a dict value, so a static write-receiver analysis misses it;
    over-approximating the writers is the design, and only the ARTIFACT
    identification is tightened here.

    The trailing guard excludes a continuing name (`.jsonl`, and a component
    that goes on with `-` or `_`) but deliberately allows a trailing `.`,
    because prose ends sentences with one.
    """
    return set(_ARTIFACT_NAME.findall(text))


def names_artifact(base: str, text: str) -> bool:
    """Convenience wrapper over `artifact_names_in` for a single basename."""
    return base in artifact_names_in(text)


def multi_writer_candidates() -> dict[str, list[str]]:
    """`{artifact basename: [gen-*.py naming it]}` for basenames with >= 2.

    `gen-*.py` is the producer naming convention in this tree and is the
    population the audit measured (82 files). A basename rather than a full
    path because that is what `referencing_scripts` matches on, and because a
    script names an artifact by whichever spelling it happens to use --
    matched as a whole path component, see `names_artifact`.
    """
    # The FILESYSTEM, not `git ls-files`. The two agree here (3,889 either
    # way, measured 2026-08-30), and the mutation harness copies the tree
    # WITHOUT `.git`, so a git-backed enumeration makes this whole suite
    # unmeasurable -- "BASELINE IS NOT GREEN", which is not a result.
    basenames = {p.name for p in (ROOT / "artifacts").rglob("*.json")}

    # One `artifact_names_in` pass per producer, then set membership. Testing
    # each of 3,742 basenames against each of 94 sources instead is ~350,000
    # regex searches and takes 112 s, which put this gate past a two-minute
    # timeout; this form is 0.05 s and computes the same answer.
    producers: list[tuple[str, set[str]]] = []
    for path in sorted((ROOT / "scripts").glob("gen-*.py")):
        try:
            text = path.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            continue
        producers.append((path.name, artifact_names_in(text)))

    out: dict[str, list[str]] = {}
    for base in sorted(basenames):
        naming = sorted(name for name, named in producers if base in named)
        if len(naming) >= 2:
            out[base] = naming
    return out


def read_candidates(path: pathlib.Path) -> set[str] | None:
    if not path.is_file():
        return None
    return {
        line.strip()
        for line in path.read_text().splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    }


def cover_arm(recorded: set[str] | None, current: dict[str, list[str]],
              guarded: set[str]) -> list[str]:
    """COVER: every multi-writer artifact is guarded or acknowledged."""
    if recorded is None:
        return ["COVER: no candidate list. Without it `GUARDED` is a literal "
                "with no denominator and a NEW multi-writer artifact is "
                "invisible. Run --update-candidates."]
    fails = []
    for base in sorted(set(current) - recorded - guarded):
        fails.append(
            f"COVER {base}: named by {len(current[base])} `gen-*.py` producers "
            f"({', '.join(current[base])}) and is neither GUARDED nor recorded "
            f"as a known candidate. Two producers writing one artifact is the "
            f"defect ADR-0652 exists for. Guard it, or record it deliberately "
            f"with --update-candidates so the growth is visible.")
    for base in sorted(recorded - set(current) - guarded):
        fails.append(
            f"COVER {base}: recorded as a multi-writer candidate and no longer "
            f"has two `gen-*.py` producers. Good news; drop the stale entry "
            f"with --update-candidates.")
    return fails


def check(verbose: bool, candidates_path: pathlib.Path) -> int:
    fails: list[str] = []
    producers_run = 0

    current = multi_writer_candidates()
    guarded_names = {pathlib.PurePath(a.path).name for a in GUARDED}
    fails += cover_arm(read_candidates(candidates_path), current, guarded_names)
    if verbose:
        print(f"COVER ok  {len(current)} multi-writer candidate(s), "
              f"{len(guarded_names)} guarded")

    with tempfile.TemporaryDirectory(prefix="artifact-ownership-") as tmp:
        root = build_sandbox(pathlib.Path(tmp))

        for artifact in GUARDED:
            committed = ROOT / artifact.path
            basename = pathlib.PurePath(artifact.path).name
            if not committed.is_file():
                fails.append(f"KEYS {artifact.path}: absent from the tree")
                continue

            arm = keys_arm(json.loads(committed.read_text()), artifact)
            fails += arm
            if verbose and not arm:
                print(f"KEYS ok   {artifact.path}: "
                      f"{len(artifact.required_keys)} top-level key(s)")

            found = referencing_scripts(basename)
            arm = known_arm(artifact, found)
            fails += arm
            if verbose and not arm:
                print(f"KNOWN ok  {artifact.path}: {len(found)} referencing "
                      f"script(s), all classified")

            arm = reads_arm(artifact, lambda p: (ROOT / p).read_text())
            fails += arm
            if verbose and not arm:
                for reader in artifact.reads:
                    print(f"READS ok  {reader.path}: no write call")

            arm = invokes_arm(artifact, lambda p: (ROOT / p).read_text())
            fails += arm
            if verbose and not arm:
                for inv in artifact.invokes:
                    print(f"INVOKES ok {inv.path}: stages only, and names "
                          f"{artifact.owner.path}")

            arm, ran = runs_arm(root, artifact, verbose)
            fails += arm
            producers_run += ran

            fails += ctrl_arm(root, artifact, verbose)

            fails += owner_arm(root, artifact, verbose)
            producers_run += 1

    for line in fails:
        print(f"FAIL {line}", file=sys.stderr)
    # `guarded` is named rather than `artifacts` because `artifacts=1` read as
    # a coverage claim, and it never was one.
    print(f"GENERATED_ARTIFACT_OWNERSHIP|guarded={len(GUARDED)}"
          f"|multi_writer_candidates={len(current)}"
          f"|producers_run={producers_run}|fails={len(fails)}"
          f"|{'PASS' if not fails else 'FAIL'}")
    return 1 if fails else 0


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("-v", "--verbose", action="store_true",
                    help="print a line per arm, including the ones that pass")
    ap.add_argument("--candidates", default=str(CANDIDATES),
                    help="multi-writer candidate list (the controls point this "
                         "elsewhere)")
    ap.add_argument("--update-candidates", action="store_true",
                    help="rewrite the candidate list from the tree, then exit")
    args = ap.parse_args(argv)
    path = pathlib.Path(args.candidates)
    if args.update_candidates:
        current = multi_writer_candidates()
        guarded_names = {pathlib.PurePath(a.path).name for a in GUARDED}
        rows = sorted(set(current) - guarded_names)
        path.write_text(CANDIDATES_HEADER + "".join(r + "\n" for r in rows))
        print(f"recorded {len(rows)} multi-writer candidate(s) in {path} "
              f"({len(guarded_names)} guarded and therefore not listed)")
        return 0
    return check(args.verbose, path)


if __name__ == "__main__":
    sys.exit(main())

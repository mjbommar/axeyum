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
SANDBOX_TREES = ("artifacts", "scripts")


class Producer(NamedTuple):
    """A script that is RUN in the sandbox, with the argv that makes it write."""

    path: str
    argv: tuple[str, ...]
    note: str


class ReadOnly(NamedTuple):
    """A script declared read-only. Verified: it must contain no write call."""

    path: str
    note: str


class Artifact(NamedTuple):
    path: str
    owner: Producer
    required_keys: tuple[str, ...]
    required_nested: dict[str, tuple[str, ...]]
    runs: tuple[Producer, ...]
    reads: tuple[ReadOnly, ...]


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
            | {r.path for r in artifact.reads})


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
            f"byte-identical) or, only if it contains no write call at all, "
            f"as `reads`.")
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


def check(verbose: bool) -> int:
    fails: list[str] = []
    producers_run = 0

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

            arm, ran = runs_arm(root, artifact, verbose)
            fails += arm
            producers_run += ran

            fails += ctrl_arm(root, artifact, verbose)

            fails += owner_arm(root, artifact, verbose)
            producers_run += 1

    for line in fails:
        print(f"FAIL {line}", file=sys.stderr)
    print(f"GENERATED_ARTIFACT_OWNERSHIP|artifacts={len(GUARDED)}"
          f"|producers_run={producers_run}|fails={len(fails)}"
          f"|{'PASS' if not fails else 'FAIL'}")
    return 1 if fails else 0


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("-v", "--verbose", action="store_true",
                    help="print a line per arm, including the ones that pass")
    args = ap.parse_args(argv)
    return check(args.verbose)


if __name__ == "__main__":
    sys.exit(main())

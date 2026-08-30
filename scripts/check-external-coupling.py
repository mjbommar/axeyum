#!/usr/bin/env python3
"""No artifact in this repository may depend on a repository it does not own.

WHY THIS EXISTS. The sibling `../math-education` is REFERENCE ONLY: something to
read for calibration, never something this project depends on, integrates with,
or points at in its data. That constraint was stated and not gated, and by
2026-08-24 it had been violated in five places at once --

  * `knowledge-overlay-v1.json`: a source of kind `external-repository` with
    `path_hint: ../math-education`, a namespace with `resolution:
    external-pinned`, and 24 of 33 links with an endpoint in it, each carrying
    that repository's commit as `source_revision`;
  * `family-concept-crosswalk-v1.json`: `path_hint:
    ../math-education/graph/concepts` plus the same pinned commit, which its
    validator REQUIRED the file to match;
  * `tactic-catalog.schema.json`: `uses_technique` is required on every tactic
    and required `source: {const: "math-education"}` with a 40-hex `revision`,
    so no tactic could be declared without naming that checkout;
  * all 104 claims: `provenance.graph_pin`, the same SHA on every one, with
    `concept_refs[].resolved` asserting a resolution against it;
  * `check-reachability-census.py`: a default of
    `~/projects/personal/math-education/graph` -- an absolute path into one
    machine's home directory, in a tracked file.

Not one existing gate could see any of it. This is that gate. ADR-0553.

WHAT IT REFUSES, and each rule names the mechanism rather than the repository,
so a DIFFERENT sibling gets caught too:

  R1  the external-declaration vocabulary: `external-repository`,
      `external-artifact`, `external-pinned` as a value anywhere, and in any
      schema `enum` or `const` -- a schema that offers the word is an
      invitation, and the overlay schema still offered all three after its data
      was clean.
  R2  a path that escapes the checkout: any `..` segment in any string value.
  R3  a revision pin under an unregistered key. Every 40-hex value must sit
      under a key in REVISION_KEYS, which says WHICH repository that key pins.
      A new key -- `graph_pin` was one -- fails closed and has to be argued for.
  R4  source code that constructs a path out of the checkout: `ROOT.parent`,
      `expanduser("~/...")`, and a `..` used as a PATH COMPONENT --
      `Path("..")`, `/ ".."`. That last needle is not hypothetical: the deleted
      `python/axeyum/knowledge/math_education.py` opened with
      `DEFAULT_PATH_HINT = Path("..") / "math-education"`, and 777 lines of live
      integration hung off it.

      Scanned: `scripts/*.py`, `python/**/*.py`, `tools/**/*.py`. The first
      draft of this gate scanned `scripts/` ONLY, which left the largest single
      piece of coupling in the repository invisible to it -- the gate would have
      reported `findings=0` over a module whose entire purpose was reading a
      sibling checkout. A reviewer caught that, and it is the reason R4 has a
      list of roots rather than one.

WHAT IT DELIBERATELY DOES NOT COVER, measured rather than assumed:

  * ABSOLUTE PATHS. There are 1,174 in `artifacts/**`, and they are not this
    problem: `/nas3/data/axeyum/autogenesis/reference-packs/...`,
    `/home/mjbommar/lean-import-scale/mathlib4`,
    `/home/mjbommar/.elan/toolchains/...`. Each records WHERE A MEASUREMENT
    PHYSICALLY RAN, which is provenance, not a dependency declaration -- the
    artifact does not stop being checkable if the path is gone. Forbidding them
    is a real and separate policy question with a 1,174-row blast radius, and
    conflating it with this one would have made the gate impossible to land.
    The single `~`-rooted value (`lean_binary`) is the same category and is
    excluded for the same reason.
  * PINS OF SANCTIONED FOREIGN REPOSITORIES. Mathlib, the Lean toolchain and
    lean4export are pinned ON PURPOSE -- the `imported-kernel-lean` proof route
    exists precisely to admit their content under our own kernel. R3 does not
    forbid a foreign pin; it forbids an UNDECLARED one.
  * PROSE. A document may name, discuss and cite the sibling; ADR-0546 does,
    and that is the behaviour the owner asked for. A citation names a source; a
    dependency tells you where to find it and which version to use. Only the
    second is a coupling, and R1-R4 are shaped to catch exactly that half.

Usage:
    python3 scripts/check-external-coupling.py
    python3 scripts/check-external-coupling.py --self-test   # prove it can fire
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
ARTIFACTS = ROOT / "artifacts"
# R4's roots. `scripts/tests/` is filtered out inside `scan_source`.
SOURCE_ROOTS = (
    (ROOT / "scripts", "*.py"),
    (ROOT / "python", "**/*.py"),
    (ROOT / "tools", "**/*.py"),
)

HEX40 = re.compile(r"^[0-9a-f]{40}$")
DOTDOT = re.compile(r"(?:^|/)\.\.(?:/|$)")

# R1. Vocabulary that declares a dependency on something outside this checkout.
EXTERNAL_VOCABULARY = {
    "external-repository",
    "external-artifact",
    "external-pinned",
}

# R3. Every key under which a 40-hex revision may appear, and the repository it
# pins. Derived by reading all 36 keys present on 2026-08-24, not guessed.
#
# `git cat-file -e` is NOT used to verify these and must not be: measured the
# same day, `detached_transition_commit`, `reconstructed_replay_commit`,
# `pre_a_state_commit` and `reconstructed_prestate_commit` all report "not a
# commit" here while being perfectly ordinary commits of THIS repository, made
# in detached scratch worktrees and never pushed. A verifier that calls those
# foreign would be wrong in the direction that matters.
THIS_REPOSITORY = "axeyum (this repository)"
REVISION_KEYS: dict[str, str] = {
    # --- this repository -------------------------------------------------
    "acc_package_commit": THIS_REPOSITORY,
    "audit_commit": THIS_REPOSITORY,
    "axeyum_commit": THIS_REPOSITORY,
    "bool_order_commit": THIS_REPOSITORY,
    "commit": THIS_REPOSITORY,
    "detached_transition_commit": THIS_REPOSITORY,
    "detached_transition_parent": THIS_REPOSITORY,
    "driver_commit": THIS_REPOSITORY,
    "evidence_commit": THIS_REPOSITORY,
    "execution_commit": THIS_REPOSITORY,
    "fact_commit": THIS_REPOSITORY,
    "fact_transition_commit": THIS_REPOSITORY,
    "git_commit": THIS_REPOSITORY,
    "head": THIS_REPOSITORY,
    # `run.head_sha` in `artifacts/runtime/ci-latest-v1.json`, the GitHub
    # Actions runtime receipt. The artifact names its own subject one key up
    # (`"repository": "mjbommar/axeyum"`), and the value was checked to be a
    # real commit here and an ancestor of HEAD -- `08b65942f`, "docs(plan):
    # record imported ModEq bridge boundary" -- so this is our own CI pinning
    # our own tested commit, not a foreign pin.
    "head_sha": THIS_REPOSITORY,
    "historical_commit": THIS_REPOSITORY,
    "historical_prestate_commit": THIS_REPOSITORY,
    "implementation_commit": THIS_REPOSITORY,
    "importer_commit": THIS_REPOSITORY,
    "ledger_snapshot_commit": THIS_REPOSITORY,
    "main_transition_commit": THIS_REPOSITORY,
    "nat_mod_lt_commit": THIS_REPOSITORY,
    "parent": THIS_REPOSITORY,
    "pre_a_state_commit": THIS_REPOSITORY,
    "reconstructed_prestate_commit": THIS_REPOSITORY,
    "reconstructed_replay_commit": THIS_REPOSITORY,
    "registration_commit": THIS_REPOSITORY,
    "required_gate_surface_commit": THIS_REPOSITORY,
    "required_head": THIS_REPOSITORY,
    "source_commit": THIS_REPOSITORY,
    "source_head": THIS_REPOSITORY,
    # `runtime_gate_status.tested_commit` in `artifacts/product-health-v1.json`:
    # the same value as `head_sha` above, carried from the CI receipt into the
    # dashboard that summarises it. Verified to be the identical sha, so it
    # names this repository for the same reason.
    "tested_commit": THIS_REPOSITORY,
    "tooling_commit": THIS_REPOSITORY,
    # --- foreign, and sanctioned. Each is an IMPORT this project decided to
    # depend on deliberately, with an ADR behind it; that is the difference
    # between a pin and a coupling.
    "mathlib_commit": "leanprover-community/mathlib4 (imported-kernel-lean route)",
    "lean_commit": "leanprover/lean4 toolchain",
    "lean_githash": "leanprover/lean4 toolchain",
    "lean4export_commit": "leanprover/lean4export",
    "exporter_commit": "leanprover/lean4export",
}

# R4. Path expressions in source that leave the checkout.
#
# Spelled in pieces on purpose. Written literally, this table matches ITSELF --
# the first run of this gate reported two findings, both in this file, both from
# these very lines. The alternative was to exempt this file from its own scan,
# which would leave the one script nobody is watching free to escape. So the
# needles are assembled and the file stays scanned.
_PARENT = "ROOT" + ".parent"
_HOME_D = "expanduser(" + '"~'
_HOME_S = "expanduser(" + "'~"
_PATH_D = "Path(" + '".."' + ")"
_PATH_S = "Path(" + "'..'" + ")"
_JOIN_D = "/ " + '".."'
_JOIN_S = "/ " + "'..'"
ESCAPE_EXPRESSIONS = (
    (_PARENT, "a path built from the checkout's PARENT directory"),
    (_HOME_D, "an absolute path into a home directory"),
    (_HOME_S, "an absolute path into a home directory"),
    (_PATH_D, "a `..` path component, which leaves the checkout"),
    (_PATH_S, "a `..` path component, which leaves the checkout"),
    (_JOIN_D, "a `..` joined onto a path, which leaves the checkout"),
    (_JOIN_S, "a `..` joined onto a path, which leaves the checkout"),
)

# NOT a needle: a bare `"../"` STRING. Measured 2026-08-24, `scripts/` alone has
# 13 of them and every one is a relative markdown link or an upstream Lean case
# id -- `f"../notes/{path.name}"`, `"../doc/examples/compiler"`. Nor
# `.parent.parent`, which is how a dozen scripts compute the repository root.
# Both would bury the real findings in noise, and a rule nobody can keep green
# is a rule that gets deleted.


def walk(node, key, on_string):
    """Visit every string leaf with the key it hangs under."""
    if isinstance(node, dict):
        for k, v in node.items():
            walk(v, k, on_string)
    elif isinstance(node, list):
        for v in node:
            walk(v, key, on_string)
    elif isinstance(node, str):
        on_string(key, node)


def scan_document(doc, where: str) -> tuple[list[str], int]:
    """`(findings, strings_examined)` for one parsed JSON document."""
    findings: list[str] = []
    seen = 0

    def on_string(key: str, value: str) -> None:
        nonlocal seen
        seen += 1
        if value in EXTERNAL_VOCABULARY:
            findings.append(
                f"{where}: `{key}` = {value!r} declares a dependency on something "
                "outside this checkout (ADR-0553 R1)"
            )
        if DOTDOT.search(value):
            findings.append(
                f"{where}: `{key}` = {value!r} contains a `..` segment, so it "
                "names a path outside this checkout (ADR-0553 R2)"
            )
        if HEX40.match(value) and key not in REVISION_KEYS:
            findings.append(
                f"{where}: a 40-hex revision under unregistered key `{key}`. "
                f"Every pin must name the repository it belongs to: add `{key}` "
                "to REVISION_KEYS in scripts/check-external-coupling.py saying "
                "which repository, and if that is not this one and not an "
                "already sanctioned import, ADR-0553 forbids it (R3)"
            )

    walk(doc, "<root>", on_string)
    return findings, seen


def scan_artifacts() -> tuple[list[str], int, int]:
    """`(findings, files, strings)` over every JSON artifact."""
    findings: list[str] = []
    files = 0
    strings = 0
    for path in sorted(ARTIFACTS.glob("**/*.json")):
        rel = path.relative_to(ROOT) if path.is_relative_to(ROOT) else path
        try:
            doc = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            findings.append(f"{rel}: cannot read JSON: {exc}")
            continue
        files += 1
        found, seen = scan_document(doc, str(rel))
        findings.extend(found)
        strings += seen
    return findings, files, strings


def scan_source() -> tuple[list[str], int]:
    """`(findings, files)` over every source root in SOURCE_ROOTS.

    Test directories are excluded on purpose and it is the one exclusion worth
    arguing about. A control that PINS the removal has to name what it forbids
    (`test_no_default_path_to_the_reference_corpus_is_stored` asserts
    `expanduser` is absent from the census script), and a hermetic fixture
    legitimately builds a stand-in external root under `tempfile`. Both trip R4.
    The cost is that a helper under a tests directory could reintroduce an
    escape unseen; the benefit is that the controls enforcing this rule can
    exist at all.
    """
    findings: list[str] = []
    files = 0
    for root, pattern in SOURCE_ROOTS:
        if not root.is_dir():
            continue
        for path in sorted(root.glob(pattern)):
            if "tests" in path.parts:
                continue
            rel = path.relative_to(ROOT) if path.is_relative_to(ROOT) else path
            text = path.read_text(encoding="utf-8")
            files += 1
            # The module docstring may NAME a removed escape as history; only
            # the code below it is scanned. `check-reachability-census.py`
            # documents exactly the default path it used to carry.
            code = text.split('"""', 2)[2] if text.count('"""') >= 2 else text
            for needle, why in ESCAPE_EXPRESSIONS:
                if needle in code:
                    findings.append(f"{rel}: `{needle}` is {why} (ADR-0553 R4)")
    return findings, files


def vacuity(files: int, strings: int, script_files: int) -> list[str]:
    """A scan that examined nothing must FAIL, never pass.

    An empty result from a tool that was never pointed at its subject is
    indistinguishable from a strong negative result -- and this gate's whole
    value is the zero it prints, so the zero has to be earned. Three separate
    guards, because they fail for three different reasons: no files matched, the
    walker stopped reaching leaves, and the source rule lost its directory.
    """
    findings: list[str] = []
    if files == 0:
        findings.append(
            f"scanned 0 JSON artifacts under {ARTIFACTS} -- the gate was not "
            "pointed at anything"
        )
    if strings == 0:
        findings.append(
            f"examined 0 string values across {files} file(s) -- the walker is "
            "not reaching the leaves"
        )
    if script_files == 0:
        findings.append(
            "scanned 0 python files across "
            f"{', '.join(str(r) for r, _ in SOURCE_ROOTS)} -- the source rule "
            "was not pointed at anything"
        )
    return findings


SELF_TEST_CASES = (
    (
        "R1 external source kind",
        {"sources": [{"id": "s", "kind": "external-repository"}]},
        "declares a dependency",
    ),
    (
        "R1 external-pinned resolution",
        {"namespaces": [{"id": "n", "resolution": "external-pinned"}]},
        "declares a dependency",
    ),
    (
        "R2 escaping path_hint",
        {"sources": [{"path_hint": "../math-education"}]},
        "`..` segment",
    ),
    (
        "R2 escaping path inside a longer value",
        {"provenance": {"sources": ["../math-education/graph/concepts/factorial.md"]}},
        "`..` segment",
    ),
    (
        "R3 unregistered revision key",
        {"provenance": {"graph_pin": "ce3e2a52e7c95075d69262b4d8f0ee8fe748f22c"}},
        "unregistered key",
    ),
    (
        "R3 unregistered revision key on an endpoint",
        {"links": [{"target": {"source_revision": "0" * 40}}]},
        "unregistered key",
    ),
)


def self_test() -> int:
    """Prove every rule fires, and that a clean document does not trip one.

    A gate whose only evidence is a green tree is indistinguishable from a
    no-op, and this repository has shipped that gate more than once. Both
    halves are asserted: each violation is caught, and a document built only
    from REGISTERED keys and local paths is not.
    """
    failures = 0
    for name, doc, expect in SELF_TEST_CASES:
        found, _seen = scan_document(doc, "<self-test>")
        if not any(expect in f for f in found):
            print(
                f"EXTERNAL_COUPLING_SELFTEST_ERROR|{name}: rule did not fire; "
                f"expected {expect!r}, got {found}",
                file=sys.stderr,
            )
            failures += 1
        else:
            print(f"  fires: {name}")

    clean = {
        "sources": [{"id": "axeyum", "kind": "local-repository", "path_hint": "."}],
        "provenance": {"axeyum_commit": "0" * 40, "mathlib_commit": "1" * 40},
    }
    found, seen = scan_document(clean, "<self-test>")
    if found:
        print(
            f"EXTERNAL_COUPLING_SELFTEST_ERROR|a clean document was rejected: {found}",
            file=sys.stderr,
        )
        failures += 1
    elif seen == 0:
        print(
            "EXTERNAL_COUPLING_SELFTEST_ERROR|the clean case examined no strings, "
            "so it proves nothing",
            file=sys.stderr,
        )
        failures += 1
    else:
        print(f"  passes: a clean document ({seen} strings examined)")

    print(
        f"EXTERNAL_COUPLING_SELFTEST|rules={len(SELF_TEST_CASES)}|failures={failures}"
    )
    return 1 if failures else 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args(argv if argv is not None else sys.argv[1:])
    if args.self_test:
        return self_test()

    findings, files, strings = scan_artifacts()
    script_findings, script_files = scan_source()
    findings.extend(script_findings)
    findings.extend(vacuity(files, strings, script_files))

    for finding in findings:
        print(f"EXTERNAL_COUPLING_ERROR|{finding}", file=sys.stderr)
    print(
        "EXTERNAL_COUPLING|"
        f"artifacts={files}|strings={strings}|scripts={script_files}|"
        f"registered_revision_keys={len(REVISION_KEYS)}|findings={len(findings)}"
    )
    return 1 if findings else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))

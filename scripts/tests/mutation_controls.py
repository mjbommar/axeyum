#!/usr/bin/env python3
"""Delete one guard at a time and require each deletion to kill a test.

A guard nobody can remove is decoration.  This harness copies a generator into
a scratch tree, applies one textual mutation (each of which removes exactly one
guard), runs that generator's unittest module, and reports which tests died.

Usage::

    python3 scripts/tests/mutation_controls.py            # both generators
    python3 scripts/tests/mutation_controls.py adr-index  # one of them

Exit status is 0 only when every mutation killed at least one test.  It prints
the surviving mutations, which are the guards you have not actually tested.

This is a control, not a gate: it rewrites a scratch copy of the repository, so
it is run deliberately rather than from `scripts/check.sh`.
"""

from __future__ import annotations

import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]

# (generator, test module, [(mutation name, find, replace), ...])
SUITES: dict[str, tuple[str, str, list[tuple[str, str, str]]]] = {
    "adr-index": (
        "scripts/gen-adr-index.py",
        "scripts.tests.test_gen_adr_index",
        [
            (
                "heading-shape guard",
                "    if heading is None:\n        raise AdrError(",
                "    if False:\n        raise AdrError(",
            ),
            (
                "front-matter stop",
                "        if field is None:\n            break",
                "        if field is None:\n            index += 1\n            continue",
            ),
            (
                "Status-required guard",
                '    if "Status" not in front:\n        raise AdrError(f"{path.name}: no \'Status:\' line in its front matter")',
                '    if "Status" not in front:\n        front["Status"] = ""',
            ),
            (
                "pipe-in-cell guard",
                '        if "|" in cell:',
                "        if False:",
            ),
            (
                "empty-directory guard",
                "    if not adrs:",
                "    if False and not adrs:",
            ),
            (
                "filename sort tiebreak",
                '    return (adr["number"], adr["path"])',
                '    return (adr["number"], "")',
            ),
            (
                "preamble own-index guard",
                '    if "## Index" in preamble:',
                "    if False:",
            ),
            (
                "preamble h1 guard",
                '    if not body or not body[0].startswith("# "):',
                "    if False:",
            ),
            (
                "--check staleness guard",
                "        if current != rendered:",
                "        if False:",
            ),
        ],
    ),
    "plan": (
        "scripts/gen-plan.py",
        "scripts.tests.test_gen_plan",
        [
            (
                "lane-heading guard",
                '    if not heading.startswith("# "):',
                "    if False:",
            ),
            (
                "lane unknown-section guard",
                "            if name not in SECTIONS:",
                "            if False:",
            ),
            (
                "lane repeated-section guard",
                "            if name in contributions:",
                "            if False:",
            ),
            (
                "text-before-first-marker guard",
                "            if line.strip():",
                "            if False:",
            ),
            (
                "landed-row shape guard",
                "            if row is None:",
                "            if False:",
            ),
            (
                "landed-row ordering tiebreak",
                '    return (_negated_date(str(row["date"])), str(row["lane"]), int(row["ordinal"]))',
                '    return (_negated_date(str(row["date"])), "", 0)',
            ),
            (
                "empty-global guard",
                "    if not global_parts:",
                "    if False:",
            ),
            (
                "unknown-placeholder guard",
                "            if section not in SECTIONS:",
                "            if False:",
            ),
            (
                "repeated-placeholder guard",
                "            if section in seen:",
                "            if False:",
            ),
            (
                "missing-placeholder guard",
                "        if name not in seen:",
                "        if False:",
            ),
            (
                "plan-heading guard",
                '    if not body or not body[0].startswith("# "):',
                "    if False:",
            ),
            (
                "required-plan-marker guard",
                "        if marker not in rendered:",
                "        if False:",
            ),
            (
                "--check staleness guard",
                "        if current != rendered:",
                "        if False:",
            ),
        ],
    ),
    "lra-hypothesis-binding": (
        "scripts/check-lra-hypothesis-binding.py",
        "scripts.tests.test_check_lra_hypothesis_binding",
        [
            (
                "injectivity of the renaming",
                "            if cand_var in used:\n                continue",
                "            if False:\n                continue",
            ),
            (
                "sort-soundness of the renaming",
                "            if not sort_compatible(carriers.get(var), sorts.get(cand_var)):\n                continue",
                "            if False:\n                continue",
            ),
            (
                "search completeness (all permutations, not the first)",
                "                found = extend(index + 1, next_phi, next_used, origins + (origin,))\n                if found is not None:\n                    return found",
                "                return extend(index + 1, next_phi, next_used, origins + (origin,))",
            ),
            (
                "unaccounted-axiom guard",
                "    if unaccounted:\n        return (None, [], set(), \"; \".join(unaccounted))",
                "    if False:\n        return (None, [], set(), \"; \".join(unaccounted))",
            ),
            (
                "carrier is an opaque constant of the right sort",
                "            if ty != carrier_hit:",
                "            if False:",
            ),
            (
                "re-check of whatever the search returned",
                "    problems = verify_binding(phi, hypotheses, allowed, carriers, sorts)\n    if problems:",
                "    problems = verify_binding(phi, hypotheses, allowed, carriers, sorts)\n    if False:",
            ),
            (
                "re-check: every renamed hypothesis is a query atom",
                "        if _rename(atom, phi) not in allowed:",
                "        if False:",
            ),
            (
                "re-check: injectivity",
                "        if target in seen:",
                "        if False:",
            ),
            (
                "sign is not normalized away on an inequality",
                '    if rel == "=":',
                "    if True:",
            ),
            (
                "a disjunction entails neither disjunct",
                '    if (head == "and" and polarity) or (head == "or" and not polarity):',
                '    if head in ("and", "or"):',
            ),
            (
                "a disequality entails neither bound",
                '    if head == "=" and polarity and len(args) >= 2:',
                '    if head == "=" and len(args) >= 2:',
            ),
            (
                "an unknown rendered leaf is not a fresh variable",
                "        if expr.startswith(QUERY_NAMESPACE):\n            return ({expr: Fraction(1)}, Fraction(0))",
                "        if True:\n            return ({expr: Fraction(1)}, Fraction(0))",
            ),
        ],
    ),
}


def baseline_and_mutants(name: str) -> int:
    generator, test_module, mutations = SUITES[name]
    survivors: list[str] = []

    with tempfile.TemporaryDirectory(prefix=f"mutation-{name}-") as tmp:
        work = Path(tmp) / "repo"
        shutil.copytree(
            ROOT,
            work,
            ignore=shutil.ignore_patterns(
                ".git", "target", "references", "corpus", "bench-results", "__pycache__"
            ),
            symlinks=True,
        )
        source = work / generator
        original = source.read_text(encoding="utf-8")

        def run() -> tuple[int, str]:
            done = subprocess.run(
                [sys.executable, "-m", "unittest", test_module],
                cwd=work,
                capture_output=True,
                text=True,
            )
            return done.returncode, done.stderr

        code, _ = run()
        if code != 0:
            print(f"{name}: BASELINE IS RED; fix the tests before mutating")
            return 1
        print(f"{name}: baseline green")

        for label, find, replace in mutations:
            if find not in original:
                print(f"  {label:34s} MUTATION DID NOT APPLY (guard text moved)")
                survivors.append(label)
                continue
            source.write_text(original.replace(find, replace, 1), encoding="utf-8")
            code, stderr = run()
            source.write_text(original, encoding="utf-8")
            killed = [
                line.split(" ", 2)[1]
                for line in stderr.splitlines()
                if line.startswith(("FAIL: ", "ERROR: "))
            ]
            if code == 0:
                print(f"  {label:34s} SURVIVED — no test depends on this guard")
                survivors.append(label)
            else:
                print(f"  {label:34s} killed {len(killed)}: {', '.join(killed) or 'see output'}")

    if survivors:
        print(f"{name}: {len(survivors)} guard(s) not covered by any test")
        return 1
    return 0


def main(argv: list[str]) -> int:
    names = argv[1:] or sorted(SUITES)
    failed = 0
    for name in names:
        if name not in SUITES:
            print(f"unknown suite {name!r}; known: {', '.join(sorted(SUITES))}")
            return 2
        failed |= baseline_and_mutants(name)
    return failed


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))

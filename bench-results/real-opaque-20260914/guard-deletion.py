#!/usr/bin/env python3
"""REAL-OPAQUE -- delete ONE guard at a time and record which tests die.

The rule this exists for: six of seven guards in one suite here were removable
with everything still green, because they all rejected through one shared
check. A guard whose deletion kills nothing is not a guard. A guard whose
deletion kills the SAME test as another guard's deletion is one guard wearing
two hats, and the matrix has to say so rather than the prose claiming five.

Runs from the repository root. Mutates a file, runs the suite, restores from
`git checkout HEAD -- <file>` (both files are committed and otherwise clean --
asserted before anything is touched), and prints one row per guard.

NOT a `cargo mutants` run and not a Python `__pycache__` loop: each mutant is a
real edit, a real `cargo test`, and the restore is verified by `git diff --exit-code`.
"""

import json
import subprocess
import sys

SOLVER = "crates/axeyum-solver/src"

# BOTH halves of the registered suite. The integration file alone cannot observe
# `replayed_sat` / `simplex_fallback` at all -- the entry point above them
# returns a type with no `Sat` variant -- so the lib-side filter is not a
# convenience, it is the only place those two guards are visible.
# Tests that read the SOURCE TEXT rather than run the solver. They die on every
# mutant here, because the mutants ARE source-text edits -- which makes them a
# universal killer and destroys the matrix's whole purpose: with this test
# counted, `G5-model-oracle` reads "killed=1" and looks load-bearing when in
# fact nothing behavioural observes it. A single check that rejects EVERYTHING
# is the same disease as a single check that rejects nothing.
#
# Excluded here and ONLY here. The pin is a real guard against a new `Sat` site
# appearing, and it runs in the suite; it is just not evidence about which
# runtime guard is load-bearing.
TEXT_PINS = {
    "the_sat_exit_enumeration_still_describes_the_source",
    "the_brace_stripper_ignores_braces_that_are_not_braces",
}

SUITES = [
    ("--test", "lra_opaque_real_apps", []),
    ("--lib", None, ["opaque_real_guard_tests"]),
]

# (id, file, needle, replacement, what it closes)
GUARDS = [
    (
        "G1-replayed-sat",
        f"{SOLVER}/lra.rs",
        "    if ctx.has_opaque_vars() {\n        return Ok(Decision::Incomplete(",
        "    if false && ctx.has_opaque_vars() {\n        return Ok(Decision::Incomplete(",
        "Fourier-Motzkin sat exit",
    ),
    (
        "G2-simplex-fallback",
        f"{SOLVER}/lra.rs",
        # Re-anchored for the ADR-2060 merge: `simplex_fallback` now returns a
        # NAMED `SimplexDecline` instead of a `Decision`, so the guard's body
        # changed even though the guard did not.
        "            if ctx.has_opaque_vars() {\n                return Ok(Err(SimplexDecline::OpaqueAbstractionSatisfiable));",
        "            if false && ctx.has_opaque_vars() {\n                return Ok(Err(SimplexDecline::OpaqueAbstractionSatisfiable));",
        "exact-rational simplex sat exit",
    ),
    (
        "G3-support-fast-path",
        f"{SOLVER}/dpll_lia.rs",
        "if !self.ctx.has_opaque_int_apps(arena) && !self.ctx.has_opaque_real_apps(arena) {",
        "if !self.ctx.has_opaque_int_apps(arena) {",
        "dpll_lia support-set sat exit",
    ),
    (
        "G4-full-path",
        f"{SOLVER}/dpll_lia.rs",
        "            if self.ctx.has_opaque_real_apps(arena) {",
        "            if false && self.ctx.has_opaque_real_apps(arena) {",
        "dpll_lia full-path sat exit",
    ),
    (
        "G5-model-oracle",
        f"{SOLVER}/dpll_lia.rs",
        "theory_model(arena, &real_lits, real_model_oracle, deadline)",
        "theory_model(arena, &real_lits, real_theory_oracle, deadline)",
        "sat-model reconstruction uses the UNabstracted decider",
    ),
]


# Composites. The guards on this route are NESTED (entry gate -> model oracle
# -> replay -> the outcome TYPE), not parallel, so removing an inner one is
# invisible while an outer one still returns. These peel them in order and are
# the only way to say how deep the closure actually goes -- and, for the last
# one, to record that the deepest layer cannot be removed by any local edit
# because it is a type with no `Sat` variant.
COMPOSITES = [
    ("C1-both-entry-gates", ["G3-support-fast-path", "G4-full-path"]),
    (
        "C2-entry-gates-and-model-oracle",
        ["G3-support-fast-path", "G4-full-path", "G5-model-oracle"],
    ),
    (
        "C3-everything-but-the-type",
        [
            "G1-replayed-sat",
            "G2-simplex-fallback",
            "G3-support-fast-path",
            "G4-full-path",
            "G5-model-oracle",
        ],
    ),
]


def sh(args, **kw):
    return subprocess.run(args, capture_output=True, text=True, **kw)


def assert_clean(paths):
    for p in paths:
        d = sh(["git", "diff", "--exit-code", "--", p])
        if d.returncode != 0:
            sys.exit(f"ABORT: {p} has uncommitted changes; a mutation run would lose them")


def run_suite():
    """Returns (ok, {'passed': [...], 'failed': [...]}) over the whole suite."""
    failed, passed = set(), set()
    for kind, name, filters in SUITES:
        cmd = [
            "scripts/cargo-serialized.sh",
            "test",
            "-p",
            "axeyum-solver",
            "--features",
            "full",
            kind,
        ]
        if name:
            cmd.append(name)
        cmd += ["--", "--test-threads=4", *filters]
        r = sh(cmd)
        out = r.stdout + r.stderr
        if "error[E" in out or "error: could not compile" in out:
            return None, {"__COMPILE__": out[-2000:]}
        for line in out.splitlines():
            line = line.strip()
            if line.startswith("test ") and line.endswith(" ... ok"):
                passed.add(line[5:-7])
            elif line.startswith("test ") and " ... FAILED" in line:
                failed.add(line[5 : line.index(" ... FAILED")])
    behavioural = {t for t in failed if t.rsplit("::", 1)[-1] not in TEXT_PINS}
    return (len(failed) == 0), {
        "passed": sorted(passed),
        "failed": sorted(behavioural),
        "text_pins_also_failed": sorted(failed - behavioural),
    }


def main():
    files = sorted({g[1] for g in GUARDS})
    assert_clean(files)

    print("== baseline (no mutation) ==")
    ok, base = run_suite()
    if ok is None:
        sys.exit("ABORT: baseline does not compile\n" + base["__COMPILE__"])
    if not ok:
        sys.exit(f"ABORT: baseline is RED, mutation says nothing: {base['failed']}")
    print(f"   {len(base['passed'])} passed, 0 failed")

    rows = []
    for gid, path, needle, repl, what in GUARDS:
        src = open(path).read()
        n = src.count(needle)
        if n != 1:
            rows.append(
                {"guard": gid, "what": what, "status": f"ANCHOR-NOT-UNIQUE({n})", "killed": []}
            )
            print(f"   {gid}: ANCHOR MATCHED {n} PLACES -- not mutated")
            continue
        open(path, "w").write(src.replace(needle, repl))
        try:
            ok, res = run_suite()
            if ok is None:
                status, killed = "DOES-NOT-COMPILE", []
            else:
                killed = res["failed"]
                status = "ok" if killed else "SURVIVED"
        finally:
            sh(["git", "checkout", "HEAD", "--", path])
            assert_clean([path])
        rows.append({"guard": gid, "what": what, "status": status, "killed": killed})
        print(f"   {gid}: {status} killed={len(killed)} {killed}")

    by_id = {g[0]: g for g in GUARDS}
    for cid, members in COMPOSITES:
        touched = sorted({by_id[m][1] for m in members})
        applied = True
        for m in members:
            _, path, needle, repl, _ = by_id[m]
            src = open(path).read()
            if src.count(needle) != 1:
                applied = False
                break
            open(path, "w").write(src.replace(needle, repl))
        try:
            if not applied:
                status, killed = "ANCHOR-NOT-UNIQUE", []
            else:
                ok, res = run_suite()
                if ok is None:
                    status, killed = "DOES-NOT-COMPILE", []
                else:
                    killed = res["failed"]
                    status = "ok" if killed else "SURVIVED"
        finally:
            for path in touched:
                sh(["git", "checkout", "HEAD", "--", path])
            assert_clean(touched)
        rows.append(
            {
                "guard": cid,
                "what": "composite: " + " + ".join(members),
                "status": status,
                "killed": killed,
            }
        )
        print(f"   {cid}: {status} killed={len(killed)} {killed}")

    json.dump(
        {"baseline_passed": base["passed"], "rows": rows},
        open("bench-results/real-opaque-20260914/ref/guard-deletion.json", "w"),
        indent=2,
    )
    print("\nwrote ref/guard-deletion.json")

    survivors = [r for r in rows if r["status"] == "SURVIVED"]
    if survivors:
        print(f"\nSURVIVORS (a guard nothing tests): {[r['guard'] for r in survivors]}")
        sys.exit(1)
    # The exit status depends on the finding, which is the whole point.
    print("\nevery guard has a killer")


if __name__ == "__main__":
    main()

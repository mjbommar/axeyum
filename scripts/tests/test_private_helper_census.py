#!/usr/bin/env python3
"""Controls for `scripts/private-helper-census.py`.

A census whose `--check` cannot go red is worse than no census: it makes the
committed artifact look measured while it drifts. So the controls here are
adversarial rather than confirmatory, and each names the defect it would catch.

  GREEN    `--check` is 0 against the committed tree. The baseline; without it
           every red below is uninterpretable.
  STALE    `--check` is 1 when the artifact's bytes differ. This is the arm
           that makes the gate a gate.
  MISSING  `--check` is 1 when the artifact is absent, rather than exiting 0
           on a file it never read.
  NORMALIZE  two functions differing ONLY by receiver name and carrier type
           hash EQUAL, and two differing in a real step hash DIFFERENT. The
           second half is the one that matters: a normalizer that collapsed
           everything would report enormous, meaningless groups.
  STRINGS  two functions differing only in a string literal hash DIFFERENT.
           Masking literal content (the easy implementation) would merge every
           `declare_theorem` script in the crate into one group.
  COMMENTS a comment does not change the digest, and a `{` inside a comment or
           a string does not truncate the body.
  LIFETIME `&mut NatDev<'_>` is not read as an unterminated char literal --
           the failure mode that would silently blank the rest of every file.
  PUBLIC   a `pub` fn is EXCLUDED. The census is about steps a name search
           cannot reach; counting public helpers would inflate every group.

Run:  python3 scripts/tests/test_private_helper_census.py
Exit 0 when every control passes, 1 on any failure.
"""

from __future__ import annotations

import importlib.util
import pathlib
import shutil
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "private-helper-census.py"
ARTIFACT = ROOT / "artifacts" / "refactor" / "private-helper-census.json"


def load_module():
    spec = importlib.util.spec_from_file_location("phc", SCRIPT)
    assert spec and spec.loader
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def run_check(cwd: pathlib.Path) -> int:
    return subprocess.run(
        [sys.executable, str(cwd / "scripts" / "private-helper-census.py"),
         "--check"],
        cwd=cwd, capture_output=True, text=True, check=False).returncode


def sandbox(work: pathlib.Path) -> pathlib.Path:
    """A copy carrying only what the census reads and writes."""
    root = work / "tree"
    (root / "scripts").mkdir(parents=True)
    shutil.copy2(SCRIPT, root / "scripts" / SCRIPT.name)
    (root / "artifacts" / "refactor").mkdir(parents=True)
    if ARTIFACT.is_file():
        shutil.copy2(ARTIFACT, root / "artifacts" / "refactor" / ARTIFACT.name)
    shutil.copytree(ROOT / "crates" / "axeyum-lean-kernel" / "src",
                    root / "crates" / "axeyum-lean-kernel" / "src")
    return root


def digest_of(mod, source: str, name: str) -> str | None:
    """The body digest the census computes for `name` in `source`."""
    with tempfile.TemporaryDirectory() as td:
        path = pathlib.Path(td) / "m.rs"
        path.write_text(source)
        for site in mod.scan(path, "m.rs"):
            if site["name"] == name:
                return site["body_digest"]
    return None


def sites_of(mod, source: str) -> list[dict]:
    with tempfile.TemporaryDirectory() as td:
        path = pathlib.Path(td) / "m.rs"
        path.write_text(source)
        return mod.scan(path, "m.rs")


def main() -> int:
    mod = load_module()
    fails: list[str] = []

    def check(name: str, ok: bool, detail: str) -> None:
        if ok:
            print(f"  ok   {name}: {detail}")
        else:
            fails.append(f"{name}: {detail}")
            print(f"  FAIL {name}: {detail}")

    print("private-helper-census controls")

    # --- GREEN / STALE / MISSING ------------------------------------------
    with tempfile.TemporaryDirectory() as td:
        root = sandbox(pathlib.Path(td))
        check("GREEN", run_check(root) == 0,
              "--check is 0 against an unmodified tree")

        target = root / "artifacts" / "refactor" / ARTIFACT.name
        original = target.read_text()
        target.write_text(original.replace('"schema_version": 1',
                                           '"schema_version": 2', 1))
        check("STALE", run_check(root) == 1,
              "--check is 1 when the committed artifact's bytes differ")

        target.unlink()
        check("MISSING", run_check(root) == 1,
              "--check is 1 when the artifact is absent")

    # --- NORMALIZE ---------------------------------------------------------
    a = ("fn step(d: &mut NatDev<'_>, x: ExprId) -> ExprId {\n"
         "    let t = d.nat_ty();\n    d.apply(t, &[x])\n}\n")
    b = ("fn step(dev: &mut IntDev<'_>, x: ExprId) -> ExprId {\n"
         "    let t = dev.nat_ty();\n    dev.apply(t, &[x])\n}\n")
    check("NORMALIZE", digest_of(mod, a, "step") == digest_of(mod, b, "step"),
          "receiver name and carrier type normalize to the same digest")

    c = ("fn step(d: &mut NatDev<'_>, x: ExprId) -> ExprId {\n"
         "    let t = d.bool_ty();\n    d.apply(t, &[x])\n}\n")
    check("NORMALIZE-neg", digest_of(mod, a, "step") != digest_of(mod, c, "step"),
          "a different proof step gives a different digest "
          "(the normalizer does not collapse everything)")

    # --- STRINGS -----------------------------------------------------------
    s1 = 'fn d1(d: &mut NatDev<\'_>) { d.declare_theorem("Nat.add_comm"); }\n'
    s2 = 'fn d1(d: &mut NatDev<\'_>) { d.declare_theorem("Nat.mul_comm"); }\n'
    check("STRINGS", digest_of(mod, s1, "d1") != digest_of(mod, s2, "d1"),
          "string literal content is kept, so two declaration scripts naming "
          "different theorems do not merge")

    # --- COMMENTS ----------------------------------------------------------
    k1 = 'fn k(d: &mut NatDev<\'_>) { let s = "a { b"; d.go(s); }\n'
    k2 = ('fn k(d: &mut NatDev<\'_>) {\n'
          '    // a { comment with an unbalanced brace\n'
          '    let s = "a { b"; d.go(s);\n}\n')
    check("COMMENTS", digest_of(mod, k1, "k") == digest_of(mod, k2, "k"),
          "a comment does not change the digest and an unbalanced `{` inside "
          "a comment or a string does not truncate the body")

    # --- LIFETIME ----------------------------------------------------------
    lt = ("fn one(d: &mut NatDev<'_>) -> ExprId { d.zero() }\n"
          "fn two(d: &mut NatDev<'_>) -> ExprId { d.zero() }\n")
    names = {s["name"] for s in sites_of(mod, lt)}
    check("LIFETIME", names == {"one", "two"},
          f"`<'_>` is a lifetime, not a char literal; found {sorted(names)}")

    # --- PUBLIC ------------------------------------------------------------
    vis = ("pub fn shown(d: &mut NatDev<'_>) -> ExprId { d.zero() }\n"
           "pub(crate) fn hidden(d: &mut NatDev<'_>) -> ExprId { d.zero() }\n"
           "fn bare(d: &mut NatDev<'_>) -> ExprId { d.zero() }\n")
    got = {s["name"]: s["visibility"] for s in sites_of(mod, vis)}
    check("PUBLIC", got == {"hidden": "pub(crate)", "bare": "private"},
          f"`pub` is excluded and the rest are classified; got {got}")

    print()
    if fails:
        print(f"PRIVATE_HELPER_CENSUS_CONTROLS FAIL ({len(fails)})")
        return 1
    print("PRIVATE_HELPER_CENSUS_CONTROLS ok|controls=8")
    return 0


if __name__ == "__main__":
    sys.exit(main())

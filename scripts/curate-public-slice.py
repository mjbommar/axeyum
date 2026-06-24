#!/usr/bin/env python3
"""Curate clean, parser-faithful, status-annotated SMT-LIB slices from the
cvc5 regress suite, mirroring the committed
QF_UF / QF_LRA / QF_UFLIA / QF_LIA / QF_NRA / QF_NIA filter for
`corpus/public-curated/`. Reproducible record of the curation.

This filter is validated: `--prefix QF_UF` re-derives the 103 clean QF_UF-family
files (the committed 88-file bounded slice plus its 15 excluded files) exactly,
and the exact-logic match re-derives QF_NRA (38 files) and QF_NIA (39 files)
byte-for-byte.

Usage: curate-public-slice.py <LOGIC_PATTERN> <out_dir|-> [--prefix] [--root DIR]
  --prefix : match any (set-logic X) where X starts with LOGIC_PATTERN
             (the QF_UF "family" filter). Default is exact-logic match.
             out_dir "-" lists the selection without copying.
  --root DIR : scan DIR instead of the default cvc5 regress root. Used for the
             bitwuzla QF_ABV slice (`references/bitwuzla/test/regress`); the
             flattened vendored name is relative to DIR.

Selects files under the scan root (default references/cvc5/test/regress/) that:
  - declare a matching (set-logic ...)
  - carry a (set-info :status ...)
  - use only plain (assert ...) + (check-sat)  [no forbidden commands]
  - are not .smtv1.smt2
Vendored name flattens path relative to test/regress/ : '/' -> '__'.
"""
import sys, os, re, shutil

REGRESS_ROOT = "references/cvc5/test/regress"

# Exotic/incremental commands that the flat benchmark-slice parser cannot
# faithfully represent (from the committed README filter, extended).
FORBIDDEN_CMDS = [
    "check-sat-assuming", "get-value", "get-model", "get-unsat-core",
    "push", "pop", "reset-assertions", "get-info", "get-assignment",
    "define-fun-rec", "echo", "get-unsat-assumptions", "get-interpolant",
    "get-abduct", "get-proof", "reset", "declare-pool", "block-model",
]

def has_cmd(text, cmd):
    return re.search(r"\(\s*" + re.escape(cmd) + r"\b", text) is not None

def logic_matches(text, pat, prefix):
    if prefix:
        return re.search(r"\(\s*set-logic\s+" + re.escape(pat) + r"[A-Za-z0-9_]*\s*\)", text) is not None
    return re.search(r"\(\s*set-logic\s+" + re.escape(pat) + r"\s*\)", text) is not None

def curate(pat, out_dir, prefix, root=REGRESS_ROOT):
    selected = []
    for dirpath, _dirs, files in os.walk(root):
        for fn in sorted(files):
            if not fn.endswith(".smt2") or fn.endswith(".smtv1.smt2"):
                continue
            full = os.path.join(dirpath, fn)
            try:
                text = open(full, "r", encoding="utf-8", errors="replace").read()
            except Exception:
                continue
            if not logic_matches(text, pat, prefix):
                continue
            if not re.search(r"\(\s*set-info\s+:status\b", text):
                continue
            if any(has_cmd(text, c) for c in FORBIDDEN_CMDS):
                continue
            # drop set-option :incremental true and :produce-models true
            if re.search(r"set-option\s+:incremental\s+true", text):
                continue
            if re.search(r"set-option\s+:produce-models\s+true", text):
                continue
            # drop files with zero (assert ...) — flat view would solve a
            # different (vacuous) problem than the source intends.
            if not has_cmd(text, "assert"):
                continue
            selected.append(full)

    if out_dir != "-":
        os.makedirs(out_dir, exist_ok=True)
    names = []
    for full in selected:
        rel = os.path.relpath(full, root)
        flat = rel.replace("/", "__")
        if out_dir != "-":
            shutil.copyfile(full, os.path.join(out_dir, flat))
        names.append(flat)
    return names

if __name__ == "__main__":
    args = sys.argv[1:]
    prefix = "--prefix" in args
    root = REGRESS_ROOT
    if "--root" in args:
        i = args.index("--root")
        root = args[i + 1]
        del args[i : i + 2]
    args = [a for a in args if a != "--prefix"]
    pat, out_dir = args[0], args[1]
    names = curate(pat, out_dir, prefix, root)
    print(f"{pat} (prefix={prefix}, root={root}): {len(names)} files")
    for n in names:
        print("  " + n)

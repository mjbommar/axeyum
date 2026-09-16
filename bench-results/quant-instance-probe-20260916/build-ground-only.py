#!/usr/bin/env python3
"""QUANT-INSTANCE-PROBE step 2: build the ground-only file for one core.

    build-ground-only.py <core.smt2> <instances.json> <out.smt2>

Takes the original core file, strips every quantified `assert`
(`scripts/strip-quantified-assertions.py`, imported rather than
re-implemented), appends z3's own recovered GROUND instantiated bodies
(`scripts/z3-proof-instances.py --json`'s `bodies` field -- the `not_ground`
field is deliberately NOT used: those bodies still carry an unresolved outer
bound variable from a nested instantiation and are not valid SMT-LIB), and
rewrites `(set-logic ...)` to `QF_UFLIA`.

This file's own correctness claim is bounded, not assumed: whether the
result is actually `unsat` is a SEPARATE check
(`check-ground-only-unsat.sh`), because dropping the `not_ground` bodies can
make the reconstruction incomplete -- exactly the failure mode the lane
brief asks to be reported, not hidden.

Exit status depends on the finding: 0 written normally, 3 if the input core
has no quantified assert to strip (nothing to reconstruct FROM), 4 if the
instances file recovered zero ground bodies (nothing to reconstruct WITH --
the resulting file would just be the stripped original, silently measuring
whatever `strip-quantified-assertions.py` already answers).
"""

from __future__ import annotations

import importlib.util
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
STRIP_SCRIPT = ROOT / "scripts" / "strip-quantified-assertions.py"
_spec = importlib.util.spec_from_file_location("strip_quantified_assertions", STRIP_SCRIPT)
assert _spec is not None and _spec.loader is not None
strip_mod = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(strip_mod)

SET_LOGIC_RE = re.compile(r"\(set-logic\s+[A-Za-z_][A-Za-z0-9_]*\s*\)")
CHECK_SAT_RE = re.compile(r"\(check-sat\)")


def build(original_text: str, instances_json: dict) -> tuple[str, dict]:
    """Returns (rewritten_text, stats). Raises ValueError on an unparseable
    original file (propagated from `strip_file`)."""
    result = strip_mod.strip_file(original_text)
    bodies = instances_json.get("bodies", [])

    text = result.text
    if SET_LOGIC_RE.search(text):
        text = SET_LOGIC_RE.sub("(set-logic QF_UFLIA)", text, count=1)
    else:
        text = "(set-logic QF_UFLIA)\n" + text

    assert_block = "".join(f"(assert {b})\n" for b in bodies)
    if CHECK_SAT_RE.search(text):
        text = CHECK_SAT_RE.sub(assert_block + "(check-sat)", text, count=1)
    else:
        text = text + assert_block + "(check-sat)\n"

    stats = {
        "quant_asserts_stripped": result.dropped,
        "ground_asserts_kept": result.kept,
        "instances_added": len(bodies),
        "not_ground_dropped": len(instances_json.get("not_ground", [])),
        "unmatched": instances_json.get("unmatched", 0),
    }
    return text, stats


def main(argv: list) -> int:
    if len(argv) != 4:
        sys.stderr.write(__doc__ or "")
        return 2
    core_path, inst_json_path, out_path = argv[1], argv[2], argv[3]

    original = Path(core_path).read_text(encoding="utf-8", errors="replace")
    instances = json.loads(Path(inst_json_path).read_text(encoding="utf-8"))

    try:
        text, stats = build(original, instances)
    except ValueError as exc:
        sys.stderr.write(f"PARSE-FAIL {core_path}: {exc}\n")
        return 3

    if stats["quant_asserts_stripped"] == 0:
        sys.stderr.write(f"DEGENERATE {core_path}: no quantified assert to strip\n")
        return 3
    if stats["instances_added"] == 0:
        sys.stderr.write(
            f"DEGENERATE {core_path}: zero ground instance bodies recovered "
            "(the output is just the stripped original)\n"
        )
        return 4

    Path(out_path).write_text(text, encoding="utf-8")
    print(
        "quant_stripped={quant_asserts_stripped} ground_kept={ground_asserts_kept} "
        "instances_added={instances_added} not_ground_dropped={not_ground_dropped} "
        "unmatched={unmatched}".format(**stats)
    )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))

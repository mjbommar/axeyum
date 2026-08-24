#!/usr/bin/env python3
"""Generate `crates/axeyum-py/src/kernel/prelude_fields.rs`.

The nine `*Prelude` structs in `axeyum-lean-kernel` carry **1,207 `NameId`
fields** between them (measured 2026-08-24). The Python binding hands a prelude
package to the caller as a flat, ordered `{field name -> NameId}` table, and
Rust has no reflection: the field list has to be written out. Writing it by hand
would rot silently the first time a prelude grows a theorem -- the failure would
be a *missing* attribute, which reads exactly like "that theorem does not
exist", the empty-result trap CLAUDE.md warns about.

So the table is generated from the struct definitions, and this script is the
generator. Run it after any prelude gains or loses a field:

    python3 scripts/gen-py-prelude-fields.py            # rewrite
    python3 scripts/gen-py-prelude-fields.py --check    # exit 1 if stale

`--check` is what a gate runs; it prints the measured field count per struct so
a run that parsed nothing cannot pass for a run that found no drift.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
KERNEL_SRC = ROOT / "crates" / "axeyum-lean-kernel" / "src"
TARGET = ROOT / "crates" / "axeyum-py" / "src" / "kernel" / "prelude_fields.rs"

# (rust struct, source file, python kind, builder fn) in dependency order.
PRELUDES = [
    ("LogicPrelude", "prelude.rs", "logic"),
    ("NatPrelude", "nat_prelude.rs", "nat"),
    ("IntPrelude", "int_prelude.rs", "int"),
    ("RatPrelude", "rat_prelude.rs", "rat"),
    ("ArithPrelude", "arith_prelude.rs", "arith"),
    ("CRealPrelude", "creal.rs", "creal"),
    ("ComplexPrelude", "complex.rs", "complex"),
    ("CPointPrelude", "creal_point.rs", "cpoint"),
    ("StringPrelude", "string_prelude.rs", "string"),
]

FIELD = re.compile(r"^\s{4}pub ([a-z_][a-z_0-9]*): ([A-Za-z0-9_<>, ]+),\s*$")


def struct_fields(struct: str, filename: str) -> list[tuple[str, str]]:
    """The `pub name: Type` fields of `struct`, in declaration order."""
    text = (KERNEL_SRC / filename).read_text(encoding="utf-8")
    start = text.index(f"pub struct {struct} {{")
    end = text.index("\n}\n", start)
    fields = []
    for line in text[start:end].splitlines():
        match = FIELD.match(line)
        if match:
            fields.append((match.group(1), match.group(2)))
    if not fields:
        raise SystemExit(f"error: parsed zero fields out of {struct} -- generator is broken")
    return fields


def render() -> tuple[str, dict[str, int]]:
    counts: dict[str, int] = {}
    out: list[str] = [
        "//! Field tables for the nine `*Prelude` packages -- GENERATED, do not edit.",
        "//!",
        "//! Regenerate with `python3 scripts/gen-py-prelude-fields.py`; the same script",
        "//! with `--check` fails when this file is stale. Rust has no reflection, so the",
        "//! binding's flat `{field name -> NameId}` view of a prelude package has to name",
        "//! every field, and a hand-written list rots into a MISSING attribute -- which",
        "//! reads exactly like `that theorem does not exist`.",
        "",
        "use axeyum_lean_kernel::{",
        "    ArithPrelude, CPointPrelude, CRealPrelude, ComplexPrelude, IntPrelude, LogicPrelude,",
        "    NameId, NatPrelude, RatPrelude, StringPrelude,",
        "};",
        "",
        "/// One package's flattened contents: scalar names, name lists, and the",
        "/// sub-packages it was built on top of.",
        "pub(super) struct Fields {",
        "    /// `(field name, interned name)`, in struct declaration order.",
        "    pub(super) names: Vec<(&'static str, NameId)>,",
        "    /// `(field name, interned names)` for the one `Vec<NameId>` field.",
        "    pub(super) lists: Vec<(&'static str, Vec<NameId>)>,",
        "}",
        "",
    ]
    for struct, filename, kind in PRELUDES:
        fields = struct_fields(struct, filename)
        scalars = [n for n, t in fields if t == "NameId"]
        lists = [n for n, t in fields if t == "Vec<NameId>"]
        nested = [(n, t) for n, t in fields if t.endswith("Prelude")]
        counts[kind] = len(scalars)
        out.append(f"/// The `{struct}` field table ({len(scalars)} names,")
        out.append(f"/// {len(lists)} name lists, {len(nested)} sub-packages).")
        out.append("#[must_use]")
        out.append(
            "#[allow(clippy::too_many_lines)] // a generated field table; length is the point."
        )
        out.append(f"pub(super) fn {kind}(p: &{struct}) -> Fields {{")
        out.append("    Fields {")
        out.append("        names: vec![")
        for name in scalars:
            out.append(f'            ("{name}", p.{name}),')
        out.append("        ],")
        if lists:
            out.append("        lists: vec![")
            for name in lists:
                out.append(f'            ("{name}", p.{name}.clone()),')
            out.append("        ],")
        else:
            out.append("        lists: Vec::new(),")
        out.append("    }")
        out.append("}")
        out.append("")
        if nested:
            out.append(f"/// The sub-packages `{struct}` carries, by field name.")
            out.append("#[must_use]")
            out.append(f"pub(super) fn {kind}_sub(p: &{struct}) -> Vec<(&'static str, Sub)> {{")
            out.append("    vec![")
            for name, ty in nested:
                variant = ty.removesuffix("Prelude")
                # Every sub-package type is `Copy`; `.clone()` here would trip
                # `clippy::clone_on_copy` under `-D warnings`.
                out.append(f'        ("{name}", Sub::{variant}(Box::new(p.{name}))),')
            out.append("    ]")
            out.append("}")
            out.append("")
    out.append("/// A sub-package carried inside another package.")
    out.append("pub(super) enum Sub {")
    for variant, struct in [
        ("Logic", "LogicPrelude"),
        ("Nat", "NatPrelude"),
        ("Int", "IntPrelude"),
        ("Rat", "RatPrelude"),
        ("CReal", "CRealPrelude"),
    ]:
        out.append(f"    /// A nested [`{struct}`].")
        out.append(f"    {variant}(Box<{struct}>),")
    out.append("}")
    out.append("")
    return "\n".join(out), counts


def rustfmt(text: str) -> str:
    """`text` as `rustfmt --edition 2024` would write it.

    The generated file is checked by `clippy -D warnings` and by `cargo fmt
    --check` like any other source file, so the generator has to emit the
    formatter's fixed point rather than something merely valid. Formatting here
    -- not as a separate step afterwards -- is what keeps `--check` meaningful:
    a post-hoc `rustfmt` would make every regenerated file read as stale.
    """
    scratch = TARGET.parent / "prelude_fields.rustfmt-scratch.rs"
    scratch.parent.mkdir(parents=True, exist_ok=True)
    scratch.write_text(text, encoding="utf-8")
    try:
        subprocess.run(
            ["rustfmt", "--edition", "2024", str(scratch)],
            check=True,
            capture_output=True,
        )
        return scratch.read_text(encoding="utf-8")
    except FileNotFoundError:
        print("PRELUDE-FIELDS|WARN rustfmt not on PATH -- emitting unformatted")
        return text
    finally:
        scratch.unlink(missing_ok=True)


def main() -> int:
    text, counts = render()
    text = rustfmt(text)
    total = sum(counts.values())
    summary = ", ".join(f"{k}={v}" for k, v in counts.items())
    print(f"PRELUDE-FIELDS|total={total}|{summary}")
    if total == 0:
        print("PRELUDE-FIELDS|FAIL parsed zero fields")
        return 1
    if "--check" in sys.argv:
        current = TARGET.read_text(encoding="utf-8") if TARGET.exists() else ""
        if current != text:
            print(f"PRELUDE-FIELDS|FAIL {TARGET} is stale -- rerun without --check")
            return 1
        print("PRELUDE-FIELDS|OK up to date")
        return 0
    TARGET.write_text(text, encoding="utf-8")
    print(f"PRELUDE-FIELDS|wrote {TARGET}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

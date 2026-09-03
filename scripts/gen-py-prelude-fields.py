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

## Registry fields (ADR-1512), and the silent shrink they caused

`CRealPrelude` is now a **facade**: a module's names live in a `Copy` registry
struct owned by `creal/<module>.rs` (`pub pi: PiNames`, `pub completeness:
CompletenessNames`, …), not as flat fields on the prelude. The first version of
this script matched `pub <name>: NameId` and nothing else, so on the day the
split landed (`8dd580a1c`) a regeneration DROPPED every migrated field from the
Python surface -- 69 of `CRealPrelude`'s 606 names disappeared and no gate said
a word, because a shrinking generated file is indistinguishable from a prelude
that lost a theorem.

Two changes close that:

1. A registry field is **flattened with a dotted name**: `PiNames::pi_le_four`
   reaches Python as `p["pi.pi_le_four"]`. Dotted, not flattened bare, because
   two modules may legitimately declare the same leaf name and because the
   dotted form says where the name lives. `__getattr__`, `__getitem__`,
   `to_dict`, `field_names` and `__contains__` all take it unchanged.
2. **An unclassified field type is a hard error**, not a skip. That is the
   actual defect: the parser silently ignored what it did not understand, so
   the next structural change to a prelude will fail loudly here instead of
   quietly amputating the binding.
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
#
# `ListPrelude` (`list_prelude.rs`) added 2026-09-03: `List.{u}`'s own field
# table (the inductive plus `length`/`append`/`map`/`foldr`/`reverse` and the
# six pure-`List` theorems) is all plain `NameId`, so it registers cleanly.
# `ListNatBridge`/`ListPerm` (`list_prelude/bridge.rs`, `list_prelude/perm.rs`)
# are deliberately NOT registered here: `ListNatBridge::count_to_multiset` is
# `Option<NameId>`, a type this generator's `collect()` does not classify (see
# its own module doc), and teaching it optional fields is out of this lane's
# scope.
PRELUDES = [
    ("LogicPrelude", "prelude.rs", "logic"),
    ("ListPrelude", "list_prelude.rs", "list"),
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
# ADR-1512's per-module registries. The naming rule is
# `scripts/creal-migrate-registry.py::struct_name`: the module name in
# CamelCase plus `Names`, so `creal/ivt_boundary.rs` owns `IvtBoundaryNames`.
REGISTRY = re.compile(r"^[A-Z][A-Za-z0-9]*Names$")

_STRUCT_FILE: dict[str, Path] = {}


def struct_file(struct: str) -> Path:
    """The kernel source file defining `struct`.

    Resolved by scanning rather than from the field name, because the field
    name is only the module name BY CONVENTION -- and a convention the
    generator depends on silently is the same failure mode this script exists
    to prevent. Ambiguity and absence are both hard errors.
    """
    if struct in _STRUCT_FILE:
        return _STRUCT_FILE[struct]
    needle = f"pub struct {struct} {{"
    hits = [p for p in sorted(KERNEL_SRC.rglob("*.rs")) if needle in p.read_text(encoding="utf-8")]
    if not hits:
        raise SystemExit(
            f"error: no `{needle}` anywhere under {KERNEL_SRC} -- "
            "a prelude field names a type this generator cannot resolve"
        )
    if len(hits) > 1:
        where = ", ".join(str(p.relative_to(ROOT)) for p in hits)
        raise SystemExit(f"error: `{needle}` defined in {len(hits)} files ({where})")
    _STRUCT_FILE[struct] = hits[0]
    return hits[0]


def struct_fields(struct: str, path: Path) -> list[tuple[str, str]]:
    """The `pub name: Type` fields of `struct`, in declaration order."""
    text = path.read_text(encoding="utf-8")
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


def collect(
    struct: str, path: Path, prefix: str, expr: str, seen: tuple[str, ...] = ()
) -> tuple[list[tuple[str, str]], list[tuple[str, str]], list[tuple[str, str]]]:
    """`(scalars, lists, sub-packages)` for `struct`, registries flattened.

    Each entry is `(python field name, rust accessor expression)`. A registry
    field contributes its own fields under a dotted name; a `*Prelude` field is
    a sub-package and is NOT flattened (it is wrapped as its own Python object).

    Every other field type raises: see the module docstring. A registry inside
    a registry would work, and a cycle is refused rather than recursed.
    """
    if struct in seen:
        raise SystemExit(f"error: registry cycle through `{struct}` ({' -> '.join(seen)})")
    scalars: list[tuple[str, str]] = []
    lists: list[tuple[str, str]] = []
    nested: list[tuple[str, str]] = []
    for name, ty in struct_fields(struct, path):
        dotted = f"{prefix}{name}"
        access = f"{expr}.{name}"
        if ty == "NameId":
            scalars.append((dotted, access))
        elif ty == "Vec<NameId>":
            lists.append((dotted, access))
        elif ty.endswith("Prelude"):
            if prefix:
                raise SystemExit(
                    f"error: {struct}.{name} is a `{ty}` sub-package inside a registry; "
                    "the Python binding wraps sub-packages only at the top level"
                )
            nested.append((dotted, ty))
        elif REGISTRY.match(ty):
            sub_scalars, sub_lists, sub_nested = collect(
                ty, struct_file(ty), f"{dotted}.", access, (*seen, struct)
            )
            scalars += sub_scalars
            lists += sub_lists
            nested += sub_nested
        else:
            raise SystemExit(
                f"error: {struct}.{name} has type `{ty}`, which this generator does not "
                "classify. Teach it the new shape -- do NOT let it be skipped: a skipped "
                "field vanishes from the Python surface and reads as a missing theorem "
                "(ADR-1512, 8dd580a1c)."
            )
    return scalars, lists, nested


def render() -> tuple[str, dict[str, int], dict[str, tuple[int, int]]]:
    counts: dict[str, int] = {}
    split: dict[str, tuple[int, int]] = {}
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
        "    ArithPrelude, CPointPrelude, CRealPrelude, ComplexPrelude, IntPrelude, ListPrelude,",
        "    LogicPrelude, NameId, NatPrelude, RatPrelude, StringPrelude,",
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
        scalars, lists, nested = collect(struct, KERNEL_SRC / filename, "", "p")
        registry = sum(1 for name, _ in scalars if "." in name)
        counts[kind] = len(scalars)
        split[kind] = (len(scalars) - registry, registry)
        out.append(f"/// The `{struct}` field table ({len(scalars)} names,")
        out.append(f"/// {len(lists)} name lists, {len(nested)} sub-packages).")
        if registry:
            out.append("///")
            out.append(
                f"/// {registry} of the names come from ADR-1512 per-module registries and"
            )
            out.append("/// carry a dotted field name (`pi.pi_le_four`); the rest are flat")
            out.append(f"/// fields on `{struct}` itself.")
        out.append("#[must_use]")
        out.append(
            "#[allow(clippy::too_many_lines)] // a generated field table; length is the point."
        )
        out.append(f"pub(super) fn {kind}(p: &{struct}) -> Fields {{")
        out.append("    Fields {")
        out.append("        names: vec![")
        for name, access in scalars:
            out.append(f'            ("{name}", {access}),')
        out.append("        ],")
        if lists:
            out.append("        lists: vec![")
            for name, access in lists:
                out.append(f'            ("{name}", {access}.clone()),')
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
    return "\n".join(out), counts, split


RUSTFMT_MISSING = False


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
        global RUSTFMT_MISSING  # noqa: PLW0603 -- one process-wide capability fact
        RUSTFMT_MISSING = True
        print("PRELUDE-FIELDS|WARN rustfmt not on PATH -- emitting unformatted")
        return text
    finally:
        scratch.unlink(missing_ok=True)


def main() -> int:
    text, counts, split = render()
    text = rustfmt(text)
    total = sum(counts.values())
    summary = ", ".join(f"{k}={v}" for k, v in counts.items())
    print(f"PRELUDE-FIELDS|total={total}|{summary}")
    # The flat/registry split per package. Printed unconditionally because the
    # ADR-1512 shrink was invisible in the totals alone: `creal=537` and
    # `creal=606` are both plausible-looking numbers, and only the second
    # component says whether the registries were read at all.
    registry_total = sum(r for _, r in split.values())
    detail = ", ".join(f"{k}={f}+{r}" for k, (f, r) in split.items() if r)
    print(f"PRELUDE-FIELDS|registry={registry_total}|{detail or 'none'}")
    if total == 0:
        print("PRELUDE-FIELDS|FAIL parsed zero fields")
        return 1
    if "--check" in sys.argv:
        if RUSTFMT_MISSING:
            # UNANSWERABLE, not stale. The committed file is `rustfmt`'s fixed
            # point, so without `rustfmt` the comparison is against a different
            # text and every tree reads as drifted. Exit 2 -- the repository's
            # code for "no subject / cannot answer", as
            # `recount-pinned-inventory.py` uses it -- so a gate can report the
            # missing toolchain instead of a red that means nothing. Measured
            # 2026-08-16, `just` and `lean` existed on one fleet host of five;
            # a host-capability assumption in a gate is not a safe one.
            print(
                "PRELUDE-FIELDS|SKIP rustfmt not on PATH -- cannot compare "
                "against the formatted fixed point"
            )
            return 2
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

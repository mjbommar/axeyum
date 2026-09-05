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

## Path-qualified registry fields (ADR-1613's "unrelated live gap")

A registry field is sometimes written qualified -- `pub poly: poly::PolyNames`
on `ComplexPrelude` -- typically because the bare name collides with another
struct of the same name elsewhere in the crate (`PolyNames` is ALSO defined in
`nat_prelude/polynomial_setoid.rs`). The field regex used to exclude `:`
entirely, so a qualified type didn't match the field pattern AT ALL: the line
was invisible before classification ever ran, which is the same silent-skip
failure class as (2) above, just one step earlier. Measured 2026-09-04:
`ComplexPrelude.poly` was dropped and the generator printed a plausible
`complex=<N>` with no complaint.

The fix is not "match `:` too and then do a global name search" -- a global
search is exactly the ambiguity that made the field qualified in the first
place. Instead, `resolve_qualified_type` walks the ACTUAL `mod`/`use`
declarations starting from the file that declares the field, exactly as
rustc's own path resolution would: `poly::PolyNames` in `complex.rs` follows
`complex.rs`'s own `pub(crate) mod poly;` to `complex/poly.rs`, never touching
`nat_prelude/polynomial_setoid.rs`'s same-named struct. `crate::SigmaNames`
(an absolute path) starts at the crate root (`lib.rs`) and follows its
`pub use sigma_prelude::SigmaNames;` re-export to `sigma_prelude.rs`. Neither
resolution guesses from the type's spelling; both fail loudly, naming the
field, if a `mod`/`use` step can't be found.
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

# `:` is included so a PATH-QUALIFIED type (`poly::PolyNames`) still matches
# the field pattern -- see the module doc's "path-qualified registry fields"
# section. Excluding `:` was the original defect: the line didn't reach
# classification at all, so it couldn't even hit the "unclassified type" hard
# error below.
FIELD = re.compile(r"^\s{4}pub ([a-z_][a-z_0-9]*): ([A-Za-z0-9_:<>, ]+),\s*$")
# ADR-1512's per-module registries. The naming rule is
# `scripts/creal-migrate-registry.py::struct_name`: the module name in
# CamelCase plus `Names`, so `creal/ivt_boundary.rs` owns `IvtBoundaryNames`.
# Matched against the type's LAST `::`-segment, so `poly::PolyNames` and
# `crate::SigmaNames` both match on `PolyNames`/`SigmaNames`.
REGISTRY = re.compile(r"^[A-Z][A-Za-z0-9]*Names$")

MOD_DECL = re.compile(r"^\s*(?:pub(?:\([^)]*\))?\s+)?mod\s+([a-z_][a-z0-9_]*)\s*;\s*$", re.MULTILINE)
# `use path::to::Type;`, `pub use path::to::Type;`, and the `{...}` group form
# `use path::to::{A, B as C};`. Deliberately does not try to look inside
# doc comments or handle `use self::...`/glob imports -- neither shape occurs
# in the field types this generator has ever had to resolve, and a shape it
# can't recognise is refused loudly (below), never guessed at.
USE_STMT = re.compile(
    r"(?:pub(?:\([^)]*\))?\s+)?use\s+((?:[A-Za-z_][A-Za-z0-9_]*::)*)(\{[^{}]*\}|[A-Za-z_][A-Za-z0-9_]*)(?:\s+as\s+([A-Za-z_][A-Za-z0-9_]*))?\s*;",
    re.MULTILINE,
)

_STRUCT_FILE: dict[str, Path] = {}


def display_path(path: Path) -> str:
    """`path` relative to `ROOT` when it is under it, else the path as-is.

    Error messages are read by a person, so trim the common case; but
    `KERNEL_SRC` is a module-level variable a test can point elsewhere (a
    scratch fixture, not under `ROOT`), and `Path.relative_to` raises rather
    than falling back -- this must not crash instead of reporting the error
    it was building.
    """
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


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
        where = ", ".join(display_path(p) for p in hits)
        raise SystemExit(f"error: `{needle}` defined in {len(hits)} files ({where})")
    _STRUCT_FILE[struct] = hits[0]
    return hits[0]


def submodule_dir(file: Path) -> Path:
    """The directory holding `file`'s child modules.

    The crate root (`lib.rs`) and a directory module (`mod.rs`) declare their
    children in their OWN directory; every other file `foo.rs` declares its
    children in the sibling directory `foo/` (Rust 2018+ module layout).
    """
    if file.name in ("lib.rs", "main.rs", "mod.rs"):
        return file.parent
    return file.parent / file.stem


def parent_module_file(file: Path) -> Path:
    """The file defining the module that declares `file` as a child."""
    directory = file.parent if file.name != "mod.rs" else file.parent.parent
    if directory == KERNEL_SRC:
        return KERNEL_SRC / "lib.rs"
    candidates = [directory.parent / f"{directory.name}.rs", directory / "mod.rs"]
    hits = [c for c in candidates if c.exists() and c != file]
    if len(hits) != 1:
        raise SystemExit(
            f"error: cannot resolve the parent module of {file} -- looked for "
            f"{candidates[0]} and {candidates[1]}"
        )
    return hits[0]


def resolve_child_module(file: Path, name: str) -> Path:
    """The file defining child module `name`, declared by `mod {name};` in `file`."""
    text = file.read_text(encoding="utf-8")
    if not any(m.group(1) == name for m in MOD_DECL.finditer(text)):
        raise SystemExit(f"error: no `mod {name};` declaration in {file}")
    directory = submodule_dir(file)
    candidates = [directory / f"{name}.rs", directory / name / "mod.rs"]
    hits = [c for c in candidates if c.exists()]
    if not hits:
        raise SystemExit(
            f"error: `mod {name};` is declared in {file} but neither "
            f"{candidates[0]} nor {candidates[1]} exists"
        )
    if len(hits) > 1:
        raise SystemExit(
            f"error: `mod {name};` is declared in {file} and BOTH "
            f"{candidates[0]} and {candidates[1]} exist -- ambiguous"
        )
    return hits[0]


def resolve_module_path(segments: list[str], start_file: Path) -> Path:
    """Walk `segments` (a `::`-path with the trailing item name removed) as
    Rust module components starting at `start_file`, returning the file the
    last segment's module resolves to. `segments` may be empty, in which case
    `start_file` itself is returned.

    `crate` jumps to the crate root; `self` is a no-op; `super` moves to the
    enclosing module; anything else is resolved as a declared child module.
    Every step is read from an actual `mod` declaration -- never guessed from
    the segment's spelling.
    """
    file = start_file
    for index, segment in enumerate(segments):
        if segment == "crate":
            if index != 0:
                raise SystemExit(f"error: `crate` may only lead a path (got `{'::'.join(segments)}`)")
            file = KERNEL_SRC / "lib.rs"
        elif segment == "self":
            continue
        elif segment == "super":
            file = parent_module_file(file)
        else:
            file = resolve_child_module(file, segment)
    return file


def use_targets(text: str) -> list[tuple[str, str, str]]:
    """`(visible name, module-path segments joined by '::', original name)`
    for every `use`/`pub use` item in `text`, including `{...}` groups and
    `as`-aliases (the visible name is the alias when one is given).
    """
    out: list[tuple[str, str, str]] = []
    for match in USE_STMT.finditer(text):
        base = match.group(1)[:-2] if match.group(1) else ""  # drop trailing `::`
        tail, alias = match.group(2), match.group(3)
        if tail.startswith("{"):
            for item in tail[1:-1].split(","):
                item = item.strip()
                if not item:
                    continue
                if " as " in item:
                    orig, _, item_alias = item.partition(" as ")
                    out.append((item_alias.strip(), base, orig.strip()))
                else:
                    out.append((item, base, item))
        elif alias:
            out.append((alias, base, tail))
        else:
            out.append((tail, base, tail))
    return out


def resolve_struct_in_file(type_name: str, file: Path, visited: tuple[Path, ...] = ()) -> Path:
    """The file actually defining `pub struct {type_name}`, starting the
    search at `file` and following one `use`/`pub use` re-export if `file`
    doesn't define it directly.
    """
    if file in visited:
        chain = " -> ".join(str(p) for p in (*visited, file))
        raise SystemExit(f"error: `use` cycle resolving `{type_name}` through {chain}")
    text = file.read_text(encoding="utf-8")
    if f"pub struct {type_name} {{" in text:
        return file
    target: tuple[str, str] | None = None
    for visible, base, orig in use_targets(text):
        if visible == type_name:
            target = (base, orig)
            break
    if target is None:
        raise SystemExit(
            f"error: `{type_name}` is neither defined in {file} nor brought into "
            f"scope there by a `use` -- cannot resolve the qualified field type"
        )
    base, orig = target
    mod_segments = base.split("::") if base else []
    next_file = resolve_module_path(mod_segments, file)
    return resolve_struct_in_file(orig, next_file, (*visited, file))


def resolve_qualified_type(ty: str, from_file: Path) -> Path:
    """The `.rs` file defining the struct a `::`-qualified field type (e.g.
    `poly::PolyNames`, `crate::SigmaNames`) refers to, resolved by walking the
    real `mod`/`use` declarations starting at `from_file` -- the file that
    declares the field. Never a bare-name search: that is ambiguous exactly
    when a type is written qualified in the first place (`PolyNames` is
    defined in both `complex/poly.rs` and `nat_prelude/polynomial_setoid.rs`).
    """
    segments = ty.split("::")
    type_name = segments[-1]
    mod_file = resolve_module_path(segments[:-1], from_file)
    return resolve_struct_in_file(type_name, mod_file)


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
        # Classification (NameId / Vec<NameId> / *Prelude / *Names) always
        # goes by the type's LAST `::`-segment: `poly::PolyNames` classifies
        # exactly like bare `PolyNames`. What differs is how its defining
        # file is found -- see the module doc.
        bare_ty = ty.rsplit("::", 1)[-1]
        if ty == "NameId":
            scalars.append((dotted, access))
        elif ty == "Vec<NameId>":
            lists.append((dotted, access))
        elif bare_ty.endswith("Prelude"):
            if prefix:
                raise SystemExit(
                    f"error: {struct}.{name} is a `{ty}` sub-package inside a registry; "
                    "the Python binding wraps sub-packages only at the top level"
                )
            nested.append((dotted, bare_ty))
        elif REGISTRY.match(bare_ty):
            if "::" in ty:
                try:
                    sub_file = resolve_qualified_type(ty, path)
                except SystemExit as exc:
                    raise SystemExit(f"error: {struct}.{name} (`{ty}`): {exc.code}") from None
            else:
                sub_file = struct_file(bare_ty)
            sub_scalars, sub_lists, sub_nested = collect(
                bare_ty, sub_file, f"{dotted}.", access, (*seen, struct)
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

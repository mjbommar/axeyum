#!/usr/bin/env python3
"""ADR-1512 migration: move a self-contained `creal/` module's names out of
`CRealPrelude` into a per-module registry behind the facade.

Mechanical, and it reads its field list from the DEPENDENCY GRAPH rather than
from a literal: `artifacts/refactor/creal-declare-deps.json` says which fields
each step provides, so a module that grew a declaration since the last run
migrates all of it.

    python3 scripts/creal-migrate-registry.py --list
    python3 scripts/creal-migrate-registry.py <module> [<module> ...]

`--list` answers WHICH modules can move, and it is not the same question the
build-order graph answers. ADR-1512's table said fifteen modules were fully
self-contained; it was measured over `creal.rs` plus `creal/*.rs` alone, so it
could not see `complex.rs` reading `creal.sqrt` (19 sites) -- `sqrt`, its
largest entry at 17 fields, is NOT a local move. `--list` scans the whole crate
and its examples.

It has the opposite failure too, and the honest thing is to say so: the scan is
by NAME, not by receiver TYPE, so `RatPrelude::poly_eval` in `rat_prelude/`
reads as an external use of `CRealPrelude::poly_eval`. A module `--list` calls
blocked may still be movable; a module it calls movable really is, because a
false positive can only ever exclude. Check a blocked module's reported sites
before believing them.

Rerun `scripts/creal-declare-deps.py` afterwards: the generated `STEPS` table
addresses migrated fields as `p.<module>.<field>` and is stale until it is.
"""
from __future__ import annotations

import importlib.util
import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
CRATE = ROOT / "crates" / "axeyum-lean-kernel"
SRC = CRATE / "src"
CREAL = SRC / "creal.rs"
CREAL_DIR = SRC / "creal"
LIB = SRC / "lib.rs"
ARTIFACT = ROOT / "artifacts" / "refactor" / "creal-declare-deps.json"


def struct_name(module: str) -> str:
    return "".join(p.capitalize() for p in module.split("_")) + "Names"


def fields_of(module: str) -> list[str]:
    doc = json.load(open(ARTIFACT))
    out = []
    for step in doc["steps"]:
        if step.get("module") == module:
            out += [f for f in step.get("measured_provides", []) if "." not in f]
    # Declaration order within the module, as the struct has them: sort by the
    # position of the field in `CRealPrelude` so the registry reads the same.
    text = CREAL.read_text()
    return sorted(set(out), key=lambda f: text.index(f"    pub {f}: NameId,"))


def cut_spans(text: str, spans: dict[str, tuple[int, int]]) -> tuple[str, dict[str, str], int]:
    """Cut every span, LAST first so the earlier offsets stay valid, and return
    the smallest start -- which is where the facade field replaces them.

    Cutting in field order instead is the obvious way and it is wrong: the
    second cut's offsets are measured against a string the first cut already
    shortened, so `min` over them can name a position inside the wrong entry.
    """
    taken = {f: text[a:b] for f, (a, b) in spans.items()}
    for field in sorted(spans, key=lambda f: -spans[f][0]):
        a, b = spans[field]
        text = text[:a] + text[b:]
    return text, taken, min(a for a, _ in spans.values())


def take_struct_fields(text: str, fields: list[str]) -> tuple[str, dict[str, str], int]:
    """Cut each field's `pub <f>: NameId,` line and the `///` block above it."""
    spans: dict[str, tuple[int, int]] = {}
    for field in fields:
        needle = f"    pub {field}: NameId,\n"
        at = text.index(needle)
        end = at + len(needle)
        start = text.rindex("\n", 0, at) + 1
        while start > 0:
            prev = text.rindex("\n", 0, start - 1) + 1
            if not text[prev:start].startswith("    ///"):
                break
            start = prev
        spans[field] = (start, end)
    return cut_spans(text, spans)


ENTRY = re.compile(r"^        ([a-z_][a-z_0-9]*): ", re.M)


def take_intern_entries(text: str, fields: list[str]) -> tuple[str, dict[str, str], int]:
    """Cut each `<f>: kernel.name_str(creal, "..."),` entry from `intern_names`.

    Entries wrap across lines when rustfmt says so, so the end is found by
    depth-tracking to the entry's own trailing comma rather than by line.
    """
    spans: dict[str, tuple[int, int]] = {}
    for field in fields:
        m = re.search(rf"^        {re.escape(field)}: ", text, re.M)
        if m is None:
            sys.exit(f"migrate: no intern_names entry for `{field}`")
        i, depth = m.end(), 0
        while i < len(text):
            c = text[i]
            if c in "([{":
                depth += 1
            elif c in ")]}":
                depth -= 1
            elif c == "," and depth == 0:
                break
            i += 1
        spans[field] = (m.start(), text.index("\n", i) + 1)
    return cut_spans(text, spans)


def kernel_name(entry: str) -> str:
    m = re.search(r'name_str\(\s*creal,\s*"([^"]+)"\s*\)', entry)
    if m is None:
        sys.exit(f"migrate: cannot read the kernel spelling out of: {entry!r}")
    return m.group(1)


def drop_orphan_banners(text: str) -> str:
    """A `// --- <group> ---` banner whose whole group just moved out."""
    lines = text.split("\n")
    out = []
    for i, line in enumerate(lines):
        if line.startswith("    // --- "):
            j = i + 1
            while j < len(lines) and not lines[j].strip():
                j += 1
            if j < len(lines) and (
                lines[j].startswith("    // --- ") or lines[j].startswith("}")
            ):
                continue
        out.append(line)
    return "\n".join(out)


def rewrite_accessors(module: str, fields: list[str]) -> int:
    """`p.<f>` -> `p.<module>.<f>`, and `CRealPrelude::<f>` -> `<Struct>::<f>`.

    Only over files that hold a `CRealPrelude`: `creal.rs`, `creal/**`, and the
    examples that read the prelude directly. A crate-wide sweep would rewrite
    `RatPrelude::poly_eval` and friends, which are different fields that happen
    to share a name.
    """
    name = struct_name(module)
    paths = [CREAL] + sorted(CREAL_DIR.rglob("*.rs")) + sorted((CRATE / "examples").rglob("*.rs"))
    acc = re.compile(r"(?<![A-Za-z0-9_])p\.(" + "|".join(map(re.escape, fields)) + r")(?![A-Za-z0-9_])")
    link = re.compile(r"CRealPrelude::(" + "|".join(map(re.escape, fields)) + r")(?![A-Za-z0-9_])")
    changed = 0
    for path in paths:
        text = path.read_text()
        new = acc.sub(rf"p.{module}.\1", text)
        new = link.sub(rf"{name}::\1", new)
        if new != text:
            changed += 1
            path.write_text(new)
    return changed


def migrate(module: str) -> None:
    name = struct_name(module)
    fields = fields_of(module)
    if not fields:
        sys.exit(f"migrate: {module} provides no CRealPrelude field")

    text = CREAL.read_text()
    text, docs, struct_at = take_struct_fields(text, fields)
    text, entries, intern_at = take_intern_entries(text, fields)

    plural = "name" if len(fields) == 1 else f"{len(fields)} names"
    facade = (
        f"    /// `creal/{module}.rs`'s own {plural}, moved out of this struct by\n"
        f"    /// ADR-1512 so that adding a declaration to that module touches\n"
        f"    /// that module alone.\n"
        f"    ///\n"
        f"    /// Reached as `p.{module}.{fields[0]}` and documented in\n"
        f"    /// [`{name}`] rather than here. No other `creal` module reads\n"
        f"    /// these names, which is what makes the move local rather than a\n"
        f"    /// cross-module rename (`scripts/creal-declare-deps.py`).\n"
        f"    pub {module}: {name},\n"
    )
    text = text[:struct_at] + facade + text[struct_at:]
    shift = len(facade)
    intern_at += shift
    text = (
        text[:intern_at]
        + f"        {module}: {module}::{name}::intern(kernel, creal),\n"
        + text[intern_at:]
    )
    text = drop_orphan_banners(text)

    anchor = "pub use ivt_boundary::IvtBoundaryNames;\n"
    text = text.replace(anchor, anchor + f"pub use {module}::{name};\n", 1)
    CREAL.write_text(text)

    # The registry, appended to the module that owns it.
    body = [
        f"/// The kernel names `creal/{module}.rs` declares.",
        "///",
        f"/// One of ADR-1512's per-module registries behind the [`CRealPrelude`]",
        "/// facade: the field, its documentation and its interning all live",
        "/// beside the `declare_*` that uses them, so a declaration added here",
        "/// does not touch `creal.rs` at all.",
        "#[derive(Clone, Copy, Debug, PartialEq, Eq)]",
        f"pub struct {name} {{",
    ]
    for field in fields:
        doc = docs[field]
        doc = doc.replace("[`Self::", "[`super::CRealPrelude::")
        body.append(doc.rstrip("\n"))
    body.append("}")
    body.append("")
    body.append(f"impl {name} {{")
    body.append("    /// Interns this module's names under the `CReal` root.")
    body.append("    ///")
    body.append("    /// Split out of `creal.rs`'s `intern_names` by ADR-1512: the kernel")
    body.append("    /// spelling of each name sits in the file that declares it.")
    body.append("    pub(super) fn intern(kernel: &mut Kernel, creal: NameId) -> Self {")
    body.append("        Self {")
    for field in fields:
        body.append(f'            {field}: kernel.name_str(creal, "{kernel_name(entries[field])}"),')
    body.append("        }")
    body.append("    }")
    body.append("}")
    body.append("")

    target = CREAL_DIR / f"{module}.rs"
    module_text = target.read_text()
    # `intern` needs `Kernel` and `NameId`; most of these modules import
    # neither, because until now nothing in them named a `NameId` type.
    uses = list(re.finditer(r"^use .*;\n", module_text, re.M))
    missing = [
        line
        for line in ("use crate::Kernel;\n", "use crate::name::NameId;\n")
        if line not in module_text
    ]
    if missing:
        at = uses[-1].end() if uses else 0
        module_text = module_text[:at] + "".join(missing) + module_text[at:]
    target.write_text(module_text.rstrip("\n") + "\n\n" + "\n".join(body))

    touched = rewrite_accessors(module, fields)

    # `pub` field, publicly nameable type: the same re-export `IvtBoundaryNames`
    # needs, or `private_interfaces` fires.
    lib = LIB.read_text()
    lib = lib.replace(
        "pub use creal::{CRealPrelude, IvtBoundaryNames",
        f"pub use creal::{{CRealPrelude, IvtBoundaryNames, {name}",
        1,
    )
    LIB.write_text(lib)

    print(f"{module}: {len(fields)} fields -> {name}, {touched} file(s) rewritten")


def repoint_doc_links() -> int:
    """`Self::<f>` / `CRealPrelude::<f>` -> `<Registry>::<f>`, for every field
    already in a registry.

    Run ONCE, after every migration in the batch, never inside `migrate`. A
    field's doc block travels with the field, so a link written in module A's
    doc to a field owned by module B moves into A's registry only when A is
    migrated -- which may be after B's own rewrite has already run and can no
    longer see it. Eleven links broke exactly this way on the first pass.

    `Self` is rewritten only in `creal.rs`, where it means `CRealPrelude`. In a
    module file it means that module's own registry and is already right.
    """
    registry = {}
    for field in json.load(open(ARTIFACT))["field_names"]:
        if "." in field:
            module, leaf = field.split(".", 1)
            registry[leaf] = struct_name(module)
    if not registry:
        return 0
    alt = "|".join(sorted(map(re.escape, registry), key=len, reverse=True))
    link = re.compile(r"CRealPrelude::(" + alt + r")(?![A-Za-z0-9_])")
    own = re.compile(r"(?<![A-Za-z0-9_:])Self::(" + alt + r")(?![A-Za-z0-9_])")
    changed = 0
    for path in [CREAL] + sorted(CREAL_DIR.rglob("*.rs")) + sorted(
        (CRATE / "examples").rglob("*.rs")
    ):
        text = path.read_text()
        new = link.sub(lambda m: f"{registry[m.group(1)]}::{m.group(1)}", text)
        if path == CREAL:
            new = own.sub(lambda m: f"{registry[m.group(1)]}::{m.group(1)}", new)
        if new != text:
            path.write_text(new)
            changed += 1
    return changed


def report_candidates() -> None:
    """Which modules own names nothing outside them reads. See the module docs
    for what this scan can and cannot see."""
    spec = importlib.util.spec_from_file_location(
        "cdd", str(pathlib.Path(__file__).with_name("creal-declare-deps.py"))
    )
    cdd = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(cdd)

    doc = json.load(open(ARTIFACT))
    owner: dict[str, str] = {}
    for step in doc["steps"]:
        for f in step.get("measured_provides", []):
            owner[f] = step.get("module", "creal")
    by_module: dict[str, list[str]] = {}
    for f, m in owner.items():
        if m != "creal" and "." not in f:
            by_module.setdefault(m, []).append(f)

    accessor = re.compile(
        r"(?<![A-Za-z0-9_])([a-z_][a-z_0-9]*)\.([a-z_][a-z_0-9]*)(?![A-Za-z0-9_(])"
    )
    seen: dict[str, dict[str, int]] = {}
    for path in sorted(SRC.rglob("*.rs")) + sorted((CRATE / "examples").rglob("*.rs")):
        if path.name == "steps_generated.rs":
            continue
        rel = str(path.relative_to(CRATE))
        if path == CREAL:
            where = "creal"
        elif path.parent == CREAL_DIR:
            where = path.stem
        elif "creal/inventory/" in rel:
            # A shard names every one of its module's fields once, and it moves
            # WITH the module. Counting it makes every module look blocked.
            where = "INVENTORY"
        else:
            where = rel
        for m in accessor.finditer(cdd.strip_noise(path.read_text())):
            seen.setdefault(m.group(2), {})
            seen[m.group(2)][where] = seen[m.group(2)].get(where, 0) + 1

    movable, blocked = [], []
    for module, fields in sorted(by_module.items(), key=lambda kv: -len(kv[1])):
        external: dict[str, int] = {}
        for f in fields:
            for w, n in seen.get(f, {}).items():
                if w in (module, "creal", "INVENTORY") or w.endswith(("_tests", "_tests.rs")):
                    continue
                external[w] = external.get(w, 0) + n
        (movable if not external else blocked).append((module, len(fields), external))

    print(f"movable: {len(movable)} module(s), {sum(n for _, n, _ in movable)} field(s)")
    for module, n, _ in movable:
        print(f"  {module:22s} {n:3d}")
    print(f"\nblocked: {len(blocked)} module(s) -- verify the sites before believing them")
    for module, n, ext in blocked:
        top = ", ".join(f"{w}:{c}" for w, c in sorted(ext.items(), key=lambda kv: -kv[1])[:3])
        print(f"  {module:22s} {n:3d} fields, external {sum(ext.values()):4d} -> {top}")


if __name__ == "__main__":
    args = sys.argv[1:]
    if not args:
        sys.exit(__doc__)
    if args == ["--list"]:
        report_candidates()
        raise SystemExit(0)

    for module in args:
        migrate(module)
    print(f"doc links repointed in {repoint_doc_links()} file(s)")

    files = [CREAL, LIB] + [CREAL_DIR / f"{m}.rs" for m in args]
    subprocess.run(["rustfmt", "--edition", "2024", *map(str, files)], check=True)
    print(
        "now run `python3 scripts/creal-declare-deps.py` -- the generated STEPS "
        "table addresses these fields by their new path and is stale until you do"
    )

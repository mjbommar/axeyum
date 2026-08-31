#!/usr/bin/env python3
"""Validate and generate from declaration-spec files (L3 phase D1, ADR-0965).

A declaration-spec file (`artifacts/declaration-spec/*.json`, schema in
`schema.json`) describes a small subsystem of pure `Definition` kernel
declarations via a typed expression DSL. This script is the "generator"
half of the pilot:

  - validates every spec against four guards that must fire BEFORE any
    kernel construction is attempted: duplicate name within the spec
    corpus, duplicate name against the real kernel's full name inventory
    (the cross-prelude case), missing/invalid build phase, and a
    dependency cycle among the spec's own declarations. A fifth guard
    checks that the declared `dependencies` list agrees with the
    `const_ref` nodes actually present in the recipe (no drift between
    declared and used dependencies);
  - on success, emits generated Python types, a generated Rust
    name/equation constant table (compiled into
    `examples/declaration_spec_pilot.rs` via `include!`, so it is not
    decorative), and a generated inventory JSON row set.

Every guard failure is tagged `GUARD:<NAME>` so a grep-based check (and
mutation testing) can address it precisely. Exit code depends on the
finding: 0 only if the whole validated corpus is clean; 1 on any
violation, including an empty corpus (fail on absence, not just on error).
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_SPECS_DIR = REPO_ROOT / "artifacts" / "declaration-spec"
DEFAULT_GENERATED_DIR = DEFAULT_SPECS_DIR / "generated"
DEFAULT_SNAPSHOT = DEFAULT_GENERATED_DIR / "kernel-names-snapshot.txt"

SUPPORTED_SPEC_VERSION = 1
SUPPORTED_KINDS = {"Definition"}


@dataclass
class Violation:
    guard: str
    detail: str

    def __str__(self) -> str:
        return f"GUARD:{self.guard} {self.detail}"


def fq_name(namespace: str, local_name: str) -> str:
    return f"{namespace}.{local_name}" if namespace else local_name


def load_spec(path: Path) -> dict:
    with path.open("r", encoding="utf-8") as fh:
        return json.load(fh)


def walk_expr_const_refs(node) -> list[str]:
    """Recursively collect every `const_ref` name reachable from `node`."""
    found: list[str] = []

    def _walk(n):
        if isinstance(n, dict):
            if n.get("op") == "const_ref" and isinstance(n.get("name"), str):
                found.append(n["name"])
            for v in n.values():
                _walk(v)
        elif isinstance(n, list):
            for item in n:
                _walk(item)

    _walk(node)
    return found


def validate_spec_shape(spec_path: Path, spec: dict) -> list[Violation]:
    violations: list[Violation] = []

    version = spec.get("spec_version")
    if version != SUPPORTED_SPEC_VERSION:
        violations.append(
            Violation(
                "BAD_SPEC_VERSION",
                f"{spec_path}: spec_version={version!r}, expected {SUPPORTED_SPEC_VERSION}",
            )
        )
        return violations  # nothing below is safe to interpret

    decls = spec.get("declarations")
    if not isinstance(decls, list) or not decls:
        violations.append(
            Violation("EMPTY_DECLARATIONS", f"{spec_path}: no declarations")
        )
        return violations

    for i, decl in enumerate(decls):
        where = f"{spec_path}#{i} ({decl.get('local_name', '<unnamed>')})"
        for required in ("local_name", "namespace", "kind", "universe_params", "binders", "type", "value", "dependencies"):
            if required not in decl:
                violations.append(Violation("MISSING_FIELD", f"{where}: missing '{required}'"))
        if "kind" in decl and decl["kind"] not in SUPPORTED_KINDS:
            violations.append(
                Violation(
                    "UNSUPPORTED_KIND",
                    f"{where}: kind={decl['kind']!r} not in {sorted(SUPPORTED_KINDS)} "
                    "(a spec may only describe Definitions -- see ADR-0965)",
                )
            )
        if "phase" not in decl:
            violations.append(Violation("MISSING_PHASE", f"{where}: no 'phase' field"))
        else:
            phase = decl["phase"]
            if not isinstance(phase, int) or isinstance(phase, bool) or phase < 0:
                violations.append(Violation("MISSING_PHASE", f"{where}: phase={phase!r} is not a non-negative integer"))

    return violations


def check_in_corpus_duplicates(specs: list[tuple[Path, dict]]) -> list[Violation]:
    violations: list[Violation] = []
    seen: dict[str, Path] = {}
    for path, spec in specs:
        for decl in spec.get("declarations", []):
            if "local_name" not in decl or "namespace" not in decl:
                continue
            name = fq_name(decl["namespace"], decl["local_name"])
            if name in seen:
                violations.append(
                    Violation(
                        "DUPLICATE_NAME",
                        f"'{name}' declared in both {seen[name]} and {path}",
                    )
                )
            else:
                seen[name] = path
    return violations


def check_cross_prelude_duplicates(specs: list[tuple[Path, dict]], snapshot_path: Path) -> list[Violation]:
    if not snapshot_path.exists():
        return [
            Violation(
                "SNAPSHOT_MISSING",
                f"{snapshot_path} does not exist -- run the Rust example's --dump-names mode first; "
                "cannot check cross-prelude duplicates without the real kernel name inventory",
            )
        ]
    existing = {line.strip() for line in snapshot_path.read_text(encoding="utf-8").splitlines() if line.strip()}
    violations: list[Violation] = []
    for path, spec in specs:
        for decl in spec.get("declarations", []):
            if "local_name" not in decl or "namespace" not in decl:
                continue
            if decl.get("mirrors_existing") is True:
                # Deliberately describes an already-landed subsystem (the D1
                # digest-parity pilot) -- exempt by design, never by default.
                # See nat-squarefree.json's _comment and this field's schema
                # doc: no spec proposing genuinely new work may set this.
                continue
            name = fq_name(decl["namespace"], decl["local_name"])
            if name in existing:
                violations.append(
                    Violation(
                        "CROSS_PRELUDE_DUPLICATE",
                        f"'{name}' in {path} is already declared in the real kernel environment "
                        f"(see {snapshot_path}) -- this is the Nat.inverseIndex collision shape: "
                        "a name check scoped to one prelude's own files cannot see this",
                    )
                )
    return violations


def check_dependency_cycles(specs: list[tuple[Path, dict]]) -> list[Violation]:
    violations: list[Violation] = []
    for path, spec in specs:
        decls = spec.get("declarations", [])
        local_names = {d["local_name"] for d in decls if "local_name" in d}
        edges: dict[str, list[str]] = {}
        for d in decls:
            if "local_name" not in d:
                continue
            deps = d.get("dependencies", [])
            targets = [
                dep["name"]
                for dep in deps
                if isinstance(dep, dict) and dep.get("extern") is False and dep.get("name") in local_names
            ]
            edges[d["local_name"]] = targets

        # standard 3-color DFS cycle detection
        WHITE, GRAY, BLACK = 0, 1, 2
        color = {n: WHITE for n in edges}
        cycle_found: list[str] = []

        def dfs(node: str, stack: list[str]) -> bool:
            color[node] = GRAY
            stack.append(node)
            for nxt in edges.get(node, []):
                if color.get(nxt, WHITE) == GRAY:
                    idx = stack.index(nxt)
                    cycle_found.extend(stack[idx:] + [nxt])
                    return True
                if color.get(nxt, WHITE) == WHITE and dfs(nxt, stack):
                    return True
            stack.pop()
            color[node] = BLACK
            return False

        for n in list(edges.keys()):
            if color[n] == WHITE:
                if dfs(n, []):
                    violations.append(
                        Violation(
                            "DEPENDENCY_CYCLE",
                            f"{path}: cycle among local declarations: {' -> '.join(cycle_found)}",
                        )
                    )
                    break
    return violations


def check_dependency_consistency(specs: list[tuple[Path, dict]]) -> list[Violation]:
    """The declared `dependencies` list must agree with the `const_ref` nodes
    the recipe actually contains, in both directions."""
    violations: list[Violation] = []
    for path, spec in specs:
        for decl in spec.get("declarations", []):
            if "local_name" not in decl:
                continue
            where = f"{path}#{decl['local_name']}"
            declared = {
                dep["name"]
                for dep in decl.get("dependencies", [])
                if isinstance(dep, dict) and "name" in dep
            }
            used = set(walk_expr_const_refs(decl.get("type"))) | set(walk_expr_const_refs(decl.get("value")))
            missing_declared = used - declared
            unused_declared = declared - used
            if missing_declared:
                violations.append(
                    Violation(
                        "DEP_MISMATCH",
                        f"{where}: const_ref to {sorted(missing_declared)} not listed in 'dependencies'",
                    )
                )
            if unused_declared:
                violations.append(
                    Violation(
                        "DEP_MISMATCH",
                        f"{where}: 'dependencies' lists {sorted(unused_declared)}, never referenced via const_ref",
                    )
                )
    return violations


def check_phase_order(specs: list[tuple[Path, dict]]) -> list[Violation]:
    """A non-extern dependency's phase must be <= the depending declaration's
    phase. Complements the cycle check: a cycle can exist even when every
    individual edge looks phase-monotone if checked in only one direction, so
    this is deliberately a separate guard rather than folded into the cycle
    check."""
    violations: list[Violation] = []
    for path, spec in specs:
        decls = spec.get("declarations", [])
        phase_of = {d["local_name"]: d.get("phase") for d in decls if "local_name" in d}
        for d in decls:
            if "local_name" not in d or "phase" not in d:
                continue
            for dep in d.get("dependencies", []):
                if not isinstance(dep, dict) or dep.get("extern") is not False:
                    continue
                dep_name = dep.get("name")
                dep_phase = phase_of.get(dep_name)
                if dep_phase is None:
                    continue  # unresolved local dependency; not this guard's job
                if dep_phase > d["phase"]:
                    violations.append(
                        Violation(
                            "PHASE_ORDER",
                            f"{path}#{d['local_name']}: phase {d['phase']} < dependency "
                            f"'{dep_name}' phase {dep_phase}",
                        )
                    )
    return violations


def gen_python_types(spec: dict, out_dir: Path) -> Path:
    subsystem = spec["subsystem"]
    lines = [
        '"""Generated by scripts/gen-declaration-spec.py -- do not hand-edit.',
        f"Mirrors artifacts/declaration-spec/{subsystem}.json (spec_version="
        f"{spec['spec_version']}). Pure data, no proof content: see ADR-0965.",
        '"""',
        "from __future__ import annotations",
        "from dataclasses import dataclass",
        "",
        "@dataclass(frozen=True)",
        "class DeclarationRow:",
        "    fq_name: str",
        "    kind: str",
        "    phase: int",
        "    dependencies: tuple[str, ...]",
        "",
        f"SUBSYSTEM = {subsystem!r}",
        "DECLARATIONS: tuple[DeclarationRow, ...] = (",
    ]
    for decl in spec["declarations"]:
        name = fq_name(decl["namespace"], decl["local_name"])
        deps = tuple(d["name"] for d in decl.get("dependencies", []))
        lines.append(
            f"    DeclarationRow(fq_name={name!r}, kind={decl['kind']!r}, "
            f"phase={decl['phase']}, dependencies={deps!r}),"
        )
    lines.append(")")
    lines.append("")
    out_path = out_dir / f"{subsystem.replace('-', '_')}_types.py"
    out_path.write_text("\n".join(lines), encoding="utf-8")
    return out_path


def rust_escape(s: str) -> str:
    return s.replace("\\", "\\\\").replace('"', '\\"')


def gen_rust_names_table(spec: dict, out_dir: Path) -> Path:
    subsystem = spec["subsystem"].replace("-", "_")
    lines = [
        "// Generated by scripts/gen-declaration-spec.py -- do not hand-edit.",
        f"// Mirrors artifacts/declaration-spec/{spec['subsystem']}.json "
        f"(spec_version={spec['spec_version']}). Pure registration data: names, kind,",
        "// phase, dependencies, and evaluation equations -- no proof content (ADR-0965).",
        "// `include!`'d directly into examples/declaration_spec_pilot.rs, so this is",
        "// compiled and exercised, not decorative.",
        "",
        "#[allow(dead_code, missing_docs)]",
        "pub struct SpecDeclRow {",
        "    pub namespace: &'static str,",
        "    pub local_name: &'static str,",
        "    pub kind: &'static str,",
        "    pub phase: u32,",
        "}",
        "",
        "#[allow(dead_code, missing_docs)]",
        "pub const SPEC_DECLARATIONS: &[SpecDeclRow] = &[",
    ]
    for decl in spec["declarations"]:
        lines.append(
            # rustfmt breaks this struct literal across lines at the default
            # width, so a single-line form makes `cargo fmt --check` reject the
            # generated file -- and the freshness check then regenerates the
            # unformatted form, undoing any external fixup. Two gates in direct
            # conflict, with the generator losing. Emit the shape rustfmt wants.
            "    SpecDeclRow {\n"
            "        namespace: \"%s\",\n"
            "        local_name: \"%s\",\n"
            "        kind: \"%s\",\n"
            "        phase: %d,\n"
            "    },"
            % (
                rust_escape(decl["namespace"]),
                rust_escape(decl["local_name"]),
                rust_escape(decl["kind"]),
                decl["phase"],
            )
        )
    lines.append("];")
    lines.append("")
    lines.append("#[allow(dead_code, missing_docs)]")
    lines.append("pub struct SpecEquationRow {")
    lines.append("    pub local_name: &'static str,")
    lines.append("    pub args: &'static [i64],")
    lines.append("    pub expect_bool: bool,")
    lines.append("}")
    lines.append("")
    lines.append("#[allow(dead_code, missing_docs)]")
    lines.append("pub const SPEC_EQUATIONS: &[SpecEquationRow] = &[")
    for decl in spec["declarations"]:
        for eq in decl.get("equations", []):
            args_str = ", ".join(str(int(a)) for a in eq["args"])
            expect = eq["expect"]
            if not isinstance(expect, bool):
                continue  # pilot's Rust table only carries the Bool-valued equations
            lines.append(
                "    SpecEquationRow {\n"
                "        local_name: \"%s\",\n"
                "        args: &[%s],\n"
                "        expect_bool: %s,\n"
                "    },"
                % (rust_escape(decl["local_name"]), args_str, "true" if expect else "false")
            )
    lines.append("];")
    lines.append("")
    out_path = out_dir / f"{subsystem}_names.rs"
    out_path.write_text("\n".join(lines), encoding="utf-8")
    return out_path


def gen_inventory(spec: dict, out_dir: Path) -> Path:
    rows = []
    for decl in spec["declarations"]:
        rows.append(
            {
                "fq_name": fq_name(decl["namespace"], decl["local_name"]),
                "kind": decl["kind"],
                "phase": decl["phase"],
                "dependencies": [d["name"] for d in decl.get("dependencies", [])],
                "subsystem": spec["subsystem"],
            }
        )
    out_path = out_dir / f"{spec['subsystem'].replace('-', '_')}_inventory.json"
    out_path.write_text(json.dumps(rows, indent=2) + "\n", encoding="utf-8")
    return out_path


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--specs-dir", type=Path, default=DEFAULT_SPECS_DIR)
    ap.add_argument("--generated-dir", type=Path, default=DEFAULT_GENERATED_DIR)
    ap.add_argument("--snapshot", type=Path, default=DEFAULT_SNAPSHOT)
    ap.add_argument(
        "--only",
        nargs="+",
        type=Path,
        default=None,
        help="Restrict the validated corpus to exactly these spec files (paths).",
    )
    ap.add_argument("--check", action="store_true", help="Validate only; do not write generated artifacts.")
    ap.add_argument(
        "--skip-cross-prelude",
        action="store_true",
        help="Skip the cross-prelude duplicate guard (for offline/no-Rust-build validation only).",
    )
    args = ap.parse_args()

    if args.only is not None:
        spec_paths = list(args.only)
    else:
        spec_paths = sorted(
            p
            for p in args.specs_dir.glob("*.json")
            if p.name != "schema.json"
        )

    if not spec_paths:
        print("GUARD:EMPTY_CORPUS no spec files found -- nothing was checked", file=sys.stderr)
        return 1

    specs: list[tuple[Path, dict]] = []
    violations: list[Violation] = []
    for path in spec_paths:
        try:
            spec = load_spec(path)
        except json.JSONDecodeError as exc:
            violations.append(Violation("PARSE_ERROR", f"{path}: {exc}"))
            continue
        violations.extend(validate_spec_shape(path, spec))
        specs.append((path, spec))

    if specs:
        violations.extend(check_in_corpus_duplicates(specs))
        if not args.skip_cross_prelude:
            violations.extend(check_cross_prelude_duplicates(specs, args.snapshot))
        violations.extend(check_dependency_cycles(specs))
        violations.extend(check_phase_order(specs))
        violations.extend(check_dependency_consistency(specs))

    if violations:
        for v in violations:
            print(str(v))
        print(f"DECLARATION_SPEC_GEN|specs={len(spec_paths)}|violations={len(violations)}|verdict=FAIL")
        return 1

    checked_declarations = sum(len(s.get("declarations", [])) for _, s in specs)
    if checked_declarations == 0:
        print("GUARD:EMPTY_CORPUS specs loaded but zero declarations found", file=sys.stderr)
        return 1

    if not args.check:
        args.generated_dir.mkdir(parents=True, exist_ok=True)
        for path, spec in specs:
            gen_python_types(spec, args.generated_dir)
            gen_rust_names_table(spec, args.generated_dir)
            gen_inventory(spec, args.generated_dir)

    print(
        f"DECLARATION_SPEC_GEN|specs={len(spec_paths)}|declarations={checked_declarations}|"
        f"violations=0|verdict=PASS"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())

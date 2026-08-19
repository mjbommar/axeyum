#!/usr/bin/env python3
"""Measure proposition-facing versus implementation-body Lean dependencies.

This is a syntactic feasibility diagnostic, not a statement importer.  It never
rewrites a goal and grants no proof or ledger credit.  Its purpose is to answer
the narrower question that must precede a checked type slicer: do trusted
declarations occur in the types needed to present a target, or only in
definition bodies that a future slicer may have to abstract?
"""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import sys
from dataclasses import dataclass
from typing import Any


STRUCTURAL = {"in", "il", "ie"}
DECLARATIONS = ("axiom", "def", "opaque", "thm", "quot", "inductive")
TRUSTED = {"axiom", "opaque", "thm", "quot"}


class TypeSliceError(RuntimeError):
    """The input is malformed or violates the sealed diagnostic contract."""


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def canonical_digest(value: Any) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return sha256_bytes(encoded)


@dataclass(frozen=True)
class DeclarationRecord:
    kind: str
    names: tuple[int, ...]
    type_roots: tuple[int, ...]
    value_roots: tuple[int, ...]


@dataclass(frozen=True)
class StreamAnalysis:
    stream_sha256: str
    declarations: int
    implementation_declarations: int
    type_declarations: int
    implementation_trusted: tuple[str, ...]
    type_trusted: tuple[str, ...]
    abstractable_type_boundary: tuple[str, ...]


class ExportGraph:
    def __init__(self) -> None:
        self.names = [""]
        self.expressions: list[frozenset[int]] = []
        self.declarations: list[DeclarationRecord] = []
        self.owner: dict[int, int] = {}
        self.metadata_seen = False

    def add(self, raw: dict[str, Any], line: int) -> None:
        markers = STRUCTURAL.intersection(raw)
        if len(markers) > 1:
            raise TypeSliceError(f"line {line}: multiple structural index spaces")
        if "meta" in raw:
            if line != 1 or self.metadata_seen or set(raw) != {"meta"}:
                raise TypeSliceError(f"line {line}: misplaced metadata")
            self.metadata_seen = True
        elif "in" in raw:
            self._name(raw, line)
        elif "ie" in raw:
            self._expression(raw, line)
        elif "il" in raw:
            # Level topology is independently checked by the Rust importer.  It
            # cannot introduce a declaration dependency, but dense ids are still
            # deliberately left to that authority rather than half-validated.
            return
        else:
            self._declaration(raw, line)

    def _name(self, raw: dict[str, Any], line: int) -> None:
        ident = raw.get("in")
        if ident != len(self.names):
            raise TypeSliceError(
                f"line {line}: expected dense name {len(self.names)}, got {ident!r}"
            )
        if set(raw) == {"in", "str"} and isinstance(raw["str"], dict):
            payload = raw["str"]
            pre, component = payload.get("pre"), payload.get("str")
        elif set(raw) == {"in", "num"} and isinstance(raw["num"], dict):
            payload = raw["num"]
            pre, component = payload.get("pre"), payload.get("i")
            component = str(component) if isinstance(component, int) else None
        else:
            raise TypeSliceError(f"line {line}: malformed name record")
        if not isinstance(pre, int) or not 0 <= pre < len(self.names):
            raise TypeSliceError(f"line {line}: forward or missing name prefix")
        if not isinstance(component, str) or not component:
            raise TypeSliceError(f"line {line}: empty name component")
        self.names.append(component if pre == 0 else f"{self.names[pre]}.{component}")

    def _expr_ref(self, value: Any, line: int) -> int:
        if not isinstance(value, int) or not 0 <= value < len(self.expressions):
            raise TypeSliceError(f"line {line}: forward or missing expression reference")
        return value

    def _name_ref(self, value: Any, line: int) -> int:
        if not isinstance(value, int) or not 0 <= value < len(self.names):
            raise TypeSliceError(f"line {line}: forward or missing name reference")
        return value

    def _expression(self, raw: dict[str, Any], line: int) -> None:
        ident = raw.get("ie")
        if ident != len(self.expressions):
            raise TypeSliceError(
                f"line {line}: expected dense expression {len(self.expressions)}, got {ident!r}"
            )
        kinds = set(raw) - {"ie"}
        if len(kinds) != 1:
            raise TypeSliceError(f"line {line}: expression kind is not unique")
        kind = next(iter(kinds))
        payload = raw[kind]
        dependencies: set[int] = set()
        children: list[Any] = []
        if kind == "const" and isinstance(payload, dict):
            dependencies.add(self._name_ref(payload.get("name"), line))
        elif kind == "app" and isinstance(payload, dict):
            children = [payload.get("fn"), payload.get("arg")]
        elif kind in {"lam", "forallE"} and isinstance(payload, dict):
            children = [payload.get("type"), payload.get("body")]
        elif kind == "letE" and isinstance(payload, dict):
            children = [payload.get("type"), payload.get("value"), payload.get("body")]
        elif kind == "mdata" and isinstance(payload, dict):
            children = [payload.get("expr")]
        elif kind == "proj" and isinstance(payload, dict):
            dependencies.add(self._name_ref(payload.get("typeName"), line))
            children = [payload.get("struct")]
        elif kind not in {"bvar", "sort", "natVal", "strVal"}:
            raise TypeSliceError(f"line {line}: unsupported expression kind {kind!r}")
        for child in children:
            dependencies.update(self.expressions[self._expr_ref(child, line)])
        self.expressions.append(frozenset(dependencies))

    def _root(self, value: Any, line: int) -> int:
        return self._expr_ref(value, line)

    def _declaration(self, raw: dict[str, Any], line: int) -> None:
        kinds = [kind for kind in DECLARATIONS if kind in raw]
        if len(kinds) != 1 or len(raw) != 1:
            raise TypeSliceError(f"line {line}: declaration kind is not unique")
        kind = kinds[0]
        payload = raw[kind]
        if not isinstance(payload, dict):
            raise TypeSliceError(f"line {line}: declaration payload is not an object")
        names: list[int] = []
        types: list[int] = []
        values: list[int] = []
        if kind == "inductive":
            for group in ("types", "ctors", "recs"):
                members = payload.get(group)
                if not isinstance(members, list):
                    raise TypeSliceError(f"line {line}: inductive {group} is not an array")
                for member in members:
                    if not isinstance(member, dict):
                        raise TypeSliceError(f"line {line}: inductive member is not an object")
                    names.append(self._name_ref(member.get("name"), line))
                    types.append(self._root(member.get("type"), line))
                    for rule in member.get("rules", []):
                        if not isinstance(rule, dict):
                            raise TypeSliceError(f"line {line}: recursor rule is not an object")
                        values.append(self._root(rule.get("rhs"), line))
        else:
            names.append(self._name_ref(payload.get("name"), line))
            types.append(self._root(payload.get("type"), line))
            if kind in {"def", "opaque", "thm"}:
                values.append(self._root(payload.get("value"), line))
        index = len(self.declarations)
        for name in names:
            if name in self.owner:
                raise TypeSliceError(f"line {line}: duplicate declaration {self.names[name]!r}")
            self.owner[name] = index
        self.declarations.append(
            DeclarationRecord(kind, tuple(names), tuple(types), tuple(values))
        )

    def closure(self, roots: tuple[int, ...], include_values: bool) -> set[int]:
        selected: set[int] = set()
        pending_names: list[int] = []
        for root in roots:
            pending_names.extend(self.expressions[root])
        while pending_names:
            name = pending_names.pop()
            owner = self.owner.get(name)
            if owner is None or owner in selected:
                continue
            selected.add(owner)
            declaration = self.declarations[owner]
            expression_roots = declaration.type_roots
            if include_values:
                expression_roots += declaration.value_roots
            for root in expression_roots:
                pending_names.extend(self.expressions[root])
        return selected

    def analyze(self, target: str, stream_sha256: str) -> StreamAnalysis:
        if not self.metadata_seen:
            raise TypeSliceError("stream has no metadata")
        target_names = [index for index, name in enumerate(self.names) if name == target]
        if len(target_names) != 1 or target_names[0] not in self.owner:
            raise TypeSliceError(f"target {target!r} does not name exactly one declaration")
        target_owner = self.owner[target_names[0]]
        target_decl = self.declarations[target_owner]
        if target_decl.kind != "def" or len(target_decl.names) != 1:
            raise TypeSliceError(f"target {target!r} is not one definition")
        roots = target_decl.type_roots + target_decl.value_roots
        implementation = self.closure(roots, include_values=True)
        type_slice = self.closure(roots, include_values=False)

        def trusted(indices: set[int]) -> tuple[str, ...]:
            return tuple(
                sorted(
                    self.names[name]
                    for index in indices
                    if self.declarations[index].kind in TRUSTED
                    for name in self.declarations[index].names
                )
            )

        implementation_trusted = trusted(implementation)
        type_trusted = trusted(type_slice)
        abstractable = tuple(
            sorted(
                self.names[name]
                for index in type_slice
                if self.declarations[index].kind == "def"
                for name in self.declarations[index].names
            )
        )
        return StreamAnalysis(
            stream_sha256=stream_sha256,
            declarations=len(self.declarations),
            implementation_declarations=len(implementation),
            type_declarations=len(type_slice),
            implementation_trusted=implementation_trusted,
            type_trusted=type_trusted,
            abstractable_type_boundary=abstractable,
        )


def analyze_stream(path: pathlib.Path, target: str) -> StreamAnalysis:
    data = path.read_bytes()
    graph = ExportGraph()
    for line_number, raw_line in enumerate(data.splitlines(), 1):
        if not raw_line:
            raise TypeSliceError(f"line {line_number}: blank record")
        value = json.loads(raw_line)
        if not isinstance(value, dict):
            raise TypeSliceError(f"line {line_number}: record is not an object")
        graph.add(value, line_number)
    return graph.analyze(target, sha256_bytes(data))


def analyze_archive(root: pathlib.Path, mapping: dict[str, Any]) -> dict[str, Any]:
    authority = mapping.get("authority", {})
    if (
        mapping.get("kind") != "axeyum-autogenesis-reflexivity-coverage-input"
        or mapping.get("state") != "proof-free-source-input"
        or authority.get("held_out_inspected") is not False
        or authority.get("partitions_inspected") != ["development", "train"]
    ):
        raise TypeSliceError("mapping does not preserve the frozen train/development boundary")
    mapped_rows = mapping.get("rows")
    if not isinstance(mapped_rows, list) or len(mapped_rows) != 138:
        raise TypeSliceError("mapping does not contain exactly 138 rows")
    rows = []
    for mapped in mapped_rows:
        if not isinstance(mapped, dict) or mapped.get("partition") not in {"train", "development"}:
            raise TypeSliceError("sealed or malformed row entered the analysis")
        artifact = mapped.get("artifact_file")
        target = mapped.get("target_definition")
        if (
            not isinstance(artifact, str)
            or pathlib.PurePath(artifact).name != artifact
            or not isinstance(target, str)
            or not target
        ):
            raise TypeSliceError("unsafe artifact path or target")
        result = analyze_stream(root / "streams" / artifact, target)
        rows.append(
            {
                "artifact_file": artifact,
                "fact_id": mapped.get("fact_id"),
                "family": mapped.get("family"),
                "partition": mapped.get("partition"),
                "target_definition": target,
                "stream_sha256": result.stream_sha256,
                "declarations": result.declarations,
                "implementation_declarations": result.implementation_declarations,
                "type_declarations": result.type_declarations,
                "implementation_trusted": list(result.implementation_trusted),
                "type_trusted": list(result.type_trusted),
                "abstractable_type_boundary": list(result.abstractable_type_boundary),
            }
        )
    clean = sum(not row["type_trusted"] for row in rows)
    implementation_contaminated = sum(bool(row["implementation_trusted"]) for row in rows)
    output: dict[str, Any] = {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-type-slice-feasibility",
        "state": "syntactic-diagnostic-no-proof-or-ledger-credit",
        "authority": {
            "partitions_inspected": ["development", "train"],
            "held_out_inspected": False,
            "proof_bodies_executed": False,
            "targets": len(rows),
        },
        "mapping_input_sha256": mapping.get("input_sha256"),
        "coverage": {
            "implementation_closure_has_trusted": implementation_contaminated,
            "type_closure_has_no_trusted": clean,
            "type_closure_has_trusted": len(rows) - clean,
        },
        "rows": rows,
        "limitations": (
            "Syntactic declaration reachability is an upper-bound feasibility result. "
            "It neither constructs an abstracted proposition nor checks abstraction types, "
            "definitional equality, a proof, or a ledger transition."
        ),
    }
    output["observation_sha256"] = canonical_digest(output)
    return output


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=pathlib.Path)
    parser.add_argument("mapping", type=pathlib.Path)
    parser.add_argument("--output", type=pathlib.Path)
    args = parser.parse_args()
    try:
        mapping = json.loads(args.mapping.read_text())
        if not isinstance(mapping, dict):
            raise TypeSliceError("mapping is not an object")
        result = analyze_archive(args.archive, mapping)
        rendered = json.dumps(result, indent=2, ensure_ascii=False) + "\n"
        if args.output is None:
            sys.stdout.write(rendered)
        else:
            args.output.write_text(rendered)
        coverage = result["coverage"]
        print(
            "AUTOGENESIS_TYPE_SLICE_FEASIBILITY_OK|"
            f"{result['observation_sha256']}|"
            f"clean={coverage['type_closure_has_no_trusted']}|held_out=0",
            file=sys.stderr,
        )
        return 0
    except (OSError, TypeError, json.JSONDecodeError, TypeSliceError) as error:
        print(f"autogenesis-type-slice-feasibility: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())

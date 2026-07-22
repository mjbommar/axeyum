#!/usr/bin/env python3
"""Fail-closed inventory probe for lean4export NDJSON 3.1.0.

This is research scaffolding, not a trusted kernel reader.  It validates the
stream's elementary topological/index invariants and reports which records the
current Rust kernel cannot yet admit.  Parsing a declaration is deliberately
not reported as checking it.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Iterable


FORMAT_VERSION = "3.1.0"
NAME_KINDS = {"str", "num"}
LEVEL_KINDS = {"succ", "max", "imax", "param"}
EXPR_KINDS = {
    "bvar",
    "sort",
    "const",
    "app",
    "lam",
    "forallE",
    "letE",
    "proj",
    "natVal",
    "strVal",
    "mdata",
}
DECL_KINDS = {"axiom", "def", "opaque", "thm", "quot", "inductive"}


class ProbeError(ValueError):
    """Malformed or unsupported input; the probe never guesses."""


@dataclass(frozen=True)
class InductiveTypeInventory:
    name: str
    all_names: tuple[str, ...]
    constructor_names: tuple[str, ...]
    num_params: int
    num_indices: int
    num_nested: int
    is_rec: bool
    is_reflexive: bool


@dataclass(frozen=True)
class ConstructorInventory:
    name: str
    inductive: str
    cidx: int
    num_params: int
    num_fields: int


@dataclass(frozen=True)
class RecursorInventory:
    name: str
    all_names: tuple[str, ...]
    num_params: int
    num_indices: int
    num_motives: int
    num_minors: int
    rule_constructors: tuple[str, ...]
    rule_nfields: tuple[int, ...]
    k: bool


@dataclass(frozen=True)
class InductiveGroupInventory:
    types: tuple[InductiveTypeInventory, ...]
    constructors: tuple[ConstructorInventory, ...]
    recursors: tuple[RecursorInventory, ...]


@dataclass(frozen=True)
class ProbeResult:
    format: str
    lean: str
    lean_githash: str
    names: int
    levels: int
    exprs: int
    decls: int
    declaration_kinds: dict[str, int]
    expression_kinds: dict[str, int]
    declaration_names: tuple[str, ...]
    inductive_groups: tuple[InductiveGroupInventory, ...]
    blockers: tuple[str, ...]


def _integer(value: Any, where: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ProbeError(f"{where}: expected a non-negative integer")
    return value


def _boolean(value: Any, where: str) -> bool:
    if not isinstance(value, bool):
        raise ProbeError(f"{where}: expected a boolean")
    return value


def _object(value: Any, where: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise ProbeError(f"{where}: expected an object")
    return value


def _refs_exist(refs: Iterable[Any], seen: set[int], where: str) -> None:
    for raw in refs:
        ref = _integer(raw, where)
        if ref not in seen:
            raise ProbeError(f"{where}: forward or missing reference {ref}")


def _one_kind(record: dict[str, Any], kinds: set[str], where: str) -> str:
    found = sorted(kinds.intersection(record))
    if len(found) != 1:
        raise ProbeError(f"{where}: expected exactly one record kind, got {found}")
    return found[0]


def probe_lines(lines: Iterable[str], *, require_format: str = FORMAT_VERSION) -> ProbeResult:
    records: list[dict[str, Any]] = []
    for line_number, raw in enumerate(lines, 1):
        if not raw.strip():
            raise ProbeError(f"line {line_number}: blank lines are not NDJSON records")
        try:
            records.append(_object(json.loads(raw), f"line {line_number}"))
        except json.JSONDecodeError as error:
            raise ProbeError(f"line {line_number}: invalid JSON: {error.msg}") from error
    if not records:
        raise ProbeError("empty input")

    if set(records[0]) != {"meta"}:
        raise ProbeError("line 1: stream must begin with exactly one meta record")
    meta = _object(records[0]["meta"], "meta")
    export_format = str(_object(meta.get("format"), "meta.format").get("version", ""))
    lean = _object(meta.get("lean"), "meta.lean")
    lean_version = str(lean.get("version", ""))
    lean_githash = str(lean.get("githash", ""))
    if export_format != require_format:
        raise ProbeError(
            f"meta.format.version: expected {require_format}, got {export_format or '<missing>'}"
        )
    if not lean_version or not lean_githash:
        raise ProbeError("meta.lean: version and githash are required")

    names = {0}
    name_values = {0: ""}
    levels = {0}
    exprs: set[int] = set()
    next_name = 1
    next_level = 1
    next_expr = 0
    expression_kinds: Counter[str] = Counter()
    declaration_kinds: Counter[str] = Counter()
    declaration_names: list[str] = []
    inductive_groups: list[InductiveGroupInventory] = []
    blockers: set[str] = set()

    for line_number, record in enumerate(records[1:], 2):
        if "meta" in record:
            raise ProbeError(f"line {line_number}: duplicate meta record")
        marker_count = sum(marker in record for marker in ("in", "il", "ie"))
        if marker_count > 1:
            raise ProbeError(f"line {line_number}: record has multiple index spaces")

        if "in" in record:
            kind = _one_kind(record, NAME_KINDS, f"line {line_number}")
            index = _integer(record["in"], f"line {line_number}.in")
            if index != next_name:
                raise ProbeError(f"line {line_number}.in: expected dense index {next_name}, got {index}")
            payload = _object(record[kind], f"line {line_number}.{kind}")
            _refs_exist([payload.get("pre")], names, f"line {line_number}.{kind}.pre")
            if kind == "str" and not isinstance(payload.get("str"), str):
                raise ProbeError(f"line {line_number}.str.str: expected string")
            if kind == "num":
                _integer(payload.get("i"), f"line {line_number}.num.i")
            prefix = name_values[payload["pre"]]
            suffix = payload["str"] if kind == "str" else str(payload["i"])
            name_values[index] = f"{prefix}.{suffix}" if prefix else suffix
            names.add(index)
            next_name += 1
            continue

        if "il" in record:
            kind = _one_kind(record, LEVEL_KINDS, f"line {line_number}")
            index = _integer(record["il"], f"line {line_number}.il")
            if index != next_level:
                raise ProbeError(f"line {line_number}.il: expected dense index {next_level}, got {index}")
            value = record[kind]
            if kind == "param":
                _refs_exist([value], names, f"line {line_number}.param")
            elif kind == "succ":
                _refs_exist([value], levels, f"line {line_number}.succ")
            else:
                if not isinstance(value, list) or len(value) != 2:
                    raise ProbeError(f"line {line_number}.{kind}: expected two level indices")
                _refs_exist(value, levels, f"line {line_number}.{kind}")
            levels.add(index)
            next_level += 1
            continue

        if "ie" in record:
            kind = _one_kind(record, EXPR_KINDS, f"line {line_number}")
            index = _integer(record["ie"], f"line {line_number}.ie")
            if index != next_expr:
                raise ProbeError(f"line {line_number}.ie: expected dense index {next_expr}, got {index}")
            value = record[kind]
            if kind == "sort":
                _refs_exist([value], levels, f"line {line_number}.sort")
            elif kind == "const":
                value = _object(value, f"line {line_number}.const")
                _refs_exist([value.get("name")], names, f"line {line_number}.const.name")
                universes = value.get("us")
                if not isinstance(universes, list):
                    raise ProbeError(f"line {line_number}.const.us: expected array")
                _refs_exist(universes, levels, f"line {line_number}.const.us")
            elif kind == "app":
                value = _object(value, f"line {line_number}.app")
                _refs_exist([value.get("fn"), value.get("arg")], exprs, f"line {line_number}.app")
            elif kind in {"lam", "forallE"}:
                value = _object(value, f"line {line_number}.{kind}")
                _refs_exist([value.get("name")], names, f"line {line_number}.{kind}.name")
                _refs_exist([value.get("type"), value.get("body")], exprs, f"line {line_number}.{kind}")
                if value.get("binderInfo") not in {
                    "default",
                    "implicit",
                    "strictImplicit",
                    "instImplicit",
                }:
                    raise ProbeError(f"line {line_number}.{kind}.binderInfo: unknown binder mode")
            elif kind == "letE":
                value = _object(value, f"line {line_number}.letE")
                _refs_exist([value.get("name")], names, f"line {line_number}.letE.name")
                _refs_exist(
                    [value.get("type"), value.get("value"), value.get("body")],
                    exprs,
                    f"line {line_number}.letE",
                )
            elif kind == "proj":
                value = _object(value, f"line {line_number}.proj")
                _refs_exist([value.get("typeName")], names, f"line {line_number}.proj.typeName")
                _refs_exist([value.get("struct")], exprs, f"line {line_number}.proj.struct")
                _integer(value.get("idx"), f"line {line_number}.proj.idx")
                blockers.add("expr-projection")
            elif kind == "natVal":
                if not isinstance(value, str) or not value.isdigit():
                    raise ProbeError(f"line {line_number}.natVal: expected decimal string")
            elif kind == "strVal":
                if not isinstance(value, str):
                    raise ProbeError(f"line {line_number}.strVal: expected string")
                blockers.add("literal-string-typing")
            elif kind == "mdata":
                value = _object(value, f"line {line_number}.mdata")
                _refs_exist([value.get("expr")], exprs, f"line {line_number}.mdata.expr")
                _object(value.get("data"), f"line {line_number}.mdata.data")
            else:
                _integer(value, f"line {line_number}.bvar")
            exprs.add(index)
            next_expr += 1
            expression_kinds[kind] += 1
            continue

        kind = _one_kind(record, DECL_KINDS, f"line {line_number}")
        payload = _object(record[kind], f"line {line_number}.{kind}")
        declaration_kinds[kind] += 1
        if kind in {"axiom", "def", "opaque", "thm", "quot"}:
            _refs_exist([payload.get("name")], names, f"line {line_number}.{kind}.name")
            _refs_exist([payload.get("type")], exprs, f"line {line_number}.{kind}.type")
            params = payload.get("levelParams")
            if not isinstance(params, list):
                raise ProbeError(f"line {line_number}.{kind}.levelParams: expected array")
            _refs_exist(params, names, f"line {line_number}.{kind}.levelParams")
            declaration_names.append(name_values[payload["name"]])
        if kind in {"def", "opaque", "thm"}:
            _refs_exist([payload.get("value")], exprs, f"line {line_number}.{kind}.value")
            all_names = payload.get("all")
            if not isinstance(all_names, list):
                raise ProbeError(f"line {line_number}.{kind}.all: expected array")
            _refs_exist(all_names, names, f"line {line_number}.{kind}.all")
        if kind == "def" and payload.get("safety") != "safe":
            raise ProbeError(
                f"line {line_number}.def.safety: unsafe/partial declarations are rejected"
            )
        if kind in {"axiom", "opaque"} and payload.get("isUnsafe", False):
            raise ProbeError(f"line {line_number}.{kind}: unsafe declaration is rejected")
        if kind == "quot":
            if payload.get("kind") not in {"type", "ctor", "lift", "ind"}:
                raise ProbeError(f"line {line_number}.quot.kind: unknown quotient declaration kind")
            blockers.add("quotient-package")
        if kind == "inductive":
            types = payload.get("types")
            ctors = payload.get("ctors")
            recs = payload.get("recs")
            if not all(isinstance(items, list) for items in (types, ctors, recs)):
                raise ProbeError(f"line {line_number}.inductive: types/ctors/recs must be arrays")
            if len(types) > 1:
                blockers.add("inductive-mutual")
            type_inventory: list[InductiveTypeInventory] = []
            for type_value in types:
                type_value = _object(type_value, f"line {line_number}.inductive.types")
                _refs_exist([type_value.get("name")], names, f"line {line_number}.inductive.type.name")
                _refs_exist([type_value.get("type")], exprs, f"line {line_number}.inductive.type.type")
                for field in ("levelParams", "all", "ctors"):
                    values = type_value.get(field)
                    if not isinstance(values, list):
                        raise ProbeError(f"line {line_number}.inductive.type.{field}: expected array")
                    _refs_exist(values, names, f"line {line_number}.inductive.type.{field}")
                num_params = _integer(
                    type_value.get("numParams"), "inductive.type.numParams"
                )
                num_indices = _integer(
                    type_value.get("numIndices"), "inductive.type.numIndices"
                )
                num_nested = _integer(
                    type_value.get("numNested"), "inductive.type.numNested"
                )
                is_rec = _boolean(type_value.get("isRec"), "inductive.type.isRec")
                is_reflexive = _boolean(
                    type_value.get("isReflexive"), "inductive.type.isReflexive"
                )
                _boolean(type_value.get("isUnsafe"), "inductive.type.isUnsafe")
                if is_reflexive:
                    blockers.add("inductive-reflexive")
                if num_nested > 0:
                    blockers.add("inductive-nested")
                if is_rec and num_indices > 0:
                    blockers.add("inductive-recursive-indexed")
                if type_value.get("isUnsafe"):
                    raise ProbeError(f"line {line_number}.inductive: unsafe declaration is rejected")
                type_name = name_values[type_value["name"]]
                declaration_names.append(type_name)
                type_inventory.append(
                    InductiveTypeInventory(
                        name=type_name,
                        all_names=tuple(name_values[value] for value in type_value["all"]),
                        constructor_names=tuple(
                            name_values[value] for value in type_value["ctors"]
                        ),
                        num_params=num_params,
                        num_indices=num_indices,
                        num_nested=num_nested,
                        is_rec=is_rec,
                        is_reflexive=is_reflexive,
                    )
                )
            constructor_inventory: list[ConstructorInventory] = []
            for ctor_value in ctors:
                ctor_value = _object(ctor_value, f"line {line_number}.inductive.ctors")
                _refs_exist(
                    [ctor_value.get("name"), ctor_value.get("induct")],
                    names,
                    f"line {line_number}.inductive.ctor.names",
                )
                _refs_exist(
                    [ctor_value.get("type")], exprs, f"line {line_number}.inductive.ctor.type"
                )
                params = ctor_value.get("levelParams")
                if not isinstance(params, list):
                    raise ProbeError(
                        f"line {line_number}.inductive.ctor.levelParams: expected array"
                    )
                _refs_exist(params, names, f"line {line_number}.inductive.ctor.levelParams")
                _boolean(ctor_value.get("isUnsafe"), "inductive.ctor.isUnsafe")
                if ctor_value.get("isUnsafe"):
                    raise ProbeError(f"line {line_number}.inductive: unsafe constructor is rejected")
                ctor_name = name_values[ctor_value["name"]]
                declaration_names.append(ctor_name)
                constructor_inventory.append(
                    ConstructorInventory(
                        name=ctor_name,
                        inductive=name_values[ctor_value["induct"]],
                        cidx=_integer(ctor_value.get("cidx"), "inductive.ctor.cidx"),
                        num_params=_integer(
                            ctor_value.get("numParams"), "inductive.ctor.numParams"
                        ),
                        num_fields=_integer(
                            ctor_value.get("numFields"), "inductive.ctor.numFields"
                        ),
                    )
                )
            recursor_inventory: list[RecursorInventory] = []
            for rec_value in recs:
                rec_value = _object(rec_value, f"line {line_number}.inductive.recs")
                _refs_exist([rec_value.get("name")], names, f"line {line_number}.inductive.rec.name")
                _refs_exist([rec_value.get("type")], exprs, f"line {line_number}.inductive.rec.type")
                for field in ("levelParams", "all"):
                    values = rec_value.get(field)
                    if not isinstance(values, list):
                        raise ProbeError(f"line {line_number}.inductive.rec.{field}: expected array")
                    _refs_exist(values, names, f"line {line_number}.inductive.rec.{field}")
                rules = rec_value.get("rules")
                if not isinstance(rules, list):
                    raise ProbeError(f"line {line_number}.inductive.rec.rules: expected array")
                rule_constructors: list[str] = []
                rule_nfields: list[int] = []
                for rule in rules:
                    rule = _object(rule, f"line {line_number}.inductive.rec.rule")
                    _refs_exist([rule.get("ctor")], names, f"line {line_number}.inductive.rec.rule.ctor")
                    _refs_exist([rule.get("rhs")], exprs, f"line {line_number}.inductive.rec.rule.rhs")
                    rule_constructors.append(name_values[rule["ctor"]])
                    rule_nfields.append(
                        _integer(rule.get("nfields"), "inductive.rec.rule.nfields")
                    )
                _boolean(rec_value.get("k"), "inductive.rec.k")
                _boolean(rec_value.get("isUnsafe"), "inductive.rec.isUnsafe")
                if rec_value.get("isUnsafe"):
                    raise ProbeError(f"line {line_number}.inductive: unsafe recursor is rejected")
                rec_name = name_values[rec_value["name"]]
                declaration_names.append(rec_name)
                recursor_inventory.append(
                    RecursorInventory(
                        name=rec_name,
                        all_names=tuple(name_values[value] for value in rec_value["all"]),
                        num_params=_integer(
                            rec_value.get("numParams"), "inductive.rec.numParams"
                        ),
                        num_indices=_integer(
                            rec_value.get("numIndices"), "inductive.rec.numIndices"
                        ),
                        num_motives=_integer(
                            rec_value.get("numMotives"), "inductive.rec.numMotives"
                        ),
                        num_minors=_integer(
                            rec_value.get("numMinors"), "inductive.rec.numMinors"
                        ),
                        rule_constructors=tuple(rule_constructors),
                        rule_nfields=tuple(rule_nfields),
                        k=rec_value["k"],
                    )
                )
            inductive_groups.append(
                InductiveGroupInventory(
                    types=tuple(type_inventory),
                    constructors=tuple(constructor_inventory),
                    recursors=tuple(recursor_inventory),
                )
            )

    return ProbeResult(
        format=export_format,
        lean=lean_version,
        lean_githash=lean_githash,
        names=len(names) - 1,
        levels=len(levels) - 1,
        exprs=len(exprs),
        decls=sum(declaration_kinds.values()),
        declaration_kinds=dict(sorted(declaration_kinds.items())),
        expression_kinds=dict(sorted(expression_kinds.items())),
        declaration_names=tuple(declaration_names),
        inductive_groups=tuple(inductive_groups),
        blockers=tuple(sorted(blockers)),
    )


def probe_path(path: Path, *, require_format: str = FORMAT_VERSION) -> ProbeResult:
    with path.open(encoding="utf-8") as stream:
        return probe_lines(stream, require_format=require_format)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("path", type=Path)
    parser.add_argument("--json", action="store_true", help="emit structured JSON")
    parser.add_argument("--require-format", default=FORMAT_VERSION)
    args = parser.parse_args()
    try:
        result = probe_path(args.path, require_format=args.require_format)
    except (OSError, ProbeError) as error:
        parser.exit(2, f"LEAN4EXPORT_PROBE_ERROR|{error}\n")
    if args.json:
        print(json.dumps(asdict(result), sort_keys=True, separators=(",", ":")))
    else:
        blockers = ",".join(result.blockers) if result.blockers else "none"
        print(
            "LEAN4EXPORT_PROBE"
            f"|format={result.format}|lean={result.lean}|names={result.names}"
            f"|levels={result.levels}|exprs={result.exprs}|decls={result.decls}"
            f"|blockers={blockers}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

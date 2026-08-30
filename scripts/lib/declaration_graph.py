"""Parse `lean4export` format-3.1 ndjson streams into declaration-graph rows
(L1 phase C1 / G1).

This module owns exactly one thing: turning a raw lean4export ndjson stream
(names/levels/exprs interning tables plus top-level `axiom`/`def`/`thm`/
`opaque`/`quot`/`inductive` records) into a list of declaration-row dicts
shaped like an ADR-0800 pack record, PLUS an extra `mutual_group` field used
for cycle classification.

It deliberately reuses ADR-0800's digest/closure/projection functions from
`scripts/check-library-artifact-contract.py` rather than re-deriving them --
see `_lac()` below. That is the mechanism the planning rule
(`docs/plan/global/50-planning-rules.md`) requires for keeping proof/value
data physically excluded from a producer-facing artifact: the SAME
`project_type_only` function that destructures only type-facing keys, run
against real Mathlib data instead of the nine hand-authored Lean-core
declarations ADR-0800 demonstrates it on.

Record shape reference (from `/data0/axeyum/lean-import-toolchain/
lean4export/Export.lean`, read directly rather than assumed):

    {"in": id, "str": {"pre": id, "str": "seg"}}   name table (id 0 = anonymous)
    {"in": id, "num": {"pre": id, "i": n}}
    {"il": id, "param": nameId}                    level table (id 0 = zero)
    {"il": id, "succ": levelId}
    {"il": id, "max": [l1, l2]}   (as {"max": [...]})
    {"il": id, "imax": [l1, l2]}
    {"ie": id, "bvar": i}                          expr table
    {"ie": id, "sort": levelId}
    {"ie": id, "const": {"name": nameId, "us": [levelId...]}}
    {"ie": id, "app": {"fn": id, "arg": id}}
    {"ie": id, "lam": {"name": nameId, "type": id, "body": id, "binderInfo": s}}
    {"ie": id, "forallE": {"name": nameId, "type": id, "body": id, "binderInfo": s}}
    {"ie": id, "letE": {"name": nameId, "type": id, "value": id, "body": id, "nondep": b}}
    {"ie": id, "proj": {"typeName": nameId, "idx": i, "struct": id}}
    {"ie": id, "natVal": "n"}
    {"ie": id, "strVal": "s"}
    {"ie": id, "mdata": {"data": obj, "expr": id}}
    {"axiom": {"name": nameId, "levelParams": [...], "type": id, "isUnsafe": b}}
    {"def": {"name": nameId, "levelParams": [...], "type": id, "value": id,
             "hints": ..., "safety": ..., "all": [nameId...]}}
    {"opaque": {"name": nameId, "levelParams": [...], "type": id, "value": id,
                "all": [...], "isUnsafe": b}}
    {"thm": {"name": nameId, "levelParams": [...], "type": id, "value": id,
             "all": [nameId...]}}
    {"quot": {"name": nameId, "levelParams": [...], "type": id, "kind": s}}
    {"inductive": {"types": [{"name":, "type":, "all": [...], "ctors": [...], ...}],
                   "ctors": [{"name":, "type":, "induct":, "cidx":, ...}],
                   "recs": [{"name":, "type":, "all": [...], "rules": [...], ...}]}}
"""
from __future__ import annotations

import importlib.util
import json
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parent.parent.parent

TRUSTED_KINDS = {"Inductive", "Constructor", "Recursor", "Axiom", "Opaque", "Quotient"}


def _lac():
    """Load `scripts/check-library-artifact-contract.py` (ADR-0800 reader A)
    as a module, without editing or vendoring it -- it has a dash in its
    filename so a plain `import` cannot reach it. This is the ONE reuse
    point for the digest/closure/projection mechanism; nothing in this file
    reimplements `compute_closure`, `compute_type_digest`,
    `compute_value_digest`, `compute_identity_digest`, `compute_pack_digest`,
    or `project_type_only`."""
    path = REPO_ROOT / "scripts" / "check-library-artifact-contract.py"
    spec = importlib.util.spec_from_file_location("_library_artifact_contract", path)
    assert spec is not None and spec.loader is not None
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


LAC = _lac()


# ---------------------------------------------------------------------------
# Raw ndjson parsing into local per-file tables
# ---------------------------------------------------------------------------


class ExportFile:
    """One parsed lean4export ndjson stream: local id -> node tables, plus
    the ordered list of top-level declaration records (still holding local
    ids -- resolution to global name strings happens in `resolve_rows`)."""

    def __init__(self) -> None:
        self.names: dict[int, tuple[int, str]] = {0: (0, "")}
        self.levels: dict[int, tuple] = {0: ("zero", None)}
        self.exprs: dict[int, tuple] = {}
        self.decls: list[dict] = []
        self._name_cache: dict[int, str] = {0: ""}

    def resolve_name(self, nid: int) -> str:
        if nid in self._name_cache:
            return self._name_cache[nid]
        pre, seg = self.names[nid]
        parent = self.resolve_name(pre)
        full = f"{parent}.{seg}" if parent else seg
        self._name_cache[nid] = full
        return full


def parse_ndjson(path: Path) -> ExportFile:
    ef = ExportFile()
    with open(path, "r", encoding="utf-8") as f:
        first = True
        for line in f:
            line = line.strip()
            if not line:
                continue
            rec = json.loads(line)
            if first:
                first = False
                if "meta" in rec:
                    continue
            if "in" in rec:
                nid = rec["in"]
                if "str" in rec:
                    ef.names[nid] = (rec["str"]["pre"], rec["str"]["str"])
                elif "num" in rec:
                    ef.names[nid] = (rec["num"]["pre"], f"#{rec['num']['i']}")
                continue
            if "il" in rec:
                lid = rec["il"]
                if "param" in rec:
                    ef.levels[lid] = ("param", rec["param"])
                elif "succ" in rec:
                    ef.levels[lid] = ("succ", rec["succ"])
                elif "max" in rec:
                    ef.levels[lid] = ("max", tuple(rec["max"]))
                elif "imax" in rec:
                    ef.levels[lid] = ("imax", tuple(rec["imax"]))
                continue
            if "ie" in rec:
                eid = rec["ie"]
                ef.exprs[eid] = _expr_variant(rec)
                continue
            for k in ("axiom", "def", "opaque", "thm", "quot", "inductive"):
                if k in rec:
                    ef.decls.append({"kind": k, **rec[k]})
                    break
    return ef


def _expr_variant(rec: dict) -> tuple:
    if "bvar" in rec:
        return ("bvar", rec["bvar"])
    if "sort" in rec:
        return ("sort", rec["sort"])
    if "const" in rec:
        return ("const", rec["const"]["name"], tuple(rec["const"].get("us", [])))
    if "app" in rec:
        return ("app", rec["app"]["fn"], rec["app"]["arg"])
    if "lam" in rec:
        d = rec["lam"]
        return ("lam", d["name"], d["type"], d["body"])
    if "forallE" in rec:
        d = rec["forallE"]
        return ("forallE", d["name"], d["type"], d["body"])
    if "letE" in rec:
        d = rec["letE"]
        return ("letE", d["name"], d["type"], d["value"], d["body"])
    if "proj" in rec:
        d = rec["proj"]
        return ("proj", d["typeName"], d["idx"], d["struct"])
    if "natVal" in rec:
        return ("natVal", rec["natVal"])
    if "strVal" in rec:
        return ("strVal", rec["strVal"])
    if "mdata" in rec:
        return ("mdata", rec["mdata"]["expr"])
    raise ValueError(f"unrecognized expr record: {rec}")


# ---------------------------------------------------------------------------
# Const collection and canonical text rendering over an ExportFile
# ---------------------------------------------------------------------------

# Literal expr nodes implicitly depend on these even though lean4export does
# not encode it as a `const` node inside the literal -- it instead forces the
# named declarations to be exported separately (`dumpNatDeps`/`dumpStrDeps`
# in Export.lean). Recording the implicit edge here keeps the dependency
# graph honest about what a nat/string literal actually denotes.
_NAT_LITERAL_IMPLICIT_DEP = "Nat"
_STR_LITERAL_IMPLICIT_DEPS = ("Char.ofNat", "String.ofList")


def collect_consts(ef: ExportFile, eid: int, cache: dict[int, frozenset]) -> frozenset:
    if eid in cache:
        return cache[eid]
    node = ef.exprs[eid]
    kind = node[0]
    result: set[str] = set()
    if kind == "const":
        result.add(ef.resolve_name(node[1]))
    elif kind == "app":
        result |= collect_consts(ef, node[1], cache)
        result |= collect_consts(ef, node[2], cache)
    elif kind == "lam" or kind == "forallE":
        result |= collect_consts(ef, node[2], cache)
        result |= collect_consts(ef, node[3], cache)
    elif kind == "letE":
        result |= collect_consts(ef, node[2], cache)
        result |= collect_consts(ef, node[3], cache)
        result |= collect_consts(ef, node[4], cache)
    elif kind == "proj":
        result.add(ef.resolve_name(node[1]))
        result |= collect_consts(ef, node[3], cache)
    elif kind == "mdata":
        result |= collect_consts(ef, node[1], cache)
    elif kind == "natVal":
        result.add(_NAT_LITERAL_IMPLICIT_DEP)
    elif kind == "strVal":
        result |= set(_STR_LITERAL_IMPLICIT_DEPS)
    # bvar, sort: no const references.
    frozen = frozenset(result)
    cache[eid] = frozen
    return frozen


def render_level(ef: ExportFile, lid: int) -> str:
    if lid == 0:
        return "0"
    node = ef.levels[lid]
    kind = node[0]
    if kind == "param":
        return ef.resolve_name(node[1])
    if kind == "succ":
        return f"{render_level(ef, node[1])}+1"
    if kind == "max":
        a, b = node[1]
        return f"max({render_level(ef, a)},{render_level(ef, b)})"
    if kind == "imax":
        a, b = node[1]
        return f"imax({render_level(ef, a)},{render_level(ef, b)})"
    raise ValueError(f"bad level node {node}")


def render_expr(ef: ExportFile, eid: int, cache: dict[int, str]) -> str:
    """Deterministic, memoizable, ALPHA-INVARIANT canonical text. Bound
    variables render as their raw de Bruijn index (`#i`), never a looked-up
    display name -- both because the same expr id can be reached from
    different ambient binder-name stacks (lean4export shares
    structurally-identical subterms), and because binder DISPLAY NAMES
    themselves are not reliably deterministic across independent lean4export
    invocations.

    Measured directly: exporting `Nat.add_comm` from two different `lake env`
    processes (once via mathlib4's environment, once via lean4export's own
    Init-only environment) produced BYTE-IDENTICAL structural content for the
    shared auxiliary `Nat.add.match_1` except for its bound-variable NAMES,
    e.g. `x._@.Init.Prelude.#2075127268._hygCtx...` in one run versus
    `x._@.Init.Prelude.#2314059840._hygCtx...` in the other -- Lean's macro
    hygiene assigns those numeric suffixes per elaboration SESSION, not per
    declaration. Rendering them would make `type_digest`/`identity_digest`
    disagree between two independent, semantically-identical exports of the
    same real declaration, which is exactly the nondeterminism a digest
    exists to catch -- so binder names at lam/forallE/letE are NOT rendered
    at all (`_` in their place); only the de Bruijn body references and the
    binder's TYPE (which does not carry hygiene artifacts here) are hashed.
    This is safe because Lean terms are meaningful up to alpha-equivalence:
    dropping binder names changes nothing the type checker cares about."""
    if eid in cache:
        return cache[eid]
    node = ef.exprs[eid]
    kind = node[0]
    if kind == "bvar":
        s = f"#{node[1]}"
    elif kind == "sort":
        s = f"Sort {render_level(ef, node[1])}"
    elif kind == "const":
        us = ",".join(render_level(ef, u) for u in node[2])
        nm = ef.resolve_name(node[1])
        s = f"{nm}.{{{us}}}" if us else nm
    elif kind == "app":
        s = f"({render_expr(ef, node[1], cache)} {render_expr(ef, node[2], cache)})"
    elif kind == "lam":
        s = f"fun (_ : {render_expr(ef, node[2], cache)}) => {render_expr(ef, node[3], cache)}"
    elif kind == "forallE":
        s = f"(_ : {render_expr(ef, node[2], cache)}) -> {render_expr(ef, node[3], cache)}"
    elif kind == "letE":
        s = (
            f"let _ : {render_expr(ef, node[2], cache)} := "
            f"{render_expr(ef, node[3], cache)}; {render_expr(ef, node[4], cache)}"
        )
    elif kind == "proj":
        nm = ef.resolve_name(node[1])
        s = f"{nm}.proj[{node[2]}]({render_expr(ef, node[3], cache)})"
    elif kind == "natVal":
        s = str(node[1])
    elif kind == "strVal":
        s = json.dumps(node[1])
    elif kind == "mdata":
        s = render_expr(ef, node[1], cache)
    else:
        raise ValueError(f"bad expr node {node}")
    cache[eid] = s
    return s


# ---------------------------------------------------------------------------
# Turning an ExportFile into declaration rows
# ---------------------------------------------------------------------------


def _mk_row(
    ef: ExportFile,
    name: str,
    kind: str,
    universes: list[str],
    type_id: int,
    value_id: int | None,
    mutual_group: list[str],
    text_cache: dict[int, str],
    const_cache: dict[int, frozenset],
    extra_type_deps: list[str] = (),
) -> dict:
    type_text = render_expr(ef, type_id, text_cache)
    direct_type_deps = sorted(
        (collect_consts(ef, type_id, const_cache) | set(extra_type_deps)) - {name}
    )
    if value_id is not None and kind in ("Definition", "Theorem"):
        value_text = render_expr(ef, value_id, text_cache)
        value_consts = collect_consts(ef, value_id, const_cache)
        direct_value_deps = sorted(value_consts - set(direct_type_deps) - {name})
    else:
        # Trusted kinds (Inductive/Constructor/Recursor/Axiom/Opaque/
        # Quotient) carry NO value/proof edges, by construction -- even
        # where lean4export's own export happens to include an
        # implementation term (Opaque). See module docstring / ADR-0800's
        # TRUSTED_KINDS: nothing downstream may treat a trusted kind's
        # hidden implementation as "how a theorem was proved".
        value_text = None
        direct_value_deps = []
    type_digest = LAC.compute_type_digest({"type": type_text})
    value_digest = LAC.compute_value_digest({"value": value_text})
    row = {
        "name": name,
        "kind": kind,
        "universes": universes,
        "type": type_text,
        "value": value_text,
        "type_digest": type_digest,
        "value_digest": value_digest,
        "direct_type_deps": direct_type_deps,
        "direct_value_deps": direct_value_deps,
        "mutual_group": sorted(set(mutual_group) | {name}),
    }
    row["identity_digest"] = LAC.compute_identity_digest(row, type_digest, value_digest)
    return row


def resolve_rows(ef: ExportFile, origin_module: str) -> list[dict]:
    """Turn every top-level declaration record in `ef` into one or more
    rows (an `inductive` record bundles a whole mutual family: one row per
    type, one per constructor, one per recursor)."""
    text_cache: dict[int, str] = {}
    const_cache: dict[int, frozenset] = {}
    rows: list[dict] = []

    for decl in ef.decls:
        kind = decl["kind"]
        if kind in ("axiom", "def", "opaque", "thm"):
            name = ef.resolve_name(decl["name"])
            universes = [ef.resolve_name(n) for n in decl["levelParams"]]
            mutual_group = [ef.resolve_name(n) for n in decl.get("all", [decl["name"]])]
            row_kind = {"axiom": "Axiom", "def": "Definition", "opaque": "Opaque", "thm": "Theorem"}[kind]
            value_id = decl.get("value") if kind != "axiom" else None
            row = _mk_row(
                ef, name, row_kind, universes, decl["type"], value_id, mutual_group,
                text_cache, const_cache,
            )
            row["origin_module"] = origin_module
            rows.append(row)
        elif kind == "quot":
            name = ef.resolve_name(decl["name"])
            universes = [ef.resolve_name(n) for n in decl["levelParams"]]
            row = _mk_row(
                ef, name, "Quotient", universes, decl["type"], None, [name],
                text_cache, const_cache,
            )
            row["origin_module"] = origin_module
            rows.append(row)
        elif kind == "inductive":
            # One `inductive` JSON record is ONE atomic kernel-admission unit
            # (Lean4's `Declaration::InductiveDecl`): every type, constructor,
            # and recursor it bundles is checked together, whether or not the
            # types actually reference each other. `block_group` is that whole
            # unit's name set -- used as `mutual_group` for EVERY row this
            # record produces, not just each type's own narrower `all` list,
            # because a single-type inductive with several constructors (e.g.
            # `Nat`: `Nat.zero`/`Nat.succ`) needs its ENTIRE ctor set to
            # explain the SCC {Nat, Nat.zero, Nat.succ} that the atomic
            # type->constructor edge below creates -- a narrower per-ctor
            # group of just [type, this-ctor] cannot.
            block_group = sorted(
                {ef.resolve_name(t["name"]) for t in decl["types"]}
                | {ef.resolve_name(c["name"]) for c in decl["ctors"]}
                | {ef.resolve_name(r["name"]) for r in decl["recs"]}
            )
            for t in decl["types"]:
                name = ef.resolve_name(t["name"])
                universes = [ef.resolve_name(n) for n in t["levelParams"]]
                # Deliberate modeling choice, not a literal reading of the
                # type's own declared Lean type (which is always just
                # `Sort _`): an inductive type is not meaningfully usable
                # without its own constructors existing (the kernel checks
                # them as one unit), so this graph records
                # type -> its-own-constructors as a real edge. Without it, a
                # mutual/self-referential inductive family never forms a
                # literal graph cycle at all (constructors point AT the
                # type(s) they mention; nothing points back), and the
                # UNEXPECTED_CYCLE guard below would never have anything to
                # exercise on inductive data.
                own_ctors = [ef.resolve_name(c["name"]) for c in decl["ctors"] if c["induct"] == t["name"]]
                row = _mk_row(
                    ef, name, "Inductive", universes, t["type"], None, block_group,
                    text_cache, const_cache, extra_type_deps=own_ctors,
                )
                row["origin_module"] = origin_module
                rows.append(row)
            for c in decl["ctors"]:
                name = ef.resolve_name(c["name"])
                universes = [ef.resolve_name(n) for n in c["levelParams"]]
                row = _mk_row(
                    ef, name, "Constructor", universes, c["type"], None, block_group,
                    text_cache, const_cache,
                )
                row["origin_module"] = origin_module
                rows.append(row)
            for r in decl["recs"]:
                name = ef.resolve_name(r["name"])
                universes = [ef.resolve_name(n) for n in r["levelParams"]]
                row = _mk_row(
                    ef, name, "Recursor", universes, r["type"], None, block_group,
                    text_cache, const_cache,
                )
                row["origin_module"] = origin_module
                rows.append(row)
        else:
            raise ValueError(f"unrecognized declaration kind {kind!r}")
    return rows


# ---------------------------------------------------------------------------
# Graph utilities: SCC (Tarjan) and cycle classification
# ---------------------------------------------------------------------------


def tarjan_sccs(nodes: list[str], edges: dict[str, list[str]]) -> list[list[str]]:
    """Standard Tarjan SCC, iterative to avoid Python recursion limits on a
    large closure. Returns all SCCs (including singletons); callers filter
    to size > 1 for cycle reporting."""
    index_counter = [0]
    stack: list[str] = []
    on_stack: set[str] = set()
    indices: dict[str, int] = {}
    lowlink: dict[str, int] = {}
    sccs: list[list[str]] = []

    for start in nodes:
        if start in indices:
            continue
        work: list[tuple[str, int]] = [(start, 0)]
        while work:
            v, pi = work[-1]
            if pi == 0:
                indices[v] = index_counter[0]
                lowlink[v] = index_counter[0]
                index_counter[0] += 1
                stack.append(v)
                on_stack.add(v)
            recursed = False
            neighbors = edges.get(v, [])
            i = pi
            while i < len(neighbors):
                w = neighbors[i]
                if w not in indices:
                    work[-1] = (v, i + 1)
                    work.append((w, 0))
                    recursed = True
                    break
                elif w in on_stack:
                    lowlink[v] = min(lowlink[v], indices[w])
                i += 1
            else:
                pass
            if recursed:
                continue
            work.pop()
            if work:
                parent = work[-1][0]
                lowlink[parent] = min(lowlink[parent], lowlink[v])
            if lowlink[v] == indices[v]:
                comp = []
                while True:
                    w = stack.pop()
                    on_stack.discard(w)
                    comp.append(w)
                    if w == v:
                        break
                sccs.append(sorted(comp))
    return sccs


def classify_cycles(rows: list[dict], mode: str) -> dict:
    """Compute SCCs over the TYPE graph (`mode == "type"`, edges =
    `direct_type_deps` only) or the FULL graph (`mode == "full"`, edges =
    `direct_type_deps` union `direct_value_deps`), and classify every
    multi-node SCC against the `mutual_group` recorded on its member rows.
    A cycle is EXPECTED iff its whole node set is a subset of some one row's
    `mutual_group` (mutual inductive families and mutual recursion groups
    both record this on every member row); anything else is UNEXPECTED and
    must fail the gate rather than being silently accepted or dropped."""
    if mode not in ("type", "full"):
        raise ValueError(f"mode must be 'type' or 'full', got {mode!r}")
    by_name = {r["name"]: r for r in rows}
    nodes = list(by_name)
    if mode == "full":
        edges = {
            n: sorted(set(r["direct_type_deps"]) | set(r["direct_value_deps"]))
            for n, r in by_name.items()
        }
    else:
        edges = {n: r["direct_type_deps"] for n, r in by_name.items()}
    # Strip self-loops before SCC computation: a declaration depending on
    # itself is a length-1 cycle with no ordering implications, structurally
    # unlike a length>1 SCC, and is reported separately rather than forcing
    # a mutual_group classification for a trivial case.
    edges = {n: [m for m in ms if m != n] for n, ms in edges.items()}
    self_loops = sorted(n for n in nodes if n in (by_name[n].get("direct_type_deps", []) + by_name[n].get("direct_value_deps", [])))

    sccs = [c for c in tarjan_sccs(nodes, edges) if len(c) > 1]
    expected = []
    unexpected = []
    for comp in sccs:
        comp_set = set(comp)
        explained = False
        for n in comp:
            group = set(by_name[n].get("mutual_group", []))
            if comp_set <= group:
                explained = True
                break
        entry = {"nodes": comp, "size": len(comp)}
        if explained:
            kind = "mutual_recursion"
            if any(by_name[n]["kind"] in ("Inductive", "Constructor", "Recursor") for n in comp):
                kind = "mutual_inductive"
            entry["classification"] = kind
            expected.append(entry)
        else:
            entry["classification"] = "UNEXPECTED_CYCLE"
            unexpected.append(entry)
    return {
        "self_loops": self_loops,
        "expected_cycles": expected,
        "unexpected_cycles": unexpected,
    }

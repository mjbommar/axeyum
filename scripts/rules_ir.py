#!/usr/bin/env python3
"""Compile a provision-keyed rule model against a lifted U.S. Code section.

A rules file (`rules.json`) states facts, constants, and predicates. Every
predicate names the provision it encodes (a USLM-style identifier from the
lifted section JSON produced by `scripts/uscode_lift.py`) and quotes an anchor
phrase from that provision. One encoding then serves three consumers:

1. **Traceability.** `trace()` checks that each anchor occurs verbatim in its
   provision, that each numeric literal in a predicate matches a quantity the
   lifter extracted from that provision (value and comparator), that every
   dependency between predicates on different provisions is justified by the
   statute's own structure, cross-references, or defined-term uses, and that
   every internal cross-reference leaving a modeled provision is either
   consumed by the model or listed as out of scope with a reason.
2. **Evaluation.** `evaluate()` computes every predicate for a concrete fact
   pattern, so the same model answers "which clauses apply and what is the
   statutory maximum" without a solver.
3. **Obligations.** `emit_obligation()` writes an SMT-LIB 2 script per check
   (facts as constants, predicates as `define-fun`), which Axeyum decides and
   certifies in `crates/axeyum-solver/tests/rules_as_code_examples.rs`.

Expressions are SMT-LIB s-expressions over Bool and Int with `and`, `or`,
`not`, `=>`, `ite`, `=`, `distinct`, `<`, `<=`, `>`, `>=`, `+`, `-`, `*`, and an
n-ary `max` that emission expands to nested `ite`.

Usage:

    python3 scripts/rules_ir.py RULES.json [--check]

writes `smt2/<obligation>.smt2` and `compiled.json` next to RULES.json;
`--check` fails if any of them is stale.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
SExpr = Any  # str | int | bool | list[SExpr]


class RulesError(Exception):
    pass


# ---------------------------------------------------------------------------
# S-expressions


def parse_sexpr(text: str) -> SExpr:
    tokens = re.findall(r"\(|\)|[^\s()]+", text)
    position = 0

    def read() -> SExpr:
        nonlocal position
        if position >= len(tokens):
            raise RulesError(f"unexpected end of expression: {text}")
        token = tokens[position]
        position += 1
        if token == "(":
            items = []
            while position < len(tokens) and tokens[position] != ")":
                items.append(read())
            if position >= len(tokens):
                raise RulesError(f"unbalanced expression: {text}")
            position += 1
            return items
        if token == ")":
            raise RulesError(f"unexpected ')' in {text}")
        if re.fullmatch(r"-?\d+", token):
            return int(token)
        if token == "true":
            return True
        if token == "false":
            return False
        return token

    expr = read()
    if position != len(tokens):
        raise RulesError(f"trailing tokens in expression: {text}")
    return expr


def symbols(expr: SExpr) -> set[str]:
    if isinstance(expr, list):
        out: set[str] = set()
        for item in expr[1:]:
            out |= symbols(item)
        return out
    if isinstance(expr, str):
        return {expr}
    return set()


def int_literals(expr: SExpr) -> list[int]:
    if isinstance(expr, list):
        out: list[int] = []
        for item in expr[1:]:
            out.extend(int_literals(item))
        return out
    if isinstance(expr, int) and not isinstance(expr, bool):
        return [expr]
    return []


COMPARATORS = {"<", "<=", ">", ">="}
FLIP = {"<": ">", "<=": ">=", ">": "<", ">=": "<="}


def literal_comparisons(expr: SExpr) -> list[tuple[str, int]]:
    """(comparator as `var OP literal`, literal) for each var-vs-literal atom."""
    out: list[tuple[str, int]] = []
    if not isinstance(expr, list):
        return out
    head = expr[0]
    if head in COMPARATORS and len(expr) == 3:
        lhs, rhs = expr[1], expr[2]
        if isinstance(rhs, int) and not isinstance(rhs, bool) and not isinstance(lhs, int):
            out.append((head, rhs))
        elif isinstance(lhs, int) and not isinstance(lhs, bool) and not isinstance(rhs, int):
            out.append((FLIP[head], lhs))
    for item in expr[1:]:
        out.extend(literal_comparisons(item))
    return out


def render_sexpr(expr: SExpr) -> str:
    if isinstance(expr, list):
        if expr and expr[0] == "max":
            return render_sexpr(expand_max(expr[1:]))
        return "(" + " ".join(render_sexpr(item) for item in expr) + ")"
    if isinstance(expr, bool):
        return "true" if expr else "false"
    if isinstance(expr, int):
        return str(expr) if expr >= 0 else f"(- {-expr})"
    return expr


def expand_max(args: list[SExpr]) -> SExpr:
    if not args:
        raise RulesError("max needs at least one argument")
    acc = args[0]
    for item in args[1:]:
        acc = ["ite", [">=", acc, item], acc, item]
    return acc


def rename(expr: SExpr, mapping: dict[str, str]) -> SExpr:
    if isinstance(expr, list):
        return [expr[0]] + [rename(item, mapping) for item in expr[1:]]
    if isinstance(expr, str):
        return mapping.get(expr, expr)
    return expr


def eval_sexpr(expr: SExpr, env: dict[str, Any]) -> Any:
    if isinstance(expr, bool) or isinstance(expr, int):
        return expr
    if isinstance(expr, str):
        if expr not in env:
            raise RulesError(f"unbound symbol {expr}")
        return env[expr]
    head, args = expr[0], expr[1:]
    if head == "ite":
        return eval_sexpr(args[1] if eval_sexpr(args[0], env) else args[2], env)
    values = [eval_sexpr(item, env) for item in args]
    if head == "and":
        return all(values)
    if head == "or":
        return any(values)
    if head == "not":
        return not values[0]
    if head == "=>":
        return (not values[0]) or values[1]
    if head == "=":
        return all(value == values[0] for value in values[1:])
    if head == "distinct":
        return len(set(values)) == len(values)
    if head == "<":
        return values[0] < values[1]
    if head == "<=":
        return values[0] <= values[1]
    if head == ">":
        return values[0] > values[1]
    if head == ">=":
        return values[0] >= values[1]
    if head == "+":
        return sum(values)
    if head == "-":
        return -values[0] if len(values) == 1 else values[0] - sum(values[1:])
    if head == "*":
        product = 1
        for value in values:
            product *= value
        return product
    if head == "max":
        return max(values)
    raise RulesError(f"unsupported operator {head}")


def to_python(expr: SExpr) -> str:
    """Translate an expression to a Python expression over `env`."""
    if isinstance(expr, bool):
        return "True" if expr else "False"
    if isinstance(expr, int):
        return repr(expr)
    if isinstance(expr, str):
        return f"env[{expr!r}]"
    head, args = expr[0], [to_python(item) for item in expr[1:]]
    binary = {"<": "<", "<=": "<=", ">": ">", ">=": ">="}
    if head == "ite":
        return f"({args[1]} if {args[0]} else {args[2]})"
    if head == "and":
        return "(" + " and ".join(args) + ")"
    if head == "or":
        return "(" + " or ".join(args) + ")"
    if head == "not":
        return f"(not {args[0]})"
    if head == "=>":
        return f"((not {args[0]}) or {args[1]})"
    if head == "=":
        return "(" + " and ".join(f"{args[0]} == {other}" for other in args[1:]) + ")"
    if head == "distinct":
        return f"(len({{{', '.join(args)}}}) == {len(args)})"
    if head in binary:
        return f"({args[0]} {binary[head]} {args[1]})"
    if head == "+":
        return "(" + " + ".join(args) + ")"
    if head == "-":
        return f"(-{args[0]})" if len(args) == 1 else "(" + " - ".join(args) + ")"
    if head == "*":
        return "(" + " * ".join(args) + ")"
    if head == "max":
        return "max(" + ", ".join(args) + ")"
    raise RulesError(f"unsupported operator {head}")


# ---------------------------------------------------------------------------
# Rules model


class Rules:
    def __init__(self, path: Path) -> None:
        self.path = path
        self.dir = path.parent
        self.data = json.loads(path.read_text(encoding="utf-8"))
        lifted_path = ROOT / self.data["lifted"]
        self.lifted = json.loads(lifted_path.read_text(encoding="utf-8"))
        self.base = self.lifted["section"]["id"]
        self.provisions = {node["id"]: node for node in self.lifted["provisions"]}
        self.facts = {fact["name"]: fact for fact in self.data["facts"]}
        self.constants = {const["name"]: const for const in self.data.get("constants", [])}
        self.predicates = {pred["name"]: pred for pred in self.data["predicates"]}
        self.implementations = {impl["name"]: impl for impl in self.data.get("implementations", [])}
        names = (
            list(self.facts) + list(self.constants) + list(self.predicates) + list(self.implementations)
        )
        duplicates = sorted({name for name in names if names.count(name) > 1})
        if duplicates:
            raise RulesError(f"duplicate names: {duplicates}")
        self.exprs: dict[str, SExpr] = {}
        for table in (self.predicates, self.implementations):
            for name, entry in table.items():
                self.exprs[name] = parse_sexpr(entry["expr"])
        self.constraints = [parse_sexpr(item["expr"]) for item in self.data.get("constraints", [])]
        self.order = self._topological_order()
        # Compiled once; `evaluate` runs these instead of walking s-expressions.
        self._compiled = [
            (name, eval(compile("lambda env: " + to_python(self.exprs[name]), name, "eval"), {}))  # noqa: S307
            for name in self.order
        ]
        self._constraint_fns = [
            (constraint, eval(compile("lambda env: " + to_python(constraint), "constraint", "eval"), {}))  # noqa: S307
            for constraint in self.constraints
        ]

    def pid(self, short: str) -> str:
        return self.base + short if short.startswith("/") else short

    def short(self, full: str) -> str:
        return full[len(self.base):] if full.startswith(self.base) else full

    def provision_text(self, provision_id: str) -> str:
        node = self.provisions[provision_id]
        return " ".join(part for part in [node["text"], node.get("continuation", "")] if part)

    def deps(self, name: str) -> set[str]:
        expr = self.exprs[name]
        out = set()
        for symbol in symbols(expr):
            if symbol in self.predicates or symbol in self.implementations:
                out.add(symbol)
            elif symbol in self.facts or symbol in self.constants:
                out.add(symbol)
            else:
                raise RulesError(f"{name} references unknown symbol {symbol}")
        return out

    def _topological_order(self) -> list[str]:
        order: list[str] = []
        state: dict[str, int] = {}

        def visit(name: str) -> None:
            if state.get(name) == 2:
                return
            if state.get(name) == 1:
                raise RulesError(f"cyclic rule dependency through {name}")
            state[name] = 1
            for dep in sorted(self.deps(name)):
                if dep in self.exprs:
                    visit(dep)
            state[name] = 2
            order.append(name)

        for name in sorted(self.exprs):
            visit(name)
        return order

    def sort_of(self, name: str) -> str:
        for table in (self.facts, self.constants, self.predicates, self.implementations):
            if name in table:
                return table[name]["sort"]
        raise RulesError(f"unknown symbol {name}")

    # -- evaluation --------------------------------------------------------

    def evaluate(self, facts: dict[str, Any]) -> dict[str, Any]:
        missing = sorted(set(self.facts) - set(facts))
        extra = sorted(set(facts) - set(self.facts))
        if missing or extra:
            raise RulesError(f"fact pattern mismatch: missing {missing}, unknown {extra}")
        env: dict[str, Any] = dict(facts)
        for name, const in self.constants.items():
            env[name] = const["value"]
        for constraint, check in self._constraint_fns:
            if not check(env):
                raise RulesError(f"fact pattern violates model constraint {render_sexpr(constraint)}")
        for name, fact in self.facts.items():
            domain = fact.get("domain")
            if domain and not (domain["min"] <= env[name] <= domain["max"]):
                raise RulesError(f"fact {name}={env[name]} outside its domain")
        for name, function in self._compiled:
            env[name] = function(env)
        return env

    def evaluate_interpreted(self, facts: dict[str, Any]) -> dict[str, Any]:
        """Reference evaluator: walks the s-expressions (used to cross-check `evaluate`)."""
        env: dict[str, Any] = dict(facts)
        for name, const in self.constants.items():
            env[name] = const["value"]
        for name in self.order:
            env[name] = eval_sexpr(self.exprs[name], env)
        return env

    # -- traceability ------------------------------------------------------

    @staticmethod
    def lineal(a: str, b: str) -> bool:
        """Same provision, or one is an ancestor of the other."""
        return a == b or a.startswith(b + "/") or b.startswith(a + "/")

    def related(self, a: str, b: str) -> bool:
        """Lineal, or siblings in one enumerated list below the section level."""
        if self.lineal(a, b):
            return True
        parent = self.provisions.get(a, {}).get("parent")
        return parent is not None and parent != self.base and parent == self.provisions.get(
            b, {}
        ).get("parent")

    def trace(self) -> dict[str, Any]:
        problems: list[str] = []
        anchored = []
        for table_name, table in (("fact", self.facts), ("predicate", self.predicates)):
            for name, entry in table.items():
                provision = entry.get("provision")
                if provision is None:
                    if table_name == "predicate":
                        problems.append(f"predicate {name} has no provision")
                    continue
                full = self.pid(provision)
                if full not in self.provisions:
                    problems.append(f"{table_name} {name} cites missing provision {provision}")
                    continue
                anchor = entry.get("anchor", "")
                if not anchor:
                    problems.append(f"{table_name} {name} has no anchor quote")
                elif anchor not in self.provision_text(full):
                    problems.append(f"{table_name} {name}: anchor not found in {provision}: {anchor!r}")
                else:
                    anchored.append(name)

        # Numeric literals must be quantities the lifter found in that provision.
        quantities: dict[str, list[dict[str, Any]]] = {}
        for quantity in self.lifted["quantities"]:
            quantities.setdefault(quantity["provision"], []).append(quantity)
        literal_checks = 0
        for name, pred in self.predicates.items():
            full = self.pid(pred["provision"])
            expr = self.exprs[name]
            available = quantities.get(full, [])
            for literal in int_literals(expr):
                if literal == 0 or (literal == 1 and pred["sort"] == "Bool"):
                    continue
                if not any(q["value"] == literal for q in available):
                    problems.append(
                        f"predicate {name}: literal {literal} is not a quantity stated in {pred['provision']}"
                    )
                literal_checks += 1
            for comparator, literal in literal_comparisons(expr):
                matches = [q for q in available if q["value"] == literal]
                if matches and not any(q["comparator"] == comparator for q in matches):
                    stated = sorted({q["comparator"] for q in matches})
                    problems.append(
                        f"predicate {name}: compares with {comparator} {literal}, "
                        f"but {pred['provision']} states {stated} {literal}"
                    )

        # Every dependency between provisions must be justified by the text.
        cross = {}
        for ref in self.lifted["cross_references"]:
            for target in ref["targets"]:
                cross.setdefault(ref["from"], set()).add(target)
        term_defs = {entry["provision"]: entry["term"] for entry in self.lifted["definitions"]}
        term_uses = {entry["term"]: set(entry["provisions"]) for entry in self.lifted["term_uses"]}
        edges = []
        for name, pred in self.predicates.items():
            src = self.pid(pred["provision"])
            for dep in sorted(self.deps(name)):
                if dep not in self.predicates:
                    continue
                dst = self.pid(self.predicates[dep]["provision"])
                justification = None
                if self.related(src, dst):
                    justification = "structure"
                else:
                    for origin, targets in cross.items():
                        if self.lineal(origin, src) and any(
                            target == dst or dst.startswith(target + "/") or target.startswith(dst + "/")
                            for target in targets
                        ):
                            justification = f"cross-reference from {self.short(origin)}"
                            break
                if justification is None:
                    for def_provision, term in term_defs.items():
                        if self.related(def_provision, dst) and any(
                            self.related(use, src) for use in term_uses.get(term, set())
                        ):
                            justification = f'defined term "{term}"'
                            break
                if justification is None:
                    declared = pred.get("justify", {}).get(dep)
                    if declared:
                        justification = f"declared: {declared}"
                if justification is None:
                    problems.append(
                        f"predicate {name} ({pred['provision']}) uses {dep} "
                        f"({self.predicates[dep]['provision']}) with no textual justification"
                    )
                edges.append(
                    {
                        "from": name,
                        "to": dep,
                        "from_provision": pred["provision"],
                        "to_provision": self.predicates[dep]["provision"],
                        "justification": justification,
                    }
                )

        # Every cross-reference leaving a modeled provision is consumed or scoped out.
        modeled = {self.pid(pred["provision"]) for pred in self.predicates.values()}
        out_of_scope = {
            (self.pid(item["from"]), self.pid(item["target"])): item["reason"]
            for item in self.data.get("out_of_scope_refs", [])
        }
        consumed_refs = []
        for ref in self.lifted["cross_references"]:
            if ref["scope"] != "internal" or not any(
                ref["from"] == item or ref["from"].startswith(item + "/") for item in modeled
            ):
                continue
            for target in ref["targets"]:
                consumed = any(
                    edge
                    for edge in edges
                    if self.related(self.pid(edge["from_provision"]), ref["from"])
                    and (
                        self.pid(edge["to_provision"]) == target
                        or self.pid(edge["to_provision"]).startswith(target + "/")
                        or target.startswith(self.pid(edge["to_provision"]) + "/")
                    )
                )
                # A reference to an offense subsection is consumed by the fact
                # that selects that offense.
                fact_consumed = any(
                    fact.get("provision")
                    and (
                        self.pid(fact["provision"]) == target
                        or self.pid(fact["provision"]).startswith(target + "/")
                    )
                    for fact in self.facts.values()
                )
                status = "consumed" if consumed or fact_consumed else None
                if status is None and (ref["from"], target) in out_of_scope:
                    status = "out of scope: " + out_of_scope[(ref["from"], target)]
                if status is None:
                    problems.append(
                        f"cross-reference {self.short(ref['from'])} -> {self.short(target)} "
                        f"({ref['raw']!r}) is neither modeled nor declared out of scope"
                    )
                consumed_refs.append(
                    {
                        "from": self.short(ref["from"]),
                        "target": self.short(target),
                        "raw": ref["raw"],
                        "status": status,
                    }
                )
        return {
            "problems": problems,
            "anchored": len(anchored),
            "literal_checks": literal_checks,
            "edges": edges,
            "references": consumed_refs,
        }

    # -- SMT-LIB emission --------------------------------------------------

    def closure(self, roots: set[str]) -> tuple[list[str], set[str]]:
        needed: set[str] = set()
        stack = list(roots)
        while stack:
            name = stack.pop()
            if name in needed:
                continue
            needed.add(name)
            if name in self.exprs:
                stack.extend(self.deps(name))
        return [name for name in self.order if name in needed], needed

    def emit_obligation(self, obligation: dict[str, Any]) -> str:
        copies = obligation.get("copies") or [""]
        goal = parse_sexpr(obligation["assert"])
        lines = [
            f"; {obligation['id']} for {self.data['id']} ({obligation['expected']}).",
            ";",
            f"; Generated by `python3 scripts/rules_ir.py {self.path.relative_to(ROOT)}`; do not edit.",
            f"; Source: {self.lifted['section']['citation']}, {self.lifted['source']['edition']}",
            f"; (current through {self.lifted['source']['current_through']}), lifted by scripts/uscode_lift.py.",
            ";",
        ]
        for line in wrap(obligation["question"], 76):
            lines.append(f"; {line}")
        lines.append(";")
        lines.append("; Provisions:")
        for provision in obligation["provisions"]:
            node = self.provisions[self.pid(provision)]
            lines.append(f"; - {node['citation']}")
        lines.append(f"(set-logic {obligation.get('logic', 'QF_LIA')})")

        roots = {symbol for symbol in symbols(goal)}
        base_roots = set()
        for root in roots:
            for prefix in copies:
                if prefix and root.startswith(prefix):
                    base_roots.add(root[len(prefix):])
                    break
            else:
                base_roots.add(root)
        ordered, needed = self.closure(base_roots)
        constraint_symbols = set()
        for constraint in self.constraints:
            constraint_symbols |= symbols(constraint)
        fact_names = [name for name in self.facts if name in needed or name in constraint_symbols]
        for prefix in copies:
            mapping = {
                name: prefix + name
                for name in list(self.facts) + list(self.predicates) + list(self.implementations)
            }
            for name in fact_names:
                lines.append(f"(declare-const {prefix}{name} {self.facts[name]['sort']})")
            for name in fact_names:
                domain = self.facts[name].get("domain")
                if domain:
                    lines.append(
                        f"(assert (and (<= {domain['min']} {prefix}{name}) "
                        f"(<= {prefix}{name} {domain['max']})))"
                    )
            for constraint in self.constraints:
                lines.append(f"(assert {render_sexpr(rename(constraint, mapping))})")
            for name in [n for n in self.constants if n in needed]:
                if prefix == copies[0]:
                    const = self.constants[name]
                    lines.append(f"(define-fun {name} () {const['sort']} {render_sexpr(const['value'])})")
            for name in ordered:
                if name in self.exprs:
                    sort = self.sort_of(name)
                    expr = rename(self.exprs[name], mapping)
                    if sort == "Int" and has_case_split(expr):
                        decls, clauses = lift_int(expr, prefix + name, [])
                        lines.append(f"(declare-const {prefix}{name} Int)")
                        for decl in decls:
                            lines.append(f"(declare-const {decl} Int)")
                        for clause in clauses:
                            lines.append(f"(assert {render_sexpr(clause)})")
                    else:
                        lines.append(f"(define-fun {prefix}{name} () {sort} {render_sexpr(expr)})")
        lines.append(f"(assert {render_sexpr(goal)})")
        lines.append("(check-sat)")
        return "\n".join(lines) + "\n"


def has_case_split(expr: SExpr) -> bool:
    if isinstance(expr, list):
        return expr[0] in ("ite", "max") or any(has_case_split(item) for item in expr[1:])
    return False


def lift_int(expr: SExpr, target: str, path: list[SExpr]) -> tuple[list[str], list[SExpr]]:
    """Define the Int constant `target` by clauses instead of an Int-valued term.

    `(ite c a b)` becomes `c => target = a` and `not c => target = b` (with the
    enclosing path conditions), and `(max t1 ... tn)` becomes fresh constants
    `target__k = tk` with `target >= target__k` for every k and
    `target = target__1 or ... or target = target__n`. The path conditions
    partition each case split, so the clauses define `target` totally and
    uniquely; the obligation stays Boolean structure over linear atoms, the
    fragment Axeyum's checked lazy-arithmetic refutation covers.
    """

    def guarded(clause: SExpr) -> SExpr:
        if not path:
            return clause
        condition = path[0] if len(path) == 1 else ["and", *path]
        return ["=>", condition, clause]

    if isinstance(expr, list) and expr[0] == "ite":
        then_decls, then_clauses = lift_int(expr[2], target, path + [expr[1]])
        else_decls, else_clauses = lift_int(expr[3], target, path + [["not", expr[1]]])
        return then_decls + else_decls, then_clauses + else_clauses
    if isinstance(expr, list) and expr[0] == "max":
        decls: list[str] = []
        clauses: list[SExpr] = []
        parts = []
        for index, arg in enumerate(expr[1:], start=1):
            part = f"{target}__{index}"
            parts.append(part)
            decls.append(part)
            sub_decls, sub_clauses = lift_int(arg, part, path)
            decls.extend(sub_decls)
            clauses.extend(sub_clauses)
            clauses.append(guarded([">=", target, part]))
        clauses.append(guarded(["or", *[["=", target, part] for part in parts]]))
        return decls, clauses
    if has_case_split(expr):
        raise RulesError(f"case split nested inside an Int term is not supported: {render_sexpr(expr)}")
    return [], [guarded(["=", target, expr])]


def wrap(text: str, width: int) -> list[str]:
    words = text.split()
    lines: list[str] = []
    current = ""
    for word in words:
        if current and len(current) + 1 + len(word) > width:
            lines.append(current)
            current = word
        else:
            current = f"{current} {word}".strip()
    if current:
        lines.append(current)
    return lines


def compile_rules(rules: Rules) -> tuple[dict[str, str], dict[str, Any]]:
    trace = rules.trace()
    if trace["problems"]:
        raise RulesError("traceability check failed:\n  " + "\n  ".join(trace["problems"]))
    outputs: dict[str, str] = {}
    obligations = []
    for obligation in rules.data["obligations"]:
        rel = f"smt2/{obligation['id']}.smt2"
        outputs[rel] = rules.emit_obligation(obligation)
        record = {
            "id": obligation["id"],
            "expected": obligation["expected"],
            "smt2": rel,
            "provisions": obligation["provisions"],
        }
        witness = obligation.get("witness")
        if witness is not None:
            env = rules.evaluate(witness)
            goal = parse_sexpr(obligation["assert"])
            if not eval_sexpr(goal, env):
                raise RulesError(f"{obligation['id']}: recorded witness does not satisfy the goal")
            record["witness"] = witness
            record["witness_outputs"] = {
                name: env[name] for name in obligation.get("report", []) if name in env
            }
        obligations.append(record)
    compiled = {
        "schema": "axeyum.rules-ir.compiled/v1",
        "generated_by": "python3 scripts/rules_ir.py",
        "rules": str(rules.path.relative_to(ROOT)),
        "lifted": rules.data["lifted"],
        "source_sha256": rules.lifted["source"]["sha256"],
        "counts": {
            "facts": len(rules.facts),
            "predicates": len(rules.predicates),
            "implementations": len(rules.implementations),
            "anchored_quotes": trace["anchored"],
            "literal_checks": trace["literal_checks"],
            "dependency_edges": len(trace["edges"]),
            "cross_provision_edges": sum(
                1 for edge in trace["edges"] if edge["justification"] != "structure"
            ),
            "references_checked": len(trace["references"]),
            "obligations": len(obligations),
        },
        "dependency_edges": trace["edges"],
        "references": trace["references"],
        "obligations": obligations,
    }
    outputs["compiled.json"] = json.dumps(compiled, indent=2, ensure_ascii=False) + "\n"
    if "source_extract" in rules.data:
        outputs["source.md"] = render_source(rules)
    return outputs, compiled


def render_source(rules: Rules) -> str:
    """Render the modeled provisions verbatim from the lifted section."""
    lifted = rules.lifted
    lines = [
        f"# {lifted['section']['citation']}: {lifted['section']['heading']} (excerpt)",
        "",
        f"Generated by `python3 scripts/rules_ir.py {rules.path.relative_to(ROOT)}` from",
        f"[`{rules.data['lifted']}`](../../../../{rules.data['lifted']}); do not edit.",
        "",
        f"Text: {lifted['source']['edition']}, current through",
        f"{lifted['source']['current_through']}, published by the {lifted['source']['publisher']}.",
        "The U.S. Code is a work of the United States Government and is not subject to",
        "copyright. Footnote markers are removed; the editorial footnotes follow the",
        "provision they annotate. This is the statute text the rule model cites, not",
        "legal advice.",
        "",
    ]
    for extract in rules.data["source_extract"]:
        lines.append(f'<a id="{extract["anchor"]}"></a>')
        lines.append("")
        lines.append(f"## {extract['label']}")
        lines.append("")
        if extract.get("note"):
            lines.append(extract["note"])
            lines.append("")
        for root in extract["provisions"]:
            root_id = rules.pid(root)
            root_depth = root_id.count("/")
            for node in lifted["provisions"]:
                if node["id"] != root_id and not node["id"].startswith(root_id + "/"):
                    continue
                indent = "  " * (node["id"].count("/") - root_depth)
                text = node["text"] or "(enumerated below)"
                lines.append(f"{indent}- **({node['enumerator']})** {text}")
                for note in node["footnotes"]:
                    lines.append(f"{indent}  - *Editorial note:* {note}")
            node = rules.provisions[root_id]
            if node.get("continuation"):
                lines.append(f"- {node['continuation']}")
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("rules", type=Path)
    parser.add_argument("--check", action="store_true", help="fail if generated files are stale")
    args = parser.parse_args()
    try:
        rules = Rules(args.rules.resolve())
        outputs, compiled = compile_rules(rules)
    except RulesError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    stale = []
    for rel, text in outputs.items():
        path = rules.dir / rel
        if args.check:
            if not path.exists() or path.read_text(encoding="utf-8") != text:
                stale.append(rel)
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text, encoding="utf-8")
    if stale:
        print(f"error: stale generated files: {', '.join(stale)}", file=sys.stderr)
        return 1
    counts = compiled["counts"]
    print(
        f"compiled {rules.data['id']}: {counts['predicates']} predicates, "
        f"{counts['anchored_quotes']} anchors verified, {counts['literal_checks']} literals matched, "
        f"{counts['cross_provision_edges']} cross-provision dependencies justified, "
        f"{counts['references_checked']} statute references accounted for, "
        f"{counts['obligations']} obligations"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

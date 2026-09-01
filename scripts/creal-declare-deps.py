#!/usr/bin/env python3
"""Measure `creal.rs`'s real `declare_*` dependency graph from the source.

WHY THIS EXISTS. `docs/research/11-design-review/2026-08-27-architecture-review.md`
§1 measures the failure class: `creal.rs` fuses the name registry, the
`CRealPrelude` field struct, the build ORDER and dispatch, and four lanes in
one day hit `UnknownConst` on a name plainly visible in source because a
`declare_*` ran before the step that declares what it references.

Lane `creal-steps` landed the level-1 fix: a `STEPS` table where each entry
names its `requires`/`provides` as `fn(CRealPrelude) -> NameId` accessors, and
`validate_step_order` checks the hand-written order is a valid topological
order for THAT TABLE. What nothing checks is whether the table matches the
code. `requires`/`provides` were extracted once, by a throwaway script that was
deliberately not committed, and every declaration added since has had to
maintain them by hand. A `requires` entry that is missing costs nothing while
the order happens to be right and silently disarms the preflight the moment it
is not -- which is exactly the shape of gate CLAUDE.md says is worse than no
gate at all.

So this script re-derives the graph FROM THE SOURCE and compares. It is
re-runnable by construction: nothing here is a recorded constant, and the whole
analysis is one pass over `creal.rs` plus `creal/*.rs`.

WHAT IT MEASURES, per top-level `declare_*` reachable from a `STEPS` entry:

  provides  the `CRealPrelude` fields the step's transitive call graph
            DECLARES -- `name: p.foo` (and the `name,` field-init shorthand)
            inside a `Declaration` literal, `add_inductive(p.foo, ..)` with its
            constructors, and the kernel-generated recursor attributed to its
            inductive.
  requires  the `CRealPrelude` fields it READS -- every other `p.foo` in that
            same transitive closure.

The one subtlety that a naive `p\\.(\\w+)` scan gets WRONG, and which the
`creal-steps` extraction called out as the generalization it had to make by
hand: a helper that declares under a `name: NameId` PARAMETER
(`constant`, `projection`, `declare_operation`, ..., and the `name,`
field-init shorthand used ~40 times in `integral.rs`). At such a call site
`p.foo` is a WRITE, not a read, and counting it as a read makes the step
depend on its own output. This script resolves those positionally: a function
(or a `let f = |name: NameId, ..|` closure) that declares under parameter `k`
turns every call site's `k`-th argument into a write attributed to the CALLER.

Usage:
    python3 scripts/creal-declare-deps.py            # rewrite the artifact + report
    python3 scripts/creal-declare-deps.py --check    # gate: fail if stale
    python3 scripts/creal-declare-deps.py --report   # report only, no write

Exit status:
    0  artifact written (or, with --check, up to date) and no finding
    1  --check and the artifact is stale
    2  a measured DEFECT in the STEPS table (see --strict)

`--strict` is what makes the exit status depend on the finding rather than on
whether the script ran: without it a table defect is reported and the exit is
still 0, which is how a checker learns to be ignored.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC = ROOT / "crates" / "axeyum-lean-kernel" / "src"
CREAL = SRC / "creal.rs"
CREAL_DIR = SRC / "creal"
ARTIFACT = ROOT / "artifacts" / "refactor" / "creal-declare-deps.json"

# Files that declare nothing the build order runs: the sharded inventory
# mirror and the per-module test modules.
SKIP = re.compile(r"(_tests\.rs$)|(^inventory\.rs$)")


# ---------------------------------------------------------------------------
# Lexing: strip what a regex must not see
# ---------------------------------------------------------------------------


def strip_noise(text: str, keep_strings: bool = False) -> str:
    """Blank out comments, string/char literals and lifetimes, in place.

    Offsets are PRESERVED (every removed byte becomes a space, newlines kept)
    so a match in the stripped text still names a real line in the original.
    That matters: this module's doc comments are full of `p.foo` and
    ``name: p.bar`` in prose, and `creal.rs` has ~4,900 comment lines. A scan
    that reads them attributes dependencies to whoever documented them.

    `keep_strings` blanks comments only. The two tables this script READS --
    `intern_names` and `STEPS` -- carry their content in string literals
    (`kernel.name_str(creal, "Within")`, `label: "declare_carrier"`), so
    parsing them from the fully-stripped text silently yields an EMPTY
    registry and ZERO steps while every downstream finding still prints
    cleanly. That is exactly the shape of vacuous pass CLAUDE.md warns about,
    and it is why `main` asserts both tables are non-empty.
    """
    out = list(text)
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == "/" and i + 1 < n and text[i + 1] == "/":
            j = text.find("\n", i)
            j = n if j < 0 else j
            for k in range(i, j):
                out[k] = " "
            i = j
        elif c == "/" and i + 1 < n and text[i + 1] == "*":
            depth, j = 1, i + 2
            while j < n and depth:
                if text[j : j + 2] == "/*":
                    depth += 1
                    j += 2
                elif text[j : j + 2] == "*/":
                    depth -= 1
                    j += 2
                else:
                    j += 1
            for k in range(i, j):
                if out[k] != "\n":
                    out[k] = " "
            i = j
        elif c == '"':
            j = i + 1
            while j < n:
                if text[j] == "\\":
                    j += 2
                    continue
                if text[j] == '"':
                    j += 1
                    break
                j += 1
            if not keep_strings:
                for k in range(i, j):
                    if out[k] != "\n":
                        out[k] = " "
            i = j
        elif c == "'":
            # A lifetime (`'a`, `'_`, `'static`) is not a char literal. Both
            # are harmless to blank, and telling them apart is not worth it.
            j = i + 1
            if j < n and text[j] == "\\":
                j += 2
                while j < n and text[j] != "'":
                    j += 1
                j += 1
            elif j + 1 < n and text[j + 1] == "'":
                j += 2
            else:
                while j < n and (text[j].isalnum() or text[j] == "_"):
                    j += 1
            for k in range(i, j):
                out[k] = " "
            i = j
        else:
            i += 1
    return "".join(out)


def match_brace(text: str, start: int, open_c: str = "{", close_c: str = "}") -> int:
    """Index just past the delimiter matching the one at `start`."""
    depth, i, n = 0, start, len(text)
    while i < n:
        if text[i] == open_c:
            depth += 1
        elif text[i] == close_c:
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1
    return n


def blank_test_modules(text: str) -> str:
    """Blank `#[cfg(test)] mod ... { .. }` bodies.

    Six `creal/*.rs` files carry inline test modules whose fixtures declare
    under names like `name_ok`/`name_bad`. Those are deliberate
    kernel-rejection controls, not build steps, and counting their writes
    inflates `provides` with declarations the build never makes.
    """
    out = list(text)
    for m in re.finditer(r"#\[cfg\(test\)\]", text):
        brace = text.find("{", m.end())
        if brace < 0:
            continue
        between = text[m.end() : brace]
        # Only a `mod … {` opens a block here. `#[cfg(test)] mod creal_tests;`
        # is a module DECLARATION and its next `{` is 7,000 lines away -- taking
        # it blanked `declare_constants` and 100+ other functions, which showed
        # up as `CReal.zero`/`CReal.one` being required by 115 steps and
        # provided by none.
        if "mod " not in between or ";" in between:
            continue
        end = match_brace(text, brace)
        for k in range(m.start(), end):
            if out[k] != "\n":
                out[k] = " "
    return "".join(out)


# ---------------------------------------------------------------------------
# The field registry: `intern_names`
# ---------------------------------------------------------------------------

FIELD_DECL = re.compile(r"^\s*pub ([a-z_][a-z_0-9]*): NameId,", re.M)


def struct_fields(clean: str) -> list[str]:
    """Every `NameId` field of `CRealPrelude`.

    `pub rat: RatPrelude` is deliberately NOT one: it is a whole sub-prelude
    built by `build_rat_prelude` before `creal` starts, so it is a dependency
    of the module rather than of any step, and counting it makes all 211 steps
    require something no step provides.
    """
    start = clean.index("pub struct CRealPrelude {")
    end = match_brace(clean, clean.index("{", start))
    return FIELD_DECL.findall(clean[start:end])


def field_names(clean: str) -> dict[str, str]:
    """Map each `CRealPrelude` field to the dotted name it interns.

    Parsed from `intern_names` rather than assumed from the field spelling:
    315 of 447 `CReal` names carry an underscore and 225 an internal capital,
    so `equiv_refl` is `CReal.Equiv.refl` and no naming rule recovers that.
    """
    start = clean.index("fn intern_names(")
    end = match_brace(clean, clean.index("{", start))
    body = clean[start:end]

    local: dict[str, str] = {}
    for m in re.finditer(
        r"let ([a-z_][a-z_0-9]*) = kernel\s*\.\s*name_str\(\s*([a-z_][a-z_0-9]*)\s*,\s*\"([^\"]+)\"\s*\)",
        body,
    ):
        var, parent, leaf = m.groups()
        local[var] = leaf if parent == "anon" else f"{local.get(parent, parent)}.{leaf}"

    names: dict[str, str] = {}
    for m in re.finditer(
        r"([a-z_][a-z_0-9]*):\s*kernel\s*\.\s*name_str\(\s*([a-z_][a-z_0-9]*)\s*,\s*\"([^\"]+)\"\s*\)",
        body,
    ):
        field, parent, leaf = m.groups()
        names[field] = leaf if parent == "anon" else f"{local.get(parent, parent)}.{leaf}"
    # Field-init shorthand (`creal,`) reuses a local binding of the same name.
    for field, dotted in local.items():
        names.setdefault(field, dotted)
    return names


# ---------------------------------------------------------------------------
# The STEPS table
# ---------------------------------------------------------------------------

STEP_ENTRY = re.compile(
    r"BuildStep\s*\{\s*label:\s*\"([^\"]+)\"\s*,\s*"
    r"requires:\s*&\[(.*?)\]\s*,\s*"
    r"provides:\s*&\[(.*?)\]\s*,\s*"
    r"run:\s*([A-Za-z_0-9:]+)\s*,",
    re.S,
)
ACCESSOR = re.compile(r"p\.([a-z_][a-z_0-9]*)")


def steps_table(clean: str) -> list[dict]:
    start = clean.index("const STEPS: &[BuildStep] = &[")
    end = match_brace(clean, clean.index("[", clean.index("=", start)), "[", "]")
    body = clean[start:end]
    out = []
    for m in STEP_ENTRY.finditer(body):
        label, requires, provides, run = m.groups()
        out.append(
            {
                "label": label,
                "run": run,
                "declared_requires": sorted(set(ACCESSOR.findall(requires))),
                "declared_provides": sorted(set(ACCESSOR.findall(provides))),
            }
        )
    return out


# ---------------------------------------------------------------------------
# Function index and call graph
# ---------------------------------------------------------------------------

FN_DEF = re.compile(r"\bfn\s+([a-z_][a-z_0-9]*)\s*(?:<[^>]*>)?\s*\(")
CLOSURE_DEF = re.compile(r"\blet\s+([a-z_][a-z_0-9]*)\s*=\s*(?:move\s+)?\|")
# A call, but NOT a method call: `d.apply(..)` must not resolve to a free
# function named `apply`. The negative lookbehind on `.` is what stops it.
CALL = re.compile(r"(?<![.\w])(?:([a-z_][a-z_0-9]*)::)?([a-z_][a-z_0-9]*)\s*\(")
USE_ITEM = re.compile(r"\buse\s+super::(?:([a-z_][a-z_0-9]*)::)?(\{[^}]*\}|[a-z_][a-z_0-9]*)\s*;")


def import_map(clean: str) -> dict[str, tuple[str, str]]:
    """Bare name -> `(module, item)` for this file's `use super::…` imports.

    A bare call in a `creal/` module can name a function from a SIBLING module
    or from `creal.rs` itself, and only the `use` line says which. Resolving
    bare names by "the unique function with that name anywhere in `creal/`"
    instead -- which is the obvious shortcut -- produces edges that do not
    exist: `creal.rs`'s `six_term_bound` calls `rsum`, imported from
    `crate::rat_prelude::group`, and `integral.rs` happens to define its own
    `rsum`, so the shortcut made `declare_transitivity` depend on the RIEMANN
    SUM. That single false edge put 21 spurious `out_of_order` violations in
    the first run of this script.
    """
    out: dict[str, tuple[str, str]] = {}
    for m in USE_ITEM.finditer(clean):
        module, items = m.group(1), m.group(2)
        names = items.strip("{}").split(",") if items.startswith("{") else [items]
        for entry in names:
            entry = entry.strip()
            if not entry:
                continue
            parts = entry.split(" as ")
            original = parts[0].strip()
            alias = parts[-1].strip()
            # A nested `use super::{ convergence::foo, bar }` entry carries its
            # own module.
            inner_module = module
            if "::" in original:
                inner_module, _, original = original.rpartition("::")
                inner_module = inner_module.split("::")[-1]
            if not re.fullmatch(r"[a-z_][a-z_0-9]*", original):
                continue
            out[alias] = (inner_module or "creal", original)
    return out


def split_args(text: str) -> list[str]:
    """Split a paren group's contents on TOP-LEVEL commas."""
    parts, depth, start = [], 0, 0
    for i, c in enumerate(text):
        if c in "([{<":
            depth += 1
        elif c in ")]}>":
            depth -= 1
        elif c == "," and depth == 0:
            parts.append(text[start:i])
            start = i + 1
    parts.append(text[start:])
    return [p.strip() for p in parts if p.strip()]


def param_names(sig: str) -> list[str]:
    """Parameter names, in order, from a signature's paren contents."""
    out = []
    for arg in split_args(sig):
        head = arg.split(":", 1)[0].strip()
        head = head.removeprefix("mut ").strip()
        out.append(head)
    return out


def nameid_params(sig: str) -> set[str]:
    return {
        m.group(1)
        for m in re.finditer(r"\b(?:mut\s+)?([a-z_][a-z_0-9]*)\s*:\s*NameId\b", sig)
    }


class Item:
    """A function or closure: its body span, parameters, and what it writes."""

    def __init__(self, module: str, name: str, params: list[str], nameids: set[str], body: str):
        self.module = module
        self.name = name
        self.params = params
        self.nameids = nameids
        self.body = body
        self.reads: set[str] = set()
        self.writes: set[str] = set()
        # Parameter indices this item declares under, so a call site can
        # attribute the field it passes there.
        self.declares_at: set[int] = set()
        self.calls: set[tuple[str, str]] = set()


def index_closures(module: str, body: str) -> list[Item]:
    """The `let f = |..| { .. }` closures defined directly in `body`.

    Closures are FUNCTION-LOCAL and their names repeat: `trig_fn.rs` defines
    `motive`, `step` and `induct_ty` once per `declare_*`. Indexing them
    module-globally keeps only the last of each and makes every earlier
    `declare_*` appear to call it -- which put four spurious `out_of_order`
    violations in `trig_fn` and one in `supremum`. So they are resolved only
    from inside the function that defines them, and never enter the
    module-level index.
    """
    items: list[Item] = []
    for m in CLOSURE_DEF.finditer(body):
        bar = body.index("|", m.end() - 1)
        close = body.find("|", bar + 1)
        if close < 0:
            continue
        sig = body[bar + 1 : close]
        rest = body[close + 1 :]
        offset = len(rest) - len(rest.lstrip())
        rest = rest.lstrip()
        if rest.startswith("->"):
            brace_rel = rest.find("{")
        else:
            brace_rel = 0 if rest.startswith("{") else -1
        if brace_rel < 0:
            continue
        brace = close + 1 + offset + brace_rel
        end = match_brace(body, brace)
        items.append(Item(module, m.group(1), param_names(sig), nameid_params(sig), body[brace:end]))
    return items


def index_items(module: str, clean: str) -> list[Item]:
    items: list[Item] = []
    for m in FN_DEF.finditer(clean):
        open_paren = clean.index("(", m.end() - 1)
        close_paren = match_brace(clean, open_paren, "(", ")")
        sig = clean[open_paren + 1 : close_paren - 1]
        brace = clean.find("{", close_paren)
        semi = clean.find(";", close_paren)
        if brace < 0 or (0 <= semi < brace):
            continue  # a trait signature, not a definition
        end = match_brace(clean, brace)
        items.append(
            Item(module, m.group(1), param_names(sig), nameid_params(sig), clean[brace:end])
        )
    return items


NAME_FIELD = re.compile(r"\bname:\s*([A-Za-z_0-9.]+)\s*,")
NAME_SHORTHAND = re.compile(r"^\s*name\s*,\s*$", re.M)
ADD_INDUCTIVE = re.compile(r"\badd_inductive\s*\(")
# Declaring sinks OUTSIDE `creal/`, so the call graph cannot reach them: the
# `NatOps` dev helpers, each taking the declared name first.
EXTERNAL_SINK = re.compile(r"\.\s*(?:theorem|try_theorem|declare_theorem)\s*\(")


def direct_writes(item: Item, fields: set[str]) -> tuple[set[str], set[int], list[str]]:
    """Fields this item declares under a literal, and the parameter positions
    it declares under.

    Returns `(literal_writes, declaring_param_indices, inductive_field_names)`.
    """
    writes: set[str] = set()
    at: set[int] = set()
    inductives: list[str] = []

    def note(expr: str) -> None:
        expr = expr.strip()
        if expr.startswith("p.") and expr[2:] in fields:
            writes.add(expr[2:])
        elif expr in item.nameids and expr in item.params:
            at.add(item.params.index(expr))
        elif re.fullmatch(r"[a-z_][a-z_0-9]*", expr):
            # A LOCAL binding chosen by a branch, not a parameter:
            #     let name = if join { p.uniformly_continuous_max }
            #                else    { p.uniformly_continuous_min };
            # Both arms are declared by this function, so every `p.foo` in the
            # binding's initializer is a write. Missing this made
            # `ivt_boundary::declare_ivt_boundary` require two names nothing
            # in the tree provides.
            for binding in re.finditer(rf"\blet\s+{re.escape(expr)}\s*=", item.body):
                tail = item.body[binding.end() :]
                depth, cut = 0, len(tail)
                for index, char in enumerate(tail):
                    if char in "([{":
                        depth += 1
                    elif char in ")]}":
                        depth -= 1
                    elif char == ";" and depth == 0:
                        cut = index
                        break
                for field in ACCESSOR.findall(tail[:cut]):
                    if field in fields:
                        writes.add(field)

    for m in NAME_FIELD.finditer(item.body):
        note(m.group(1))
    if NAME_SHORTHAND.search(item.body):
        if "name" in item.nameids and "name" in item.params:
            at.add(item.params.index("name"))
        else:
            note("name")

    for m in EXTERNAL_SINK.finditer(item.body):
        open_paren = item.body.index("(", m.end() - 1)
        close_paren = match_brace(item.body, open_paren, "(", ")")
        args = split_args(item.body[open_paren + 1 : close_paren - 1])
        if args:
            note(args[0])

    for m in ADD_INDUCTIVE.finditer(item.body):
        open_paren = item.body.index("(", m.end() - 1)
        close_paren = match_brace(item.body, open_paren, "(", ")")
        args = split_args(item.body[open_paren + 1 : close_paren - 1])
        if not args:
            continue
        note(args[0])
        if args[0].startswith("p."):
            inductives.append(args[0][2:])
        for ctor in re.finditer(r"\(\s*(p\.[a-z_][a-z_0-9]*)\s*,", args[-1]):
            note(ctor.group(1))
    return writes, at, inductives


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="fail if the artifact is stale")
    ap.add_argument("--report", action="store_true", help="print the report, write nothing")
    ap.add_argument(
        "--strict",
        action="store_true",
        help="exit 2 when the measured graph contradicts the STEPS table",
    )
    ap.add_argument(
        "--self-check",
        action="store_true",
        help="positive control: permute one step before its provider and require the scan to fire",
    )
    args = ap.parse_args()

    creal_raw = CREAL.read_text()
    blanked = blank_test_modules(creal_raw)
    clean = strip_noise(blanked)
    # `intern_names` and `STEPS` carry their content in string literals, so
    # they are read from a comments-only strip. See `strip_noise`.
    tables = strip_noise(blanked, keep_strings=True)

    fields = struct_fields(clean)
    field_set = set(fields)
    dotted = field_names(tables)
    steps = steps_table(tables)

    # Positive controls: each of the three parses below has a failure mode
    # that produces a clean, entirely wrong report rather than an error.
    if not fields:
        sys.exit("creal-declare-deps: parsed 0 CRealPrelude fields")
    if not dotted:
        sys.exit("creal-declare-deps: parsed 0 field names from intern_names")
    if not steps:
        sys.exit("creal-declare-deps: parsed 0 STEPS entries")
    unnamed = sorted(set(fields) - set(dotted) - {"rat"})
    if unnamed:
        sys.exit(f"creal-declare-deps: {len(unnamed)} field(s) unmapped: {unnamed[:5]}")

    # Index every non-test creal source.
    sources = {"creal": clean}
    for path in sorted(CREAL_DIR.glob("*.rs")):
        if SKIP.search(path.name):
            continue
        sources[path.stem] = strip_noise(blank_test_modules(path.read_text()))

    items: dict[tuple[str, str], Item] = {}
    imports: dict[str, dict[str, tuple[str, str]]] = {}
    for module, text in sources.items():
        imports[module] = import_map(text)
        for item in index_items(module, text):
            items[(module, item.name)] = item

    # Pass 1: literal writes and declaring parameter positions.
    recursor_of: dict[str, str] = {}
    for field, name in dotted.items():
        if name.endswith(".rec"):
            recursor_of[name[: -len(".rec")]] = field
    def note_inductives(item: Item, inductives: list[str]) -> None:
        for ind in inductives:
            rec = recursor_of.get(dotted.get(ind, ""))
            if rec:
                item.writes.add(rec)

    local_write_spans: dict[tuple[str, str], set[tuple[int, int]]] = {}
    for key, item in items.items():
        writes, at, inductives = direct_writes(item, field_set)
        item.writes |= writes
        item.declares_at |= at
        note_inductives(item, inductives)

        # A closure declaring under a `name: NameId` parameter -- `constant`
        # in `declare_constants`, and the `name,` shorthand used throughout
        # `integral.rs`. Its call sites are in THIS function's body, so the
        # field it passes there is a write by this function, not a read.
        spans: set[tuple[int, int]] = set()
        for closure in index_closures(item.module, item.body):
            c_writes, c_at, c_inductives = direct_writes(closure, field_set)
            item.writes |= c_writes
            note_inductives(item, c_inductives)
            if not c_at:
                continue
            for call in re.finditer(rf"(?<![.\w]){re.escape(closure.name)}\s*\(", item.body):
                open_paren = item.body.index("(", call.end() - 1)
                close_paren = match_brace(item.body, open_paren, "(", ")")
                inner = item.body[open_paren + 1 : close_paren - 1]
                base, cursor = open_paren + 1, 0
                for index, arg in enumerate(split_args(inner)):
                    found = inner.find(arg, cursor)
                    if found >= 0:
                        cursor = found + len(arg)
                    if index in c_at and arg.startswith("p.") and arg[2:] in field_set:
                        item.writes.add(arg[2:])
                        if found >= 0:
                            spans.add((base + found, base + found + len(arg)))
        local_write_spans[key] = spans

    # Pass 2: call graph, plus call-site attribution of parameter writes.
    #
    # A `p.foo` passed at a position the callee declares under is a WRITE by
    # the caller. Recorded as `write_offsets` so pass 3 can subtract exactly
    # those occurrences from the read scan -- without that subtraction every
    # such step reads what it provides and the graph grows a self-loop.
    write_spans: dict[tuple[str, str], set[tuple[int, int]]] = {
        k: set(local_write_spans.get(k, ())) for k in items
    }
    for key, item in items.items():
        for m in CALL.finditer(item.body):
            qualifier, name = m.group(1), m.group(2)
            if name in ("fn", "if", "for", "while", "match", "return"):
                continue
            target = None
            if qualifier:
                target = items.get((qualifier, name))
            elif (item.module, name) in items:
                target = items[(item.module, name)]
            else:
                target = items.get(imports[item.module].get(name, ("", "")))
            if target is None:
                continue
            item.calls.add((target.module, target.name))
            if not target.declares_at:
                continue
            open_paren = item.body.index("(", m.end() - 1)
            close_paren = match_brace(item.body, open_paren, "(", ")")
            inner = item.body[open_paren + 1 : close_paren - 1]
            base = open_paren + 1
            cursor = 0
            for index, arg in enumerate(split_args(inner)):
                found = inner.find(arg, cursor)
                if found >= 0:
                    cursor = found + len(arg)
                if index in target.declares_at and arg.startswith("p."):
                    field = arg[2:]
                    if field in field_set:
                        item.writes.add(field)
                        if found >= 0:
                            write_spans[key].add((base + found, base + found + len(arg)))

    # Pass 3: reads -- every other `p.foo`.
    for key, item in items.items():
        spans = write_spans[key]
        for m in ACCESSOR.finditer(item.body):
            if m.group(1) not in field_set:
                continue
            if any(lo <= m.start() < hi for lo, hi in spans):
                continue
            item.reads.add(m.group(1))

    # Transitive closure per step.
    def closure(start: Item) -> set[tuple[str, str]]:
        seen, stack = {(start.module, start.name)}, [(start.module, start.name)]
        while stack:
            key = stack.pop()
            for nxt in items[key].calls:
                if nxt not in seen:
                    seen.add(nxt)
                    stack.append(nxt)
        return seen

    measured: list[dict] = []
    for index, step in enumerate(steps):
        run = step["run"]
        module, _, fn = run.rpartition("::")
        key = (module or "creal", fn)
        if key not in items:
            measured.append({**step, "index": index, "error": f"no such function: {run}"})
            continue
        reach = closure(items[key])
        provides: set[str] = set()
        reads: set[str] = set()
        for k in reach:
            provides |= items[k].writes
            reads |= items[k].reads
        measured.append(
            {
                **step,
                "index": index,
                "module": module or "creal",
                "reachable_fns": len(reach),
                "measured_provides": sorted(provides),
                "measured_requires": sorted(reads - provides),
            }
        )

    # ---- findings ----------------------------------------------------------
    provider_of: dict[str, list[int]] = {}
    for step in measured:
        for field in step.get("measured_provides", []):
            provider_of.setdefault(field, []).append(step["index"])

    def scan_order(sequence: list[dict]) -> list[dict]:
        """Every `measured_requires` entry not provided by a strictly earlier
        step in `sequence` -- the same check `validate_step_order` performs,
        against the MEASURED graph rather than the hand-written table."""
        found = []
        seen: set[str] = set()
        for step in sequence:
            for field in step.get("measured_requires", []):
                if field in seen:
                    continue
                providers = provider_of.get(field, [])
                found.append(
                    {
                        "consumer_index": step["index"],
                        "consumer_label": step["label"],
                        "missing_field": field,
                        "missing_name": dotted.get(field, field),
                        "providers": providers,
                        "kind": "unprovided" if not providers else "out_of_order",
                    }
                )
            seen |= set(step.get("measured_provides", []))
        return found

    order_violations = scan_order(measured)

    if args.self_check:
        # POSITIVE CONTROL. "0 violations" is also what a scan that examines
        # nothing prints, so the clean result above is not evidence on its
        # own. Move one step before a step it demonstrably depends on and
        # require that the same scan fires.
        control = None
        for position, step in enumerate(measured):
            for field in step.get("measured_requires", []):
                providers = [i for i in provider_of.get(field, []) if i < step["index"]]
                if providers:
                    control = (position, providers[-1], field)
                    break
            if control:
                break
        if control is None:
            print("SELF_CHECK|FAIL|no step depends on an earlier step", file=sys.stderr)
            return 2
        position, provider_index, field = control
        permuted = list(measured)
        moved = permuted.pop(position)
        permuted.insert(next(i for i, s in enumerate(permuted) if s["index"] == provider_index), moved)
        fired = scan_order(permuted)
        ok = any(v["missing_field"] == field for v in fired)
        print(
            f"SELF_CHECK|{'PASS' if ok else 'FAIL'}|moved '{moved['label']}' before its "
            f"provider of `{dotted.get(field, field)}`|violations={len(fired)}"
        )
        if not ok:
            return 2

    # Under-declared `requires`: the table promises less than the code needs.
    table_gaps = []
    for step in measured:
        missing_req = sorted(set(step.get("measured_requires", [])) - set(step["declared_requires"]))
        missing_prov = sorted(
            set(step.get("measured_provides", [])) - set(step["declared_provides"])
        )
        extra_prov = sorted(set(step["declared_provides"]) - set(step.get("measured_provides", [])))
        if missing_req or missing_prov or extra_prov:
            table_gaps.append(
                {
                    "index": step["index"],
                    "label": step["label"],
                    "requires_missing_from_table": missing_req,
                    "provides_missing_from_table": missing_prov,
                    "provides_in_table_not_measured": extra_prov,
                }
            )

    consumed: set[str] = set()
    for step in measured:
        consumed |= set(step.get("measured_requires", []))
    leaves = [
        {"index": s["index"], "label": s["label"], "module": s.get("module")}
        for s in measured
        if s.get("measured_provides") and not (set(s["measured_provides"]) & consumed)
    ]

    per_module: dict[str, list[str]] = {}
    for step in measured:
        per_module.setdefault(step.get("module", "?"), []).append(step["label"])
    multi_entry = {m: labels for m, labels in per_module.items() if len(labels) > 1}

    duplicate_providers = {
        dotted.get(f, f): idx for f, idx in provider_of.items() if len(idx) > 1
    }

    document = {
        "schema": "creal-declare-deps/v1",
        "produced_by": "scripts/creal-declare-deps.py",
        "source": {
            "creal_rs_lines": creal_raw.count("\n") + 1,
            "creal_prelude_fields": len(fields),
            "steps": len(steps),
            "modules_indexed": len(sources),
            "functions_indexed": len(items),
        },
        "field_names": dotted,
        "steps": measured,
        "findings": {
            "linear_order_is_topological": not order_violations,
            "order_violations": order_violations,
            "table_gaps": table_gaps,
            "steps_with_no_dependents": leaves,
            "dispatch_entries_per_module": {m: len(v) for m, v in sorted(per_module.items())},
            "modules_with_multiple_dispatch_entries": multi_entry,
            "fields_provided_by_more_than_one_step": duplicate_providers,
        },
    }
    text = json.dumps(document, indent=2, sort_keys=True) + "\n"

    if args.check:
        if not ARTIFACT.exists() or ARTIFACT.read_text() != text:
            print(f"CREAL_DECLARE_DEPS|stale|{ARTIFACT.relative_to(ROOT)}", file=sys.stderr)
            return 1
    elif not args.report:
        ARTIFACT.parent.mkdir(parents=True, exist_ok=True)
        ARTIFACT.write_text(text)

    f = document["findings"]
    print(f"CREAL_DECLARE_DEPS|steps={len(steps)}|fields={len(fields)}|fns={len(items)}")
    print(f"  linear order is a valid topological order: {f['linear_order_is_topological']}")
    print(f"  order violations (measured graph):         {len(f['order_violations'])}")
    print(f"  steps whose table disagrees with the code: {len(f['table_gaps'])}")
    print(f"  steps with no dependents (leaves):         {len(f['steps_with_no_dependents'])}")
    print(f"  modules with >1 dispatch entry:            {len(f['modules_with_multiple_dispatch_entries'])}")
    print(f"  fields provided by >1 step:                {len(f['fields_provided_by_more_than_one_step'])}")

    if args.strict and (f["order_violations"] or f["table_gaps"]):
        print(
            "CREAL_DECLARE_DEPS|DEFECT|the STEPS table does not match the code",
            file=sys.stderr,
        )
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())

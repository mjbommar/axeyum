#!/usr/bin/env python3
"""How much code must be CORRECT for an admitted theorem to be true?

This project's identity is *"untrusted fast search, trusted small checking."*
Gödel's limit means some checker is believed rather than checked, so the whole
trust story reduces to one number: **how small is the thing that must be
right?** Before this script that number was eyeballed. The brief that
commissioned it said the trusted core was "roughly 9.4k lines" of
`crates/axeyum-lean-kernel/src/`, naming `tc.rs`, `inductive.rs`, `env.rs`,
`lib.rs` and `quotient.rs`, with `lean_pp.rs` / `lean_export.rs` as interop
"trusted only for the Lean crosscheck".

Measured here, the shape of that estimate is right and three of its details are
wrong:

* The trusted core is **5,129 lines of function bodies across 9 files** —
  244 of the crate's 794 functions, measured 2026-08-17 — not 9.4k, because
  whole files are not trusted, only the functions in them an admission path can
  actually reach. `tc.rs` contributes 1,644 of its 1,673 function-body lines
  (the file is 2,925 lines with doc comments and inline tests); `lib.rs`
  contributes 683 of 995 (file: 1,507); `lean_export.rs` 32 of 891 (file:
  1,292). The other 35 source files contribute **nothing**.
* **`lean_export.rs` is NOT interop-only.** `Kernel::is_k_like_inductive`
  (32 lines) lives there and is called from `k_like_major` -> `reduce_rec` ->
  `whnf` -> `def_eq`. K-like reduction is a *soundness-critical* iota rule:
  believing a family is K-like licenses reducing a recursor application whose
  major premise is not a constructor. It is on the trusted path, in the file
  nobody thought was.
* There are **four** admission gates, not three: `restore_nested_inductive_group`
  (`inductive.rs`) inserts declarations directly, after the nested-inductive
  expansion has been checked under a temporary name.

# How the trusted set is derived

Not from a list. From the only thing that can make a declaration exist:

    Environment::insert_unchecked   (env.rs, `pub(crate)`)

Every declaration that a third party ever sees came through that call. So:

1. Find every call site of it outside test code. The enclosing functions are
   the **admission gates** (guard A pins them; a new one fails the gate).
2. The trusted core is the forward call-graph closure from those gates.
   *Callers are deliberately not included*: that is the entire point of a
   kernel. A prelude, a solver, a reconstruction pass may be arbitrarily wrong;
   the gate re-checks. So `nat_prelude/` (16k lines) is content, not checker.
3. `insert_unchecked` being `pub(crate)` is what makes step 2 exhaustive —
   guard B checks that, and that no `&mut self` method of `Environment` is
   `pub`. Without it the closure would be a lower bound on nothing.

# Why the number is an UPPER bound

The call graph is built by a Rust-aware scanner (comments, string/char/raw
literals and `#[cfg(test)]` blocks are blanked; `impl` blocks give each `fn` an
owner type), and edges are resolved **conservatively**:

* `self.f(` / `Self::f(` -> `f` in the enclosing `impl` block's type.
* `T::f(` for a known impl type `T` -> every `f` in `impl … T`.
* bare `f(` -> every free (non-`impl`) `f`.
* `recv.f(` for any other receiver -> every `f` in any `impl T` where `T` is
  *named somewhere in the calling file*. This is the loose rule, and it is
  loose on purpose: it over-approximates.

Over-approximation is the safe direction for a trust claim — it can only make
the trusted core look bigger than it is. It is not free of blind spots, and the
honest list is: operator/trait dispatch (`Display`, `Index`) and function
values passed without a call (`map(Kernel::f)`) are missed. Neither carries an
accept/reject decision here; every trait impl in the nine trusted files is
`Display`/`Default`. The guard that actually protects against a missed edge is
D, which pins the *set of files* contributing trusted lines — an edge into a
prelude would move a file into the set, which no line-count drift can hide.

# The guards, and what each would catch

  A  a NEW `insert_unchecked` call site, i.e. a new way for a declaration to
     exist that nobody argued for.
  B  `insert_unchecked` (or any `Environment` mutator) becoming `pub`, which
     would let code outside this crate put an unchecked declaration in an
     environment.
  C  the trusted core growing past a ceiling — a step change, not edit noise.
  D  a file entering (or leaving) the trusted set. This is the structural
     guard: it is what turned up `lean_export.rs`.
  E  floors. A scanner that stops finding functions reports a beautiful clean
     zero, and a zero is indistinguishable from a strong result.

Every guard is driven to failure in `scripts/tests/test_check_kernel_trusted_core.py`.

# What this does NOT establish

That the 5,110 lines are *correct*. Nothing static can. It establishes what the
question is about, and it stops the answer drifting silently. Corroboration of
those lines against an independent implementation is a different instrument:
`crates/axeyum-lean-import/tests/real_lean_wire_differential.rs` feeds the same
bytes to this kernel and to official Lean's and requires them to agree.
"""

from __future__ import annotations

import argparse
import collections
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
SRC = ROOT / "crates/axeyum-lean-kernel/src"

IDENT = r"[A-Za-z_][A-Za-z0-9_]*"

# --- guard A ---------------------------------------------------------------
# The only functions permitted to contain an `Environment::insert_unchecked`
# call. Each one owns a checking argument; adding to this list means arguing a
# new one, which is exactly the review this pin exists to force.
#
#   Kernel::add_declaration            tc.rs      infers the type, requires it
#                                                 to be a Sort, and requires any
#                                                 value to check against it.
#   Kernel::add_inductive_group        inductive.rs  positivity, universe and
#                                                 constructor checks for the
#                                                 whole mutual group, then the
#                                                 derived recursors.
#   Kernel::restore_nested_inductive_group inductive.rs  republishes a group
#                                                 already checked under
#                                                 temporary names; gated by
#                                                 `validate_nested_temporary_group`.
#   Kernel::add_quotient_package       quotient.rs  the four `Quot` members, as
#                                                 a shape-validated package.
ADMISSION_GATES = {
    ("tc.rs", "add_declaration"),
    ("inductive.rs", "add_inductive_group"),
    ("inductive.rs", "restore_nested_inductive_group"),
    ("quotient.rs", "add_quotient_package"),
}

# --- guard D ---------------------------------------------------------------
# The files that contribute at least one trusted line. Pinned exactly: a file
# joining this set is an architectural event (some checking moved), and a file
# leaving it is equally worth a look. Measured 2026-08-17.
TRUSTED_FILES = {
    "env.rs",
    "expr.rs",
    "inductive.rs",
    "lean_export.rs",
    "level.rs",
    "lib.rs",
    "name.rs",
    "quotient.rs",
    "tc.rs",
}

# --- guard C ---------------------------------------------------------------
# Set 2026-08-17 at a measured 5,129 function-body lines (the docstring above
# has always said 5,129; this comment previously said "5,110", which was never
# what the tool measured at that commit — re-run against a `git archive` of
# c6a3147bc confirms 5,129 exactly, matching the docstring's own per-file
# breakdown line for line. Fixed 2026-08-25, no ceiling movement from this
# alone). The ceiling has deliberate headroom: the point is to catch a step
# change in what must be correct, not to make every edit in `tc.rs` fail an
# unrelated lane's gate. Raising it means more code must be right, so say why
# in the commit message.
#
# Raised 5500 -> 5900 on 2026-08-25 at a measured 5,508 (past the old ceiling).
# Traced to two real, necessary additions since 2026-08-17, both landed with
# their own soundness/perf evidence and both already narrated in `git log`:
#
#   +377  tc.rs (+347) / inductive.rs (+30), commit 2633d7186: universe-
#         parameter closure. The kernel-vs-Lean wire differential (widened 5
#         mutation families -> 51) found declarations official Lean 4.30.0
#         refuses that this kernel admitted — a `Param` occurring in a type or
#         value but not among the declaration's OWN `levelParams` was never
#         checked, so an undeclared universe leaked into every instantiation
#         site. `undeclared_universe_param`/`undeclared_level_param` (tc.rs)
#         are called from BOTH `check_declaration` (tc.rs) and
#         `add_inductive_group` (inductive.rs) — the inductive gate type-checks
#         its own group and never routes through `check_declaration`, so it
#         needed the same check written into the gate itself, not into a
#         caller the trusted closure would skip. This closes a real
#         soundness hole; it cannot be moved off the admission path because it
#         IS the admission path.
#   +349  tc.rs (+347) / env.rs (+2), commits 6e9aeab62 + 0887ab652 +
#         4e1f9b092: memoisation for `whnf_core`, Lean's second reduction
#         cache (ours had one of the two `type_checker.h` caches, not both).
#         Without it the full kernel suite ran 1857 s -> 13.4 s once fixed —
#         a 138x pathological cost that made the trusted core practically
#         unusable, not merely slow. The new functions (`whnf_core_result`,
#         `remember_whnf_core`, `recall_whnf_core`, the `taint_*`/
#         `drain_volatile`/`unbound_probe_mark` volatile-entry tracking,
#         `type_of`/`value_of`) sit directly inside `def_eq`/`whnf`, which
#         `add_declaration` calls to type-check every admitted term — a wrong
#         cached answer is a wrong verdict, so the cache's correctness is
#         exactly as trust-critical as the reduction it memoises and belongs
#         in the trusted core, not beside it. Each invalidation path (push,
#         pop, environment revision, `Kernel::rollback`) carries its own
#         mutation-checked test per the commit messages.
#
# Neither addition could be moved off the admission path without either
# reopening the soundness hole (universe closure) or losing the fix that made
# the kernel checkable at all in reasonable time (whnf_core memo) — see
# option (c) in the brief that produced this note; both were rejected.
#
# Headroom kept at the same character as 2026-08-17's: that ceiling was 371
# lines (7.2%) above its measurement; 5900 is 392 lines (7.1%) above this one
# — enough that an ordinary edit in `tc.rs` does not fail an unrelated lane's
# gate, not so much that a step change slips through unnoticed.
TRUSTED_LINES_MAX = 5900

# --- guard E ---------------------------------------------------------------
# Floors. A scanner that silently stops parsing reports 0 trusted lines and
# every claim above it becomes vacuous.
MIN_TOTAL_FUNCTIONS = 600
MIN_TRUSTED_FUNCTIONS = 180
MIN_TRUSTED_LINES = 4000
MIN_PRODUCTION_FILES = 30


# ---------------------------------------------------------------------------
# Rust-aware scanning
# ---------------------------------------------------------------------------
def blank_noncode(text: str) -> str:
    """Blank comments and literal *contents*, preserving every byte offset.

    Offsets are preserved so line numbers stay true and spans computed on the
    blanked view point at the real file. Handles nested `/* */`, raw strings
    (`r#"…"#`), byte strings, and — the one that bites — distinguishes a char
    literal `'a'` from a lifetime `'a`.
    """
    out = list(text)
    i, n = 0, len(text)

    def blank(a: int, b: int) -> None:
        for k in range(a, b):
            if out[k] != "\n":
                out[k] = " "

    while i < n:
        c = text[i]
        if c == "/" and i + 1 < n and text[i + 1] == "/":
            j = text.find("\n", i)
            j = n if j < 0 else j
            blank(i, j)
            i = j
            continue
        if c == "/" and i + 1 < n and text[i + 1] == "*":
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/*", j):
                    depth += 1
                    j += 2
                elif text.startswith("*/", j):
                    depth -= 1
                    j += 2
                else:
                    j += 1
            blank(i, j)
            i = j
            continue
        if c == "r" and i + 1 < n and text[i + 1] in '"#':
            m = re.match(r'r(#*)"', text[i:])
            if m:
                close = '"' + m.group(1)
                j = text.find(close, i + m.end())
                j = n if j < 0 else j + len(close)
                blank(i, j)
                i = j
                continue
        if c == "b" and i + 1 < n and text[i + 1] == '"':
            i += 1
            c = '"'
        if c == '"':
            j = i + 1
            while j < n:
                if text[j] == "\\":
                    j += 2
                    continue
                if text[j] == '"':
                    j += 1
                    break
                j += 1
            blank(i, j)
            i = j
            continue
        if c == "'":
            if i + 1 < n and text[i + 1] == "\\":
                j = i + 2
                while j < n and text[j] != "'":
                    j += 1
                blank(i, j + 1)
                i = j + 1
                continue
            if i + 2 < n and text[i + 2] == "'":
                blank(i, i + 3)
                i += 3
                continue
            i += 1  # a lifetime, not a literal
            continue
        i += 1
    return "".join(out)


def brace_span(code: str, open_idx: int) -> int:
    depth, k, n = 0, open_idx, len(code)
    while k < n:
        if code[k] == "{":
            depth += 1
        elif code[k] == "}":
            depth -= 1
            if depth == 0:
                return k + 1
        k += 1
    return n


def strip_cfg_test_blocks(code: str) -> str:
    """Blank inline `#[cfg(test)] mod tests { … }` bodies.

    `quotient.rs`, `lean_pp.rs` and `lean_export.rs` carry their tests inline,
    and those tests call `insert_unchecked` directly — six times. Counting them
    as admission gates would have made guard A meaningless on day one.
    """
    out = list(code)
    for m in re.finditer(r"#\[cfg\(test\)\]", code):
        brace = code.find("{", m.end())
        semi = code.find(";", m.end())
        if brace < 0 or (0 <= semi < brace):
            continue
        end = brace_span(code, brace)
        for p in range(m.start(), end):
            if out[p] != "\n":
                out[p] = " "
    return "".join(out)


def test_files(files: list[pathlib.Path]) -> set[pathlib.Path]:
    """Files reached only through a `#[cfg(test)] mod x;` declaration."""
    found: set[pathlib.Path] = set()
    for f in files:
        text = f.read_text(encoding="utf-8")
        pattern = (
            r"#\[cfg\(test\)\]\s*(?:pub(?:\([^)]*\))?\s+)?mod\s+(" + IDENT + r")\s*;"
        )
        for m in re.finditer(pattern, text):
            base = f.parent if f.stem == "lib" else f.parent / f.stem
            found.add((base / (m.group(1) + ".rs")).resolve())
    return found


def impl_blocks(code: str) -> list[tuple[str, int, int]]:
    """`(owner type, body start, body end)` for each `impl … Type … {`."""
    out = []
    for m in re.finditer(r"\bimpl\b", code):
        brace = code.find("{", m.end())
        if brace < 0:
            continue
        head = code[m.end() : brace]
        if "(" in head and ")" not in head:
            continue  # `-> impl Trait` inside a signature, not an impl block
        for _ in range(4):
            head = re.sub(r"<[^<>]*>", " ", head)
        if " for " in head:
            head = head.split(" for ", 1)[1]
        tokens = re.findall(IDENT, head)
        if not tokens:
            continue
        out.append((tokens[-1], brace, brace_span(code, brace)))
    return out


def function_spans(code: str) -> list[tuple[str, int, int, int]]:
    """`(name, header start, body start, body end)` for every `fn` with a body."""
    res, n = [], len(code)
    for m in re.finditer(r"\bfn\s+(" + IDENT + r")", code):
        paren = code.find("(", m.end())
        if paren < 0:
            continue
        depth, k = 0, paren
        while k < n:  # skip the parameter list
            if code[k] in "([":
                depth += 1
            elif code[k] in ")]":
                depth -= 1
                if depth == 0:
                    k += 1
                    break
            k += 1
        depth, body = 0, None
        while k < n:  # then the return type / where clause, to `{` or `;`
            ch = code[k]
            if ch in "([":
                depth += 1
            elif ch in ")]":
                depth -= 1
            elif ch == ";" and depth == 0:
                break
            elif ch == "{" and depth == 0:
                body = k
                break
            k += 1
        if body is None:
            continue  # a trait method declaration, no body
        res.append((m.group(1), m.start(), body, brace_span(code, body)))
    return res


class Crate:
    """Every function in the crate's non-test sources, plus its call graph."""

    def __init__(self, root: pathlib.Path) -> None:
        files = sorted(root.rglob("*.rs"))
        tests = test_files(files)
        self.production = [f for f in files if f.resolve() not in tests]
        self.test_files = sorted(tests)
        self.fns: list[dict] = []
        for f in self.production:
            code = strip_cfg_test_blocks(blank_noncode(f.read_text(encoding="utf-8")))
            impls = impl_blocks(code)
            for name, head, body, end in function_spans(code):
                owner, best = None, None
                for ty, start, stop in impls:
                    if start < head < stop and (best is None or start > best):
                        best, owner = start, ty
                self.fns.append(
                    {
                        "name": name,
                        "owner": owner,
                        "file": str(f.relative_to(root)),
                        "line": code.count("\n", 0, head) + 1,
                        "end": code.count("\n", 0, end) + 1,
                        "body": code[body:end],
                        "filecode": code,
                    }
                )
        self.by_name = collections.defaultdict(list)
        self.by_owner = collections.defaultdict(list)
        self.free = collections.defaultdict(list)
        for i, r in enumerate(self.fns):
            self.by_name[r["name"]].append(i)
            if r["owner"]:
                self.by_owner[(r["owner"], r["name"])].append(i)
            else:
                self.free[r["name"]].append(i)
        self.types = {r["owner"] for r in self.fns if r["owner"]}
        # Loose-rule support: for the `.f(` receiver-unknown case below, the
        # original code re-scanned the WHOLE enclosing file with a fresh
        # `re.search(type_name, filecode)` for every candidate at every call
        # site — O(call sites * same-named candidates * file size), and it
        # dominates runtime once the crate is large enough for common method
        # names (`new`, `get`, …) to have many candidates. `r["filecode"]` is
        # the *same string object* for every function in one file (assigned
        # once per file in the loop above), so which of `self.types` occurs
        # in a given file is a per-FILE fact, not a per-(function, candidate)
        # one. Precompute it once per file with a single combined-alternation
        # scan; `_resolve` below looks it up by `id(filecode)` instead of
        # re-searching. Same `\b...\b` semantics, same result set — this is a
        # cache, not a change to what counts as a match.
        self._types_in_file: dict[int, frozenset[str]] = {}
        if self.types:
            alt = "|".join(re.escape(t) for t in sorted(self.types))
            types_pattern = re.compile(r"\b(?:" + alt + r")\b")
            seen_filecodes: dict[int, str] = {}
            for r in self.fns:
                seen_filecodes.setdefault(id(r["filecode"]), r["filecode"])
            for key, code in seen_filecodes.items():
                self._types_in_file[key] = frozenset(types_pattern.findall(code))
        self.edges = [self._resolve(i, r) for i, r in enumerate(self.fns)]

    def _resolve(self, index: int, r: dict) -> set[int]:
        body, owner, out = r["body"], r["owner"], set()
        for m in re.finditer(r"\bself\s*\.\s*(" + IDENT + r")\s*\(", body):
            out.update(self.by_owner.get((owner, m.group(1)), ()))
        # `T::f` and `Self::f`, with or without a call — `map(Kernel::f)` counts.
        for m in re.finditer(r"\b(" + IDENT + r")\s*::\s*(" + IDENT + r")\b", body):
            ty, name = m.group(1), m.group(2)
            if ty == "Self":
                out.update(self.by_owner.get((owner, name), ()))
            elif ty in self.types:
                out.update(self.by_owner.get((ty, name), ()))
        for m in re.finditer(r"(?<![\w.:])(" + IDENT + r")\s*\(", body):
            out.update(self.free.get(m.group(1), ()))
        # Loose rule for any other receiver: every same-named method whose owner
        # type is nameable in this file. Over-approximating on purpose.
        present = self._types_in_file.get(id(r["filecode"]), frozenset())
        for m in re.finditer(r"\.\s*(" + IDENT + r")\s*\(", body):
            if body[max(0, m.start() - 4) : m.start()].endswith("self"):
                continue
            for j in self.by_name.get(m.group(1), ()):
                other = self.fns[j]["owner"]
                if other and other in present:
                    out.add(j)
        out.discard(index)
        return out

    def admission_gates(self) -> list[int]:
        """Enclosing functions of every non-test `insert_unchecked` call."""
        return [
            i
            for i, r in enumerate(self.fns)
            if "insert_unchecked" in r["body"] and r["name"] != "insert_unchecked"
        ]

    def closure(self, entries: list[int]) -> set[int]:
        seen, stack = set(entries), list(entries)
        while stack:
            i = stack.pop()
            for j in self.edges[i]:
                if j not in seen:
                    seen.add(j)
                    stack.append(j)
        return seen


def basename(path: str) -> str:
    return path.split("/")[-1]


def environment_mutators_are_private(root: pathlib.Path) -> list[str]:
    """Guard B: no `pub` way to change an `Environment` from outside the crate.

    The closure in `trusted()` is exhaustive only because `insert_unchecked` is
    unreachable from outside. Checked structurally rather than believed: every
    `fn` taking `&mut self` in `env.rs`'s `impl Environment` must be private or
    `pub(crate)`.
    """
    code = strip_cfg_test_blocks(
        blank_noncode((root / "env.rs").read_text(encoding="utf-8"))
    )
    leaks = []
    for ty, start, stop in impl_blocks(code):
        if ty != "Environment":
            continue
        block = code[start:stop]
        for m in re.finditer(r"(pub(?:\s*\([^)]*\))?\s+)?fn\s+(" + IDENT + r")\s*\(([^)]*)", block):
            vis, name, params = m.group(1) or "", m.group(2), m.group(3)
            if "&mut self" not in params:
                continue
            if vis.strip() and "(crate)" not in vis and "(super)" not in vis:
                leaks.append(f"Environment::{name} is `{vis.strip()}`")
    return leaks


class Report:
    def __init__(self, crate: Crate) -> None:
        self.crate = crate
        self.gates = crate.admission_gates()
        self.trusted = crate.closure(self.gates)
        self.per_file: dict[str, list[int]] = collections.defaultdict(lambda: [0, 0])
        for i, r in enumerate(crate.fns):
            lines = r["end"] - r["line"] + 1
            self.per_file[r["file"]][1] += lines
            if i in self.trusted:
                self.per_file[r["file"]][0] += lines
        self.trusted_lines = sum(v[0] for v in self.per_file.values())
        self.total_fn_lines = sum(v[1] for v in self.per_file.values())
        self.trusted_files = {
            basename(k) for k, v in self.per_file.items() if v[0] > 0
        }
        self.gate_names = {(basename(crate.fns[i]["file"]), crate.fns[i]["name"]) for i in self.gates}


def evaluate(report: Report, leaks: list[str]) -> list[str]:
    """Every guard, separated so each can be driven to failure in a control."""
    failures = []
    if report.gate_names != ADMISSION_GATES:
        added = sorted(report.gate_names - ADMISSION_GATES)
        gone = sorted(ADMISSION_GATES - report.gate_names)
        if added:
            failures.append(
                "A: declarations can now enter the environment from functions "
                f"nobody argued for: {added}. Each is a new admission gate; add "
                "it to ADMISSION_GATES only with the checking argument written down."
            )
        if gone:
            failures.append(f"A: pinned admission gate(s) no longer insert: {gone}")
    if leaks:
        failures.append(
            "B: an `Environment` mutator is public, so code outside this crate "
            f"can bypass every admission gate: {leaks}"
        )
    if report.trusted_lines > TRUSTED_LINES_MAX:
        failures.append(
            f"C: the trusted core grew to {report.trusted_lines} lines, past the "
            f"{TRUSTED_LINES_MAX} ceiling. More code must be correct than when "
            "that ceiling was set; say why before raising it."
        )
    if report.trusted_files != TRUSTED_FILES:
        added = sorted(report.trusted_files - TRUSTED_FILES)
        gone = sorted(TRUSTED_FILES - report.trusted_files)
        if added:
            failures.append(
                f"D: file(s) joined the trusted core: {added}. Something that was "
                "content or interop is now on the path to an admitted theorem."
            )
        if gone:
            failures.append(f"D: file(s) left the trusted core: {gone}")
    if len(report.crate.fns) < MIN_TOTAL_FUNCTIONS:
        failures.append(
            f"E: only {len(report.crate.fns)} functions parsed (floor "
            f"{MIN_TOTAL_FUNCTIONS}); the scanner is blind, not the crate empty."
        )
    if len(report.trusted) < MIN_TRUSTED_FUNCTIONS:
        failures.append(
            f"E: only {len(report.trusted)} trusted functions (floor "
            f"{MIN_TRUSTED_FUNCTIONS}); the call graph collapsed."
        )
    if report.trusted_lines < MIN_TRUSTED_LINES:
        failures.append(
            f"E: only {report.trusted_lines} trusted lines (floor "
            f"{MIN_TRUSTED_LINES}); a clean small number here is a bug, not a win."
        )
    if len(report.crate.production) < MIN_PRODUCTION_FILES:
        failures.append(
            f"E: only {len(report.crate.production)} production files found "
            f"(floor {MIN_PRODUCTION_FILES})."
        )
    return failures


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quiet", action="store_true")
    parser.add_argument("--verbose", action="store_true", help="list trusted functions")
    args = parser.parse_args()

    crate = Crate(SRC)
    report = Report(crate)
    failures = evaluate(report, environment_mutators_are_private(SRC))

    if not args.quiet:
        print("kernel trusted core (derived from Environment::insert_unchecked)")
        print(f"  admission gates          {len(report.gates)}")
        for i in sorted(report.gates, key=lambda i: crate.fns[i]["file"]):
            r = crate.fns[i]
            print(f"    {r['file']}:{r['line']}  {r['owner']}::{r['name']}")
        print(f"  trusted functions        {len(report.trusted)} of {len(crate.fns)}")
        print(f"  trusted function lines   {report.trusted_lines} of {report.total_fn_lines}")
        print(f"  ceiling                  {TRUSTED_LINES_MAX}")
        print("  per file (trusted / all function lines):")
        for k, v in sorted(report.per_file.items(), key=lambda kv: -kv[1][0]):
            if v[0]:
                print(f"    {v[0]:6d} / {v[1]:6d}  {k}")
        untrusted = sum(v[1] for v in report.per_file.values() if not v[0])
        print(f"  NOT trusted              {untrusted} function lines in "
              f"{sum(1 for v in report.per_file.values() if not v[0])} files "
              "(preludes, pretty-printer, arithmetic model)")
        if args.verbose:
            for i in sorted(report.trusted, key=lambda i: -(crate.fns[i]["end"] - crate.fns[i]["line"])):
                r = crate.fns[i]
                print(f"    {r['end'] - r['line'] + 1:5d}  {r['file']}:{r['line']} {r['owner']}::{r['name']}")

    for line in failures:
        print(f"FAIL {line}", file=sys.stderr)
    if failures:
        return 1
    if not args.quiet:
        print("ok: 5 guards, 0 failures")
    return 0


if __name__ == "__main__":
    sys.exit(main())

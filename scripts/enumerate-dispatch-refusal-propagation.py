#!/usr/bin/env python3
"""Enumerate every site in the solver dispatch path where a sub-solve's
`SolverError::Unsupported` is PROPAGATED to the caller rather than converted
into a decline (ADR-1927 / ADR-1966).

The defect shape this instrument exists to find:

    a dispatch rung hands a query it REWROTE to an inner solve, the inner
    solve refuses the rewrite's fragment, and that refusal travels out of
    `solve` as the ORIGINAL query's verdict -- so every rung below never runs.

Nothing here is a hand-written list of sites.  The three populations are all
derived from the source:

  * `U`  -- functions that can return `SolverError::Unsupported`.  Seeded by
            the functions whose body literally constructs one, then closed
            transitively over `?`-propagation.
  * `D`  -- the dispatch path: functions reachable in the intra-crate call
            graph from the front door, which is itself discovered as the
            `pub fn check*` / `pub fn solve*` entry points of `auto.rs`.
  * sites -- for every function in `D`, every call to a member of `U` whose
            error is propagated (bare `?`, or an `Err(Unsupported) => return
            Err(..)` match arm) rather than declined.

What this instrument CANNOT see, stated up front because three prior scans in
this repository each missed instances a probe later found:

  1. Dynamic dispatch.  A `Box<dyn Backend>` call resolves at run time; the
     call graph here is by NAME, so a refusal that arrives through a trait
     object is attributed to the trait method, not the implementation.
  2. Macro-generated call sites.  Bodies are read as text after comment and
     string stripping; a site produced by a macro expansion is invisible.
  3. Method calls are matched by BARE NAME, so two inherent methods with the
     same name merge, and a method whose receiver decides the callee is
     resolved optimistically (over-inclusive, never under).
  4. Refusals that are not `SolverError::Unsupported` -- an `Unknown` whose
     kind means "I refuse" reads as a first-class verdict here and is not in
     this population at all.  That class has to be found by reading.
  5. Whether a rung BELOW actually owns the refused construct.  That is a
     semantic question; this tool reports the structural precondition (there
     IS code below the site in the enclosing body) and a human classifies.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

CRATE_SRC = "crates/axeyum-solver/src"

# ---------------------------------------------------------------- lexing


def strip_noise(src: str) -> str:
    """Blank out comments and string/char literals, preserving byte offsets.

    Offsets are preserved so every reported line number is the real one.
    """
    out = list(src)
    i = 0
    n = len(src)
    while i < n:
        c = src[i]
        if c == "/" and i + 1 < n and src[i + 1] == "/":
            j = src.find("\n", i)
            j = n if j < 0 else j
            for k in range(i, j):
                out[k] = " "
            i = j
            continue
        if c == "/" and i + 1 < n and src[i + 1] == "*":
            depth = 1
            j = i + 2
            while j < n and depth:
                if src[j] == "/" and j + 1 < n and src[j + 1] == "*":
                    depth += 1
                    j += 2
                    continue
                if src[j] == "*" and j + 1 < n and src[j + 1] == "/":
                    depth -= 1
                    j += 2
                    continue
                j += 1
            for k in range(i, j):
                if out[k] != "\n":
                    out[k] = " "
            i = j
            continue
        if c == "r" and i + 1 < n and src[i + 1] in '#"':
            m = re.match(r'r(#*)"', src[i:])
            if m:
                term = '"' + m.group(1)
                j = src.find(term, i + m.end())
                j = n if j < 0 else j + len(term)
                for k in range(i, j):
                    if out[k] != "\n":
                        out[k] = " "
                i = j
                continue
        if c == '"':
            j = i + 1
            while j < n:
                if src[j] == "\\":
                    j += 2
                    continue
                if src[j] == '"':
                    j += 1
                    break
                j += 1
            for k in range(i, min(j, n)):
                if out[k] != "\n":
                    out[k] = " "
            i = j
            continue
        if c == "'":
            m = re.match(r"'(?:\\.|[^\\'])'", src[i:])
            if m:
                for k in range(i, i + m.end()):
                    out[k] = " "
                i += m.end()
                continue
        i += 1
    return "".join(out)


FN_RE = re.compile(r"\bfn\s+(?P<name>[A-Za-z_][A-Za-z0-9_]*)\s*(?:<[^{;()]*>)?\s*\(")
IDENT_RE = re.compile(r"\b([a-z_][a-z0-9_]*)\s*\(")
MATCH_RETURN_RE = re.compile(
    r"Err\s*\(\s*(?:SolverError::)?Unsupported[^)]*\)\s*=>\s*"
    r"(?:return\s+)?(?:Err|Some\s*\(\s*Err)"
)
UNSUP_CONSTRUCT = re.compile(
    r"SolverError::Unsupported|SolverError::unsupported|\bunsupported\s*\(|"
    r"milp_out_of_fragment"
)


def line_of(src: str, off: int) -> int:
    return src.count("\n", 0, off) + 1


def find_bodies(clean: str):
    """Yield (name, body_start, body_end, sig_offset, ret) for every `fn`."""
    n = len(clean)
    for m in FN_RE.finditer(clean):
        i = m.end() - 1
        depth = 0
        while i < n:
            if clean[i] == "(":
                depth += 1
            elif clean[i] == ")":
                depth -= 1
                if depth == 0:
                    break
            i += 1
        j = i + 1
        while j < n and clean[j] not in "{;":
            j += 1
        if j >= n or clean[j] == ";":
            continue
        ret = clean[i + 1 : j]
        depth = 0
        k = j
        while k < n:
            if clean[k] == "{":
                depth += 1
            elif clean[k] == "}":
                depth -= 1
                if depth == 0:
                    break
            k += 1
        yield m.group("name"), j, k + 1, m.start(), ret


def call_tail(body: str, open_paren: int, span: int = 48) -> str:
    """Text immediately after the closing paren of the call at `open_paren`."""
    depth = 0
    i = open_paren
    n = len(body)
    while i < n:
        if body[i] == "(":
            depth += 1
        elif body[i] == ")":
            depth -= 1
            if depth == 0:
                break
        i += 1
    return body[i + 1 : i + 1 + span]


# ------------------------------------------------------------- analysis


def load(root: Path):
    files = {}
    for p in sorted(root.rglob("*.rs")):
        raw = p.read_text(encoding="utf-8", errors="replace")
        files[p] = (raw, strip_noise(raw))
    return files


def build(files):
    fns: dict[str, list[dict]] = {}
    for path, (raw, clean) in files.items():
        sp = str(path)
        in_tests = sp.endswith("tests.rs") or "/tests/" in sp
        for name, bs, be, sig, ret in find_bodies(clean):
            fns.setdefault(name, []).append(
                {
                    "name": name,
                    "path": sp,
                    "line": line_of(raw, sig),
                    "body": clean[bs:be],
                    "body_off": bs,
                    "ret": " ".join(ret.split()),
                    "raw": raw,
                    "in_tests": in_tests,
                }
            )
    return fns


def is_subsolve(fns, name: str) -> bool:
    """A callee is a SUB-SOLVE when its declared return type carries a whole
    solver verdict -- `CheckResult`, a `Model`, or a `Verdict`.  This is read
    off the signature, not from a list of names: the defect shape is a rung
    handing a REWRITTEN QUERY to something that answers queries, and that is
    exactly what such a return type means.
    """
    for r in fns.get(name, ()):
        if r["in_tests"]:
            continue
        if re.search(r"\bCheckResult\b|\bVerdict\b", r["ret"]):
            return True
    return False


def propagation_form(body: str, m) -> str | None:
    """How the call matched at `m` hands its error to the caller, or None.

    Three forms count as propagation, and missing any one of them is how a
    scan of this kind under-reports:

      `?`           -- the bare question mark
      `tail`        -- the call IS the function's trailing expression
      `return`      -- `return f(..)` / `return Ok(f(..)?)`
    """
    tail = call_tail(body, m.end() - 1)
    stripped = tail.lstrip()
    if stripped.startswith("?"):
        return "?"
    # Trailing expression of the body: only `)` and whitespace to the end.
    if re.fullmatch(r"[\s)]*\}?\s*", tail) and set(tail) <= set(" \t\r\n)}"):
        rest = body[m.end() :]
        depth = 1
        i = m.end()
        n = len(body)
        while i < n and depth:
            if body[i] == "(":
                depth += 1
            elif body[i] == ")":
                depth -= 1
            i += 1
        rest = body[i:]
        if re.fullmatch(r"[\s)]*\}\s*", rest):
            return "tail"
    # `return f(..)` -- look back from the call for a `return` on the same stmt.
    look = body[max(0, m.start() - 12) : m.start()]
    if re.search(r"\breturn\s*$", look):
        return "return"
    return None


def constructs_unsupported(body: str) -> bool:
    """Whether the body CONSTRUCTS an `Unsupported`, not merely matches one.

    `Err(SolverError::Unsupported(msg)) => { ... }` is a match arm -- the
    function that writes it is CONVERTING a refusal, which is the opposite of
    producing one.  Counting patterns as constructions marks every conversion
    helper as a refuser and re-flags the sites it fixed.
    """
    for m in UNSUP_CONSTRUCT.finditer(body):
        after = body[m.end() :]
        # Skip the argument list, then look at what follows.
        if after.startswith("("):
            depth = 0
            i = 0
            for i, ch in enumerate(after):
                if ch == "(":
                    depth += 1
                elif ch == ")":
                    depth -= 1
                    if depth == 0:
                        break
            after = after[i + 1 :]
        if re.match(r"\s*\)*\s*(?:if\s[^=]{0,120})?=>", after):
            continue  # a match arm: this body CONVERTS, it does not produce
        return True
    return False


def close_unsupported(fns) -> set[str]:
    """Functions that can return SolverError::Unsupported, transitively."""
    seed: set[str] = set()
    for name, recs in fns.items():
        for r in recs:
            if not r["in_tests"] and constructs_unsupported(r["body"]):
                seed.add(name)
                break
    changed = True
    while changed:
        changed = False
        for name, recs in fns.items():
            if name in seed:
                continue
            for r in recs:
                if r["in_tests"]:
                    continue
                for m in IDENT_RE.finditer(r["body"]):
                    callee = m.group(1)
                    if callee not in seed or callee == name:
                        continue
                    if propagation_form(r["body"], m):
                        seed.add(name)
                        changed = True
                        break
                if name in seed:
                    break
    return seed


def reachable(fns, roots) -> set[str]:
    seen: set[str] = set()
    stack = list(roots)
    while stack:
        f = stack.pop()
        if f in seen or f not in fns:
            continue
        seen.add(f)
        for r in fns[f]:
            if r["in_tests"]:
                continue
            for m in IDENT_RE.finditer(r["body"]):
                c = m.group(1)
                if c in fns and c not in seen:
                    stack.append(c)
    return seen


def enumerate_sites(root: Path):
    files = load(root)
    fns = build(files)
    unsup = close_unsupported(fns)

    roots = {
        name
        for name, recs in fns.items()
        for r in recs
        if not r["in_tests"]
        and r["path"].endswith("auto.rs")
        and (name.startswith("check") or name.startswith("solve"))
    }
    dispatch = reachable(fns, roots)

    sites = []
    for name in sorted(dispatch):
        for r in fns[name]:
            if r["in_tests"]:
                continue
            body, raw, bs = r["body"], r["raw"], r["body_off"]
            for m in IDENT_RE.finditer(body):
                callee = m.group(1)
                if callee not in unsup or callee == name:
                    continue
                form = propagation_form(body, m)
                if form is None:
                    continue
                off = bs + m.start()
                below = sorted(
                    {
                        mm.group(1)
                        for mm in IDENT_RE.finditer(body[m.end() :])
                        if is_subsolve(fns, mm.group(1)) and mm.group(1) != name
                    }
                )
                sites.append(
                    {
                        "kind": f"propagate-{form}",
                        "fn": name,
                        "callee": callee,
                        "path": r["path"],
                        "line": line_of(raw, off),
                        "chars_below_in_body": len(body) - m.start(),
                        "subsolve": is_subsolve(fns, callee),
                        "rung": bool(re.search(r"\bCheckResult\b", r["ret"])),
                        "rungs_below": below,
                    }
                )
            for m in MATCH_RETURN_RE.finditer(body):
                off = bs + m.start()
                sites.append(
                    {
                        "kind": "match-return-Err",
                        "fn": name,
                        "callee": None,
                        "path": r["path"],
                        "line": line_of(raw, off),
                        "chars_below_in_body": len(body) - m.start(),
                        "subsolve": True,
                        "rung": bool(re.search(r"\bCheckResult\b", r["ret"])),
                        "rungs_below": [],
                    }
                )

    sites.sort(key=lambda s: (s["path"], s["line"], s["kind"]))
    core = [s for s in sites if s["subsolve"] and s["rung"]]
    summary = {
        "functions_total": sum(len(v) for v in fns.values()),
        "can_return_unsupported": len(unsup),
        "dispatch_reachable": len(dispatch),
        "roots": len(roots),
        "sites_broad": len(sites),
        "sites_core": len(core),
        "core_with_code_below": sum(
            1 for s in core if s["chars_below_in_body"] > 200
        ),
        # The structural precondition of the ADR-1966 defect: a DIFFERENT
        # sub-solve appears after the site in the same body, so declining
        # instead of propagating would let another route see the query.
        "core_with_a_rung_below": sum(1 for s in core if s["rungs_below"]),
    }
    return summary, sites, core


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=CRATE_SRC)
    ap.add_argument("--json", default=None)
    ap.add_argument("--quiet", action="store_true")
    ap.add_argument(
        "--broad",
        action="store_true",
        help="print the SUPERSET (every ?-propagated call into a function "
        "that can refuse), not just the rung-to-sub-solve core",
    )
    ap.add_argument(
        "--fail-on-new",
        default=None,
        help="pinned baseline JSON; exit 1 if a propagation site appears that "
        "is not in it (a new rung of the ADR-1966 shape)",
    )
    args = ap.parse_args()

    root = Path(args.root)
    if not root.is_dir():
        print(f"enumerator: no such directory {root}", file=sys.stderr)
        return 2
    summary, broad, core = enumerate_sites(root)
    sites = broad if args.broad else core

    # A population of zero means the instrument is broken, not that the tree
    # is clean: this crate has hundreds of `?`-propagated calls by design.
    if summary["can_return_unsupported"] == 0 or summary["dispatch_reachable"] == 0:
        print(
            "enumerator: empty seed or empty call graph -- the instrument did "
            "not run over its subject",
            file=sys.stderr,
        )
        return 2

    if args.json:
        Path(args.json).write_text(
            json.dumps(
                {"summary": summary, "sites": sites, "broad": broad}, indent=2
            )
            + "\n"
        )
    if not args.quiet:
        for k, v in summary.items():
            print(f"{k}: {v}")
        print()
        for s in sites:
            print(
                f"{s['path']}:{s['line']}  {s['kind']:<18} "
                f"{s['fn']} -> {s['callee']}"
            )

    if args.fail_on_new:
        base = json.loads(Path(args.fail_on_new).read_text())
        pinned = {
            (s["path"], s["fn"], s["kind"], s["callee"]) for s in base["sites"]
        }
        now = {(s["path"], s["fn"], s["kind"], s["callee"]) for s in sites}
        new = sorted(now - pinned)
        if new:
            print(
                "\nNEW refusal-propagation sites absent from the pinned "
                "baseline (ADR-1966): each must be classified as a terminal "
                "refusal or converted to a decline.",
                file=sys.stderr,
            )
            for t in new:
                print(f"  {t}", file=sys.stderr)
            return 1
        print(f"\nfail-on-new: 0 new sites against {len(pinned)} pinned")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

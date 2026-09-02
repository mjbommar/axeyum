#!/usr/bin/env python3
"""Census of PRIVATE `fn` items in the kernel crate — the third hiding place.

WHY THIS EXISTS. `docs/research/11-design-review/2026-09-02-retrieval-audit-for-2026-09-01.md`
named three places a proof step can hide from retrieval. Two of them are
reachable by a tool: a declared theorem has a name in the environment, and a
`pub` helper has a name in the source. The third has neither. An inline,
unnamed proof step written as a PRIVATE function in one prelude module
declares nothing, so `shape_search`, `prelude_theorem_inventory` and
`kernel_declaration_projection` are all structurally blind to it — and a lane
that needs the same step writes it again. The audit counted `dvd_elim` at 13
private copies, `absurd` at 12, `dvd_intro` at 10, `or_cases` at 6, by hand.

This is the instrument that count should have come from. It answers two
questions the name-based tools cannot:

  BY NAME  how many private `fn`s share a name across files. Cheap, and it
           finds the families a person would already guess at.
  BY BODY  how many private `fn`s share a NORMALIZED BODY. This is the one
           that matters, because it is blind to the name: it unites
           `dvd_elim` (nat_prelude, `&mut NatDev`) with `dvd_elim_nat`
           (int_prelude, `&mut IntDev`), which a name grouping splits and a
           person reading either file cannot see at all.

WHAT "NORMALIZED" MEANS, precisely, because the answer is only as good as this:

  * comments are removed (they differ per copy and say nothing about the term
    being built), but STRING LITERALS ARE KEPT INTACT. Masking literal content
    would make two functions that differ only in a declared name hash equal,
    which for a declaration script is the difference that matters most.
  * the RECEIVER NAME is normalized. Every copy takes the development as its
    first parameter; some spell it `d`, some `dev`. The whole-word rename to
    `_recv` is what lets those hash together.
  * the CARRIER TYPE is normalized: `NatDev`, `IntDev`, `CharDev` and the test
    `Fixture` all become `_DEV`. This is the deliberate one. Two copies that
    differ ONLY by carrier type are exactly the pair a `NatOps`-generic helper
    would replace, and hiding them in separate groups is how the refactor
    stayed invisible. A group whose members disagree on carrier is REPORTED as
    `carriers: [...]` so the reader can see it rather than having to trust it.
  * whitespace runs collapse to one space.

WHAT THIS DOES NOT MEASURE, stated rather than implied. Structural identity is
approximated by TEXT after those normalizations. Two copies that build the same
term through different local bindings hash differently and land in different
groups; this under-counts duplication and never over-counts it. A group of size
n is a floor, not an estimate.

VISIBILITY. "Private" here means "not `pub`": no visibility at all,
`pub(self)`, `pub(super)`, `pub(crate)`, `pub(in ...)`. All of them are
invisible outside the crate and none of them declares anything into the kernel
environment, which is the property that makes the step unretrievable. The
visibility is recorded per site so a reader can narrow.

Exit 0 when the census is written (or, under `--check`, matches). Exit 1 when
`--check` finds the committed artifact stale, so the exit status depends on
the finding.

Usage:
    python3 scripts/private-helper-census.py            # write the artifact
    python3 scripts/private-helper-census.py --check    # fail if stale
    python3 scripts/private-helper-census.py --top 10   # print top N groups
"""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
CRATE = ROOT / "crates" / "axeyum-lean-kernel" / "src"
ARTIFACT = ROOT / "artifacts" / "refactor" / "private-helper-census.json"
SCHEMA_VERSION = 1
PRODUCED_BY = "scripts/private-helper-census.py"

# The development structs this crate's proof-construction layer is written
# against. Normalized to one token so a carrier-only difference groups.
CARRIERS = ("NatDev", "IntDev", "CharDev", "RealDev", "Fixture")

_FN = re.compile(r"\bfn\s+([A-Za-z_][A-Za-z0-9_]*)")
_VIS = re.compile(r"\bpub\s*(\(\s*[A-Za-z_][A-Za-z0-9_:\s]*\s*\))?\s*$")
_CHAR_LIT = re.compile(r"'(?:\\.|[^'\\])'")


def mask(text: str) -> str:
    """`text` with comment and string-literal CONTENT replaced by spaces.

    Length- and newline-preserving, so an offset into the mask is the same
    offset into the original. This is the scanner's view only: brace matching
    must not be fooled by a `{` inside a comment or a string, and the caller
    extracts spans from the ORIGINAL text at the offsets found here.

    Rust lifetimes (`'a`, `'_`, `'static`) are not char literals and must not
    open one; `_CHAR_LIT` requires a closing quote within two escapes, which
    is what separates them.
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
                if text.startswith("/*", j):
                    depth += 1
                    j += 2
                elif text.startswith("*/", j):
                    depth -= 1
                    j += 2
                else:
                    j += 1
            for k in range(i, j):
                if out[k] != "\n":
                    out[k] = " "
            i = j
        elif c == "r" and i + 1 < n and text[i + 1] in '#"':
            m = re.match(r'r(#*)"', text[i:])
            if not m:
                i += 1
                continue
            close = '"' + m.group(1)
            j = text.find(close, i + m.end())
            j = n if j < 0 else j + len(close)
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
            for k in range(i, j):
                if out[k] != "\n":
                    out[k] = " "
            i = j
        elif c == "'":
            m = _CHAR_LIT.match(text, i)
            if m:
                for k in range(i, m.end()):
                    out[k] = " "
                i = m.end()
            else:
                i += 1  # a lifetime
        else:
            i += 1
    return "".join(out)


def strip_comments(text: str, masked: str) -> str:
    """`text` with comments removed and string literals KEPT.

    A comment is a run the mask blanked that the original did not already have
    blank; a string literal is blanked in the mask too, so the two cannot be
    told apart by the mask alone. They can be told apart by where the run
    STARTS: only a comment run starts at `//` or `/*`.
    """
    out = []
    i, n = 0, len(text)
    while i < n:
        if text.startswith("//", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
        elif text.startswith("/*", i):
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
            out.append(" ")
            i = j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def match_brace(masked: str, start: int) -> int | None:
    """Offset just past the `}` matching the `{` at `start`, or None."""
    depth = 0
    for i in range(start, len(masked)):
        c = masked[i]
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0:
                return i + 1
    return None


def visibility(text: str, fn_at: int) -> str:
    """The visibility keyword immediately preceding `fn`, or `private`."""
    head = text[max(0, fn_at - 96): fn_at]
    head = re.sub(r"\b(const|async|unsafe|extern\s+\"[^\"]*\")\s*$", "", head).rstrip()
    m = _VIS.search(head)
    if not m:
        return "private"
    inner = m.group(1)
    if inner is None:
        return "pub"
    return "pub" + re.sub(r"\s+", "", inner)


def first_param_name(sig: str) -> str | None:
    """The identifier of the function's first parameter, if it has one."""
    open_paren = sig.find("(")
    if open_paren < 0:
        return None
    depth, j = 0, open_paren
    for j in range(open_paren, len(sig)):
        if sig[j] == "(":
            depth += 1
        elif sig[j] == ")":
            depth -= 1
            if depth == 0:
                break
    params = sig[open_paren + 1: j]
    first = params.split(",")[0].strip()
    m = re.match(r"(?:mut\s+)?([A-Za-z_][A-Za-z0-9_]*)\s*:", first)
    return m.group(1) if m else None


def normalize(body: str, recv: str | None) -> str:
    if recv and recv != "self":
        body = re.sub(rf"\b{re.escape(recv)}\b", "_recv", body)
    for carrier in CARRIERS:
        body = re.sub(rf"\b{carrier}\b", "_DEV", body)
    return re.sub(r"\s+", " ", body).strip()


def carriers_in(text: str) -> list[str]:
    return sorted({c for c in CARRIERS if re.search(rf"\b{c}\b", text)})


def scan(path: pathlib.Path, rel: str) -> list[dict]:
    raw = path.read_text(encoding="utf-8", errors="replace")
    masked = mask(raw)
    sites: list[dict] = []
    for m in _FN.finditer(masked):
        fn_at = m.start()
        # Body opens at the first `{` after the signature at paren/bracket
        # depth zero. A `{` inside `(...)` or `[...]` belongs to a default or a
        # const-generic expression, not to the body.
        depth_p = depth_b = 0
        open_brace = None
        for i in range(m.end(), len(masked)):
            c = masked[i]
            if c == "(":
                depth_p += 1
            elif c == ")":
                depth_p -= 1
            elif c == "[":
                depth_b += 1
            elif c == "]":
                depth_b -= 1
            elif c == ";" and depth_p == 0 and depth_b == 0:
                break  # a trait method with no body, or an `fn` type alias
            elif c == "{" and depth_p == 0 and depth_b == 0:
                open_brace = i
                break
        if open_brace is None:
            continue
        end = match_brace(masked, open_brace)
        if end is None:
            continue

        vis = visibility(raw[:fn_at], fn_at)
        if vis == "pub":
            continue  # reachable by a name search from outside the crate

        # Depth at the `fn` keyword: 0 is a free item, >0 is inside an
        # `impl`/`trait`/`mod` block. Recorded, not filtered.
        block_depth = masked.count("{", 0, fn_at) - masked.count("}", 0, fn_at)

        sig = strip_comments(raw[fn_at:open_brace], masked[fn_at:open_brace])
        body = strip_comments(raw[open_brace + 1: end - 1], masked[open_brace + 1: end - 1])
        recv = first_param_name(sig)
        norm = normalize(body, recv)
        sites.append({
            "name": m.group(1),
            "file": rel,
            "line": raw.count("\n", 0, fn_at) + 1,
            "visibility": vis,
            "block_depth": block_depth,
            "receiver": recv,
            "carriers": carriers_in(sig + " " + body),
            "signature": re.sub(r"\s+", " ", sig).strip(),
            "body_lines": body.count("\n") + 1,
            "body_digest": hashlib.sha256(norm.encode()).hexdigest()[:16],
            "is_test_file": rel.endswith("_tests.rs"),
        })
    return sites


def build() -> dict:
    files = sorted(CRATE.rglob("*.rs"), key=lambda p: str(p))
    sites: list[dict] = []
    for path in files:
        rel = str(path.relative_to(ROOT))
        sites.extend(scan(path, rel))

    # The hiding-place population proper: a FREE item (`block_depth == 0`, so
    # not a trait-impl method that a trait already names) in a NON-TEST file.
    # The unrestricted grouping is dominated by the per-module test `Fixture`
    # impls -- 29 copies of `fn kernel`, 29 of `fn nat_state` -- which are real
    # duplication but are `impl NatOps for Fixture` methods, named by the
    # trait, and not what the retrieval audit is about. Reporting both keeps
    # the denominator honest instead of quietly filtering it away.
    inline = [s for s in sites if s["block_depth"] == 0 and not s["is_test_file"]]

    def group(key: str, population: list[dict] | None = None) -> list[dict]:
        buckets: dict[str, list[dict]] = {}
        for s in (sites if population is None else population):
            buckets.setdefault(s[key], []).append(s)
        out = []
        for k, members in buckets.items():
            if len(members) < 2:
                continue
            members = sorted(members, key=lambda s: (s["file"], s["line"]))
            out.append({
                "key": k,
                "count": len(members),
                "names": sorted({s["name"] for s in members}),
                "files": len({s["file"] for s in members}),
                "carriers": sorted({c for s in members for c in s["carriers"]}),
                "body_lines": members[0]["body_lines"],
                "signature": members[0]["signature"],
                "test_file_members": sum(1 for s in members if s["is_test_file"]),
                "sites": [f"{s['file']}:{s['line']}" for s in members],
            })
        # Deterministic: count desc, then key asc.
        return sorted(out, key=lambda g: (-g["count"], g["key"]))

    by_name = group("name")
    by_body = group("body_digest")
    inline_by_name = group("name", inline)
    inline_by_body = group("body_digest", inline)

    return {
        "schema_version": SCHEMA_VERSION,
        "kind": "private-helper-census",
        "produced_by": PRODUCED_BY,
        "authority": {
            "root": str(CRATE.relative_to(ROOT)),
            "rule": "non-`pub` `fn` items; see the module docstring for the "
                    "normalization the body digest is taken over",
            "carriers_normalized": list(CARRIERS),
        },
        "population": {
            "files_scanned": len(files),
            "private_fns": len(sites),
            "private_fns_outside_tests": sum(1 for s in sites if not s["is_test_file"]),
            "distinct_names": len({s["name"] for s in sites}),
            "distinct_body_digests": len({s["body_digest"] for s in sites}),
            "duplicated_name_groups": len(by_name),
            "duplicated_body_groups": len(by_body),
            "sites_in_duplicated_body_groups": sum(g["count"] for g in by_body),
            "inline_step_fns": len(inline),
            "inline_step_name_groups": len(inline_by_name),
            "inline_step_body_groups": len(inline_by_body),
            "sites_in_inline_step_body_groups": sum(
                g["count"] for g in inline_by_body),
        },
        "by_name": by_name,
        "by_body": by_body,
        "inline_steps_by_name": inline_by_name,
        "inline_steps_by_body": inline_by_body,
    }


def render(doc: dict) -> str:
    return json.dumps(doc, indent=2, sort_keys=False) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--check", action="store_true",
                    help="fail (exit 1) when the committed artifact is stale")
    ap.add_argument("--top", type=int, default=0,
                    help="print the top N body groups")
    args = ap.parse_args()

    doc = build()
    text = render(doc)

    if args.check:
        if not ARTIFACT.is_file():
            print(f"PRIVATE_HELPER_CENSUS FAIL: {ARTIFACT.relative_to(ROOT)} "
                  f"is missing. Regenerate with `python3 {PRODUCED_BY}`.")
            return 1
        have = ARTIFACT.read_text(encoding="utf-8")
        if have != text:
            print(f"PRIVATE_HELPER_CENSUS FAIL: "
                  f"{ARTIFACT.relative_to(ROOT)} is stale "
                  f"(committed sha256 {hashlib.sha256(have.encode()).hexdigest()[:12]}, "
                  f"recomputed {hashlib.sha256(text.encode()).hexdigest()[:12]}). "
                  f"Regenerate with `python3 {PRODUCED_BY}`.")
            return 1
        print(f"PRIVATE_HELPER_CENSUS ok|private_fns="
              f"{doc['population']['private_fns']}"
              f"|body_groups={doc['population']['duplicated_body_groups']}"
              f"|sites_in_groups={doc['population']['sites_in_duplicated_body_groups']}")
        return 0

    ARTIFACT.parent.mkdir(parents=True, exist_ok=True)
    ARTIFACT.write_text(text, encoding="utf-8")
    p = doc["population"]
    print(f"PRIVATE_HELPER_CENSUS wrote {ARTIFACT.relative_to(ROOT)}"
          f"|files={p['files_scanned']}|private_fns={p['private_fns']}"
          f"|name_groups={p['duplicated_name_groups']}"
          f"|body_groups={p['duplicated_body_groups']}")

    if args.top:
        print(f"\ntop {args.top} INLINE STEPS by NORMALIZED BODY "
              f"(free item, non-test file; {p['inline_step_fns']} such fns):")
        for g in doc["inline_steps_by_body"][:args.top]:
            print(f"  {g['count']:3d}  {'/'.join(g['names'])}"
                  f"  ({g['files']} file(s), carriers {g['carriers'] or ['-']},"
                  f" {g['body_lines']} body line(s))")
        print(f"\ntop {args.top} INLINE STEPS by NAME:")
        for g in doc["inline_steps_by_name"][:args.top]:
            print(f"  {g['count']:3d}  {g['key']}"
                  f"  ({g['files']} file(s), carriers {g['carriers'] or ['-']})")
        print(f"\ntop {args.top} ALL PRIVATE FNS by NORMALIZED BODY "
              f"(includes per-module test fixtures):")
        for g in doc["by_body"][:args.top]:
            print(f"  {g['count']:3d}  {'/'.join(g['names'])}"
                  f"  ({g['files']} file(s), carriers {g['carriers'] or ['-']},"
                  f" {g['body_lines']} body line(s),"
                  f" {g['test_file_members']} in test files)")
    return 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Resolve conflicts by keeping BOTH sides -- and refuse where that is wrong.

Keeping both sides is the right resolution for a file that is a LIST OF ITEMS
two lanes appended to independently: Rust `fn` items, markdown rows, shell
cases. It is wrong for a file with SYNTAX, and the failure is silent at
resolution time and loud much later.

Measured 2026-08-30, by me, on `artifacts/ontology/settled-fact-statement-pins.json`:
concatenating the two sides of a conflicted JSON OBJECT produced text that does
not parse (`Expecting ',' delimiter: line 30 column 3`). The merge commit was
already made. Nothing in `git status`, `git show --stat` or the merge output
hinted at it -- the file was the expected size and the diff looked ordinary.

So this refuses rather than guesses:

  * `.json` -- parsed on BOTH sides and merged structurally. Objects merge
    key-wise, lists by identity where rows carry an id field, and any key whose
    two sides disagree on a scalar is REPORTED and left to the caller. A JSON
    file is never spliced as text.
  * `.rs`, `.py`, `.sh` -- delimiter balance per side (parens and brackets, not
    only braces: the real failure dangled an open paren). Refuses when a side
    is cut mid-item, which is `lane-merge-additive.py`'s territory.
  * everything else -- keeps both sides, which is the historical behaviour.

Exit 0 resolved, 1 refused with a reason, 2 nothing to do.
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

CONFLICT = re.compile(
    r"<<<<<<< [^\n]*\n(.*?)\n?=======\n(.*?)>>>>>>> [^\n]*\n", re.S
)
GENERATED = {"PLAN.md", "docs/research/09-decisions/README.md"}
BALANCED = {".rs", ".py", ".sh"}
PAIRS = {"(": ")", "[": "]", "{": "}"}


def conflicted() -> list[str]:
    out = subprocess.run(
        ["git", "diff", "--name-only", "--diff-filter=U"],
        capture_output=True, text=True, check=True,
    ).stdout.split()
    return [f for f in out if f not in GENERATED]


def _strip_comments(text: str, ext: str) -> str:
    """Doc comments here are full of `[0,n)` and [`Self::foo`] on purpose."""
    if ext == ".rs":
        return re.sub(r"//[^\n]*", "", text)
    if ext in (".py", ".sh"):
        return re.sub(r"#[^\n]*", "", text)
    return text


def balance(text: str, ext: str) -> dict[str, int]:
    text = _strip_comments(text, ext)
    text = re.sub(r'"(?:[^"\\]|\\.)*"', '""', text)
    counts = {k: 0 for k in PAIRS}
    for ch in text:
        for op, cl in PAIRS.items():
            if ch == op:
                counts[op] += 1
            elif ch == cl:
                counts[op] -= 1
    return counts


# A DUPLICATED DEFINITION is the failure that delimiter balance cannot see, and
# it bit twice in one session. Keeping both sides of a conflict where each side
# edited THE SAME definition line leaves two of them:
#
#   * `justfile` gained three `check:` recipes across three merges. `just`
#     refuses the whole file -- "recipe `check` first defined on line 58 is
#     redefined on line 59" -- so every gate behind it stops running.
#   * `check-lean-gate.sh` gained two `CHECK_FLOOR=` assignments, 230 and 261.
#     Bash takes the LAST, so it happened to be right, and a reordering or a
#     third merge would have silently restored the lower floor.
#
# Both sides balance perfectly. There is nothing cut mid-item. The file is
# simply wrong in a way only the consumer notices.
DEFINITION = {
    "justfile": re.compile(r"^([a-z0-9][a-z0-9._-]*):(?![=])", re.M),
    ".sh": re.compile(r"^([A-Za-z_][A-Za-z_0-9]*)=", re.M),
    ".py": re.compile(r"^(?:def|class)\s+([A-Za-z_][A-Za-z_0-9]*)|^([A-Z_][A-Z_0-9]*)\s*=", re.M),
    ".rs": re.compile(r"^\s*(?:pub(?:\([^)]*\))?\s+)?(?:fn|const|static|struct|enum)\s+([A-Za-z_][A-Za-z_0-9]*)", re.M),
}


def defined_names(text: str, key: str) -> set[str]:
    pat = DEFINITION.get(key)
    if pat is None:
        return set()
    out = set()
    for m in pat.finditer(_strip_comments(text, key if key.startswith(".") else ".sh")):
        out |= {g for g in m.groups() if g}
    return out


def duplicated_definitions(sides, key: str) -> set[str]:
    """Names BOTH sides define -- keeping both would define them twice."""
    dupes: set[str] = set()
    for ours, theirs in sides:
        dupes |= defined_names(ours, key) & defined_names(theirs, key)
    return dupes


def side_texts(path: str) -> list[tuple[str, str]]:
    return CONFLICT.findall(Path(path).read_text())


def resolve_json(path: str) -> tuple[bool, str]:
    """Parse both git sides and merge structurally. Never splice text."""
    def side(stage: int):
        r = subprocess.run(["git", "show", f":{stage}:{path}"],
                           capture_output=True, text=True)
        if r.returncode != 0:
            return None
        try:
            return json.loads(r.stdout)
        except json.JSONDecodeError as exc:
            return exc

    ours, theirs = side(2), side(3)
    for label, val in (("ours", ours), ("theirs", theirs)):
        if val is None:
            return False, f"{path}: cannot read the {label} stage"
        if isinstance(val, json.JSONDecodeError):
            return False, f"{path}: the {label} side is not valid JSON ({val})"

    conflicts: list[str] = []

    def merge(a, b, trail=""):
        if isinstance(a, dict) and isinstance(b, dict):
            out = dict(a)
            for k, v in b.items():
                out[k] = merge(a[k], v, f"{trail}.{k}") if k in a else v
            return out
        if isinstance(a, list) and isinstance(b, list):
            ids = ("fact_id", "id", "name")
            key = next(
                (i for i in ids
                 if all(isinstance(r, dict) and i in r for r in a + b)), None)
            if key is None:
                seen, out = set(), []
                for r in a + b:
                    s = json.dumps(r, sort_keys=True)
                    if s not in seen:
                        seen.add(s)
                        out.append(r)
                return out
            byk = {r[key]: r for r in a}
            for r in b:
                if r[key] in byk:
                    byk[r[key]] = merge(byk[r[key]], r, f"{trail}[{r[key]}]")
                else:
                    byk[r[key]] = r
            return [byk[k] for k in sorted(byk)]
        if a != b:
            conflicts.append(f"{trail or '<root>'}: {a!r} vs {b!r}")
        return b

    merged = merge(ours, theirs)
    if conflicts:
        head = "\n    ".join(conflicts[:6])
        more = "" if len(conflicts) <= 6 else f"\n    … (+{len(conflicts)-6} more)"
        return False, (
            f"{path}: {len(conflicts)} scalar(s) disagree and no rule says which "
            f"wins — resolve by hand:\n    {head}{more}"
        )
    Path(path).write_text(json.dumps(merged, indent=2) + "\n")
    return True, f"{path}: merged structurally (both sides parsed)"


def main() -> int:
    files = conflicted()
    if not files:
        print("LANE_MERGE_RESOLVE|nothing conflicted")
        return 2

    refused: list[str] = []
    for f in files:
        ext = Path(f).suffix
        if ext == ".json":
            ok, msg = resolve_json(f)
            print(f"  {msg}")
            if not ok:
                refused.append(f)
            continue

        sides = side_texts(f)
        if not sides:
            refused.append(f)
            print(f"  {f}: REFUSED — no conflict hunk parsed; look at it")
            continue

        key = "justfile" if Path(f).name == "justfile" else ext
        dupes = duplicated_definitions(sides, key)
        if dupes:
            refused.append(f)
            print(f"  {f}: REFUSED — both sides define {sorted(dupes)}; keeping "
                  f"both would define each twice. Merge those lines by hand "
                  f"(for a dependency list, take the UNION).")
            continue

        if ext in BALANCED:
            cut = [
                f"hunk {i+1} {label}: " + ", ".join(
                    f"{k}{v:+d}" for k, v in b.items() if v)
                for i, hunk in enumerate(sides)
                for label, b in (("ours", balance(hunk[0], ext)),
                                 ("theirs", balance(hunk[1], ext)))
                if any(b.values())
            ]
            if cut:
                refused.append(f)
                print(f"  {f}: REFUSED — a side is cut mid-item, so keeping both "
                      f"will not parse. Use `lane-merge-additive.py splice`.")
                for c in cut:
                    print(f"      {c}")
                continue

        text = Path(f).read_text()
        n = len(CONFLICT.findall(text))
        Path(f).write_text(CONFLICT.sub(lambda m: m.group(1) + "\n" + m.group(2), text))
        print(f"  {f}: {n} hunk(s) kept both")

    if refused:
        print(f"LANE_MERGE_RESOLVE|REFUSED|{len(refused)}: " + ", ".join(refused),
              file=sys.stderr)
        return 1
    print(f"LANE_MERGE_RESOLVE|resolved {len(files)} file(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

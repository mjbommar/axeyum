#!/usr/bin/env python3
"""The Python-binding coverage ledger: what the Rust workspace exposes, what
`crates/axeyum-py` references, and what plan 02 still owes.

`docs/python-2026-08/02-python-api.md` carries an exit criterion -- "every row
in the three inventories marked tier R is bound or has a recorded reason for
deferral" -- and until this script existed **nothing could evaluate it**. There
was no population, no join, and no way for a reader to tell "bound" from "not
looked at". That is the CLAUDE.md trap in its purest form: an empty answer from
a tool nobody pointed at the subject reads exactly like a strong negative.

So this derives the population instead of asserting it:

1. **Public surface.** Every `pub fn` / `pub struct` / `pub enum` / `pub trait`
   / `pub const` under each crate's `src/`, module-level and in `impl` blocks.
   `pub(crate)` / `pub(super)` / `pub(in ...)` are NOT public and are excluded;
   `#[cfg(test)]` modules, `mod tests`, items inside function bodies, and items
   under a non-`pub` module are excluded. Line scanner, brace-tracked.
2. **Binding references.** `crates/axeyum-py/src/**` with comments stripped
   (a doc comment naming `solve_smtlib` is not a call). A module-level item
   counts as referenced when its name is imported from, or written under, its
   own crate path; an inherent method counts when its *type* is referenced and
   the method name is called somewhere in the binding.
3. **Inventory join.** The three tables under
   `docs/python-2026-08/inventories/` supply the tier (R / P / C) and the
   `path:line` for the rows a human triaged.

# "referenced" is not "bound", and the word is chosen deliberately

A textual scan can see that `axeyum_cas::sturm` appears in the binding. It
cannot see whether every function in that module reached Python, whether the
wrapper is correct, or whether it is dead code behind a `#[cfg]`. So no column
here says "bound". `referenced=R` is an UPPER bound on what is bound, and the
backlog it produces is therefore a LOWER bound on what is owed. A ledger that
overstated the backlog would be annoying; one that understated it would be the
checker-that-cannot-fail defect, so the error is pushed to the annoying side.

# Deferrals are data, not judgement

A tier-R row that is deliberately not bound needs a REASON, and the reason lives
in `artifacts/python-coverage-deferrals.json`, hand-maintained, one entry per
item with a non-empty `reason` string. A deferral without a reason is refused
(exit 2) rather than counted -- an unexplained deferral and a forgotten item are
the same thing, and the point of the file is to keep them different.

# The claim guard

`U > 0` is the normal, healthy state of an unfinished plan, so it is NOT an
error on its own. It becomes an error the moment any document CLAIMS the exit
criterion is met while the ledger says otherwise: that pairing is a false claim
about this repository's own coverage, and it is exactly what a generated ledger
exists to make impossible. `CLAIM_PATTERNS` below is what is scanned for.

# Why `git_commit` is excluded from `--check`

A file cannot contain the identity of the commit that contains it. The field is
recorded because a reader needs to know which tree was measured, and it is
normalised away on both sides of the `--check` comparison. Everything else is
byte-compared.

Usage::

    python3 scripts/gen-python-coverage.py           # rewrite both artifacts
    python3 scripts/gen-python-coverage.py --check   # fail if either is stale
    python3 scripts/gen-python-coverage.py --json    # print the ledger, write nothing
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

JSON_OUT = "artifacts/python-coverage-v1.json"
MD_OUT = "docs/plan/generated/python-coverage.md"
DEFERRALS = "artifacts/python-coverage-deferrals.json"
BINDING = "crates/axeyum-py"
INVENTORY_DIR = "docs/python-2026-08/inventories"

#: Documents that must not claim plan 02's exit criterion while the backlog is
#: non-empty. The ledger's own output files are excluded (they REPORT the
#: number; reporting it is not claiming it).
CLAIM_SCAN_GLOBS = (
    "docs/python-2026-08/*.md",
    "docs/plan/status/*.md",
    "docs/plan/global/*.md",
)

#: A claim that plan 02's TIER-R exit criterion is SATISFIED. Deliberately
#: narrow in two directions.
#:
#: Narrow in SUBJECT: the criterion is quoted verbatim across this strand and
#: quoting it is not claiming it, so a completion word alone is not enough --
#: the sentence has to be about tier-R rows or about plan 02 by name. The first
#: draft matched `exit criterion ... achieved` anywhere and fired on
#: `03-agentic-layer.md:204`, a sentence about a DIFFERENT plan saying its
#: criterion and its result *differ*: the exact opposite of a claim.
#:
#: Narrow in POLARITY: `NOT_A_CLAIM` drops a line that denies, defers or
#: qualifies. A gate that reads "the exit criterion is not met" as a claim that
#: it is met would make honest reporting the thing it punishes.
CLAIM_PATTERNS = (
    re.compile(
        r"(?:tier[- ]R (?:row|rows|coverage|surface)|plan 02|02-python-api)"
        r"[^.\n]{0,160}\b(?:met|satisfied|complete|completed|achieved|closed)\b",
        re.IGNORECASE,
    ),
    re.compile(
        r"\bevery tier[- ]R row (?:is|has been|was) (?:bound|covered|projected|recorded)\b",
        re.IGNORECASE,
    ),
)

#: Polarity guard for `CLAIM_PATTERNS`; any hit disqualifies the line.
NOT_A_CLAIM = re.compile(
    r"\b(?:not|never|unmet|differ|differs|until|once|when|would|will be|remains?|"
    r"pending|outstanding|cannot|no longer claims?)\b",
    re.IGNORECASE,
)

KINDS = ("fn", "struct", "enum", "trait", "const")

#: Words the inventory's backticked-name fallback must never read as an item.
NOT_AN_ITEM = frozenset(
    """true false bool char str usize isize u8 u16 u32 u64 u128 i8 i16 i32 i64 i128
    f32 f64 self Self None Some Ok Err Vec String Option Result Box Rc Arc HashMap
    BTreeMap BTreeSet HashSet Duration impl pub fn mod use crate super dyn where
    match if else for while loop let mut const static ref move return""".split()
)

_FN = re.compile(
    r"^\s*pub(?P<restrict>\s*\([^)]*\))?\s+"
    r"(?:(?:const|async|unsafe|extern\s+\"[^\"]*\")\s+)*"
    r"fn\s+(?P<name>[A-Za-z_][A-Za-z0-9_]*)"
)
_TYPE = re.compile(
    r"^\s*pub(?P<restrict>\s*\([^)]*\))?\s+(?:unsafe\s+)?"
    r"(?P<kind>struct|enum|trait|union)\s+(?P<name>[A-Za-z_][A-Za-z0-9_]*)"
)
_CONST = re.compile(
    r"^\s*pub(?P<restrict>\s*\([^)]*\))?\s+"
    r"(?P<kind>const|static)\s+(?:mut\s+)?(?P<name>[A-Za-z_][A-Za-z0-9_]*)\s*:"
)
_MOD = re.compile(
    r"^\s*(?P<pub>pub(?P<restrict>\s*\([^)]*\))?\s+)?mod\s+(?P<name>[A-Za-z_][A-Za-z0-9_]*)"
)
_IMPL = re.compile(r"^\s*(?:unsafe\s+)?impl\b(?P<rest>.*)$")
_TRAIT_BLOCK = re.compile(r"^\s*(?:pub(?:\s*\([^)]*\))?\s+)?(?:unsafe\s+)?trait\s+")
_FN_BLOCK = re.compile(r"^\s*(?:pub(?:\s*\([^)]*\))?\s+)?(?:(?:const|async|unsafe|extern\s+\"[^\"]*\")\s+)*fn\s+")
_IMPL_TYPE = re.compile(r"(?P<ty>[A-Za-z_][A-Za-z0-9_]*)\s*(?:<[^{]*)?$")

_CHAR_LITERAL = re.compile(r"'(?:\\.|[^'\\])'")


class CoverageError(Exception):
    """A malformed input the ledger refuses to guess about."""


def _decomment(line: str, in_block: bool) -> tuple[str, bool]:
    """One line of Rust with comments and literal contents removed.

    Positional, one pass, strings BEFORE comments -- because both orders of the
    naive version are wrong and each is wrong invisibly. Stripping `//` first
    truncates `let s = "http://x";`; stripping `/*` first swallows the rest of
    the file the moment a doc comment writes `**F32**/**F64**`, which is a real
    line in `crates/axeyum-fp/src/lib.rs:946` and cost this scanner 31 of that
    crate's 61 `pub fn`s until it was measured against `grep -c`.
    """
    out: list[str] = []
    index = 0
    size = len(line)
    while index < size:
        if in_block:
            end = line.find("*/", index)
            if end < 0:
                return "".join(out), True
            index = end + 2
            in_block = False
            continue
        if line.startswith("//", index):
            break
        if line.startswith("/*", index):
            in_block = True
            index += 2
            continue
        if line[index] == '"':
            cursor = index + 1
            while cursor < size and line[cursor] != '"':
                cursor += 2 if line[cursor] == "\\" else 1
            out.append('""')
            index = cursor + 1
            continue
        found = _CHAR_LITERAL.match(line, index)
        if found is not None:
            out.append("''")
            index = found.end()
            continue
        out.append(line[index])
        index += 1
    return "".join(out), in_block


class Frame:
    __slots__ = ("kind", "name", "base", "skip", "public")

    def __init__(self, kind: str, name: str, base: int, skip: bool, public: bool) -> None:
        self.kind = kind
        self.name = name
        self.base = base
        self.skip = skip
        self.public = public


def scan_rust_file(path: Path, crate: str, rel: str) -> list[dict[str, object]]:
    """Public items in one `.rs` file. See the module docstring for the rules."""
    items: list[dict[str, object]] = []
    stack: list[Frame] = []
    depth = 0
    pending: list[str] = []
    in_block_comment = False
    for lineno, raw in enumerate(path.read_text(encoding="utf-8", errors="replace").splitlines(), 1):
        code, in_block_comment = _decomment(raw, in_block_comment)
        stripped = code.strip()
        if not stripped:
            continue
        if stripped.startswith("#["):
            pending.append(stripped)
            continue

        d0 = depth
        skip_here = any("cfg(test)" in a.replace(" ", "") for a in pending)
        in_skip = any(f.skip for f in stack)
        in_fn = any(f.kind == "fn" for f in stack)
        in_trait = any(f.kind == "trait" for f in stack)
        mods_public = all(f.public for f in stack if f.kind == "mod")
        impl_ty = next((f.name for f in reversed(stack) if f.kind == "impl"), None)

        if not (in_skip or skip_here or in_fn or in_trait):
            matched = _FN.match(code) or _TYPE.match(code) or _CONST.match(code)
            if matched is not None and matched.group("restrict") is None:
                name = matched.group("name")
                kind = "fn" if matched.re is _FN else matched.group("kind")
                if kind in ("union", "static"):
                    kind = "struct" if kind == "union" else "const"
                if kind in KINDS:
                    module = "::".join(f.name for f in stack if f.kind == "mod")
                    items.append(
                        {
                            "crate": crate,
                            "kind": kind,
                            "name": f"{impl_ty}::{name}" if impl_ty else name,
                            "bare": name,
                            "type": impl_ty or "",
                            "module": module,
                            "file": rel,
                            "line": lineno,
                            "reachable": mods_public,
                        }
                    )

        opened = "{" in code
        if opened:
            mod_match = _MOD.match(code)
            if mod_match is not None:
                is_test = skip_here or mod_match.group("name") == "tests"
                stack.append(
                    Frame(
                        "mod",
                        mod_match.group("name"),
                        d0,
                        is_test,
                        mod_match.group("pub") is not None and mod_match.group("restrict") is None,
                    )
                )
            elif _IMPL.match(code) is not None:
                rest = _IMPL.match(code).group("rest")
                head = rest.split("{", 1)[0]
                if " for " in head:
                    head = head.rsplit(" for ", 1)[1]
                head = head.split(" where ", 1)[0].strip()
                found = _IMPL_TYPE.search(head.replace("&", " ").strip())
                stack.append(Frame("impl", found.group("ty") if found else "?", d0, skip_here, True))
            elif _TRAIT_BLOCK.match(code) is not None:
                stack.append(Frame("trait", "", d0, skip_here, True))
            elif _FN_BLOCK.match(code) is not None:
                stack.append(Frame("fn", "", d0, skip_here, True))
            else:
                stack.append(Frame("block", "", d0, skip_here, True))

        depth += code.count("{") - code.count("}")
        while stack and depth <= stack[-1].base:
            stack.pop()
        pending = []
    return items


def workspace_crates(root: Path) -> list[tuple[str, Path]]:
    """(`axeyum-solver`, path) for every crate with a `src/`, sorted."""
    out: list[tuple[str, Path]] = []
    for manifest in sorted((root / "crates").glob("*/Cargo.toml")):
        name = manifest.parent.name
        for line in manifest.read_text(encoding="utf-8").splitlines():
            found = re.match(r'^name\s*=\s*"([^"]+)"', line.strip())
            if found is not None:
                name = found.group(1)
                break
        if (manifest.parent / "src").is_dir():
            out.append((name, manifest.parent))
    if not out:
        raise CoverageError("no crates found under crates/ -- wrong ROOT?")
    return out


def scan_public_surface(root: Path) -> dict[str, list[dict[str, object]]]:
    surface: dict[str, list[dict[str, object]]] = {}
    for crate, directory in workspace_crates(root):
        items: list[dict[str, object]] = []
        for path in sorted((directory / "src").rglob("*.rs")):
            rel = str(path.relative_to(root))
            items.extend(scan_rust_file(path, crate, rel))
        surface[crate] = items
    return surface


def strip_comments(text: str) -> str:
    """Rust source with `//`-comments and `/* */` blocks removed."""
    out: list[str] = []
    i = 0
    n = len(text)
    while i < n:
        if text.startswith("//", i):
            end = text.find("\n", i)
            i = n if end < 0 else end
        elif text.startswith("/*", i):
            end = text.find("*/", i + 2)
            i = n if end < 0 else end + 2
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append(text[i : j + 1])
            i = j + 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def scan_binding(root: Path) -> dict[str, object]:
    """What `crates/axeyum-py` names, per crate, with comments stripped."""
    src = root / BINDING / "src"
    if not src.is_dir():
        raise CoverageError(f"{BINDING}/src does not exist")
    per_crate: dict[str, set[str]] = {}
    calls: set[str] = set()
    files = 0
    pyclass = pyfunction = pymethod = 0
    for path in sorted(src.rglob("*.rs")):
        files += 1
        text = strip_comments(path.read_text(encoding="utf-8", errors="replace"))
        pyclass += len(re.findall(r"#\[pyclass", text))
        pyfunction += len(re.findall(r"#\[pyfunction", text))
        pymethod += len(re.findall(r"\bfn\s+[A-Za-z_]", text))
        for statement in re.findall(r"\buse\s+((?:.|\n)*?);", text):
            found = re.match(r"\s*axeyum_([a-z0-9_]+)\b", statement)
            if found is None:
                continue
            crate = f"axeyum-{found.group(1).replace('_', '-')}"
            per_crate.setdefault(crate, set()).update(
                re.findall(r"[A-Za-z_][A-Za-z0-9_]*", statement)
            )
        for found in re.finditer(r"axeyum_([a-z0-9_]+)((?:::[A-Za-z_][A-Za-z0-9_]*)+)", text):
            crate = f"axeyum-{found.group(1).replace('_', '-')}"
            per_crate.setdefault(crate, set()).update(found.group(2).split("::")[1:])
        calls.update(re.findall(r"\.([A-Za-z_][A-Za-z0-9_]*)\s*\(", text))
        calls.update(re.findall(r"::([A-Za-z_][A-Za-z0-9_]*)\s*\(", text))
        calls.update(re.findall(r"\b([A-Za-z_][A-Za-z0-9_]*)\s*\(", text))
        calls.update(re.findall(r"\b([A-Za-z_][A-Za-z0-9_]*)\s*\{", text))
    return {
        "per_crate": per_crate,
        "calls": calls,
        "files": files,
        "pyclasses": pyclass,
        "pyfunctions": pyfunction,
        "fn_definitions": pymethod,
    }


def reference_evidence(item: dict[str, object], binding: dict[str, object]) -> str:
    """"" when the binding never names this item; otherwise how it names it."""
    names: set[str] = binding["per_crate"].get(item["crate"], set())  # type: ignore[assignment]
    if not names:
        return ""
    bare = str(item["bare"])
    owner = str(item["type"])
    if owner:
        if owner in names and (bare in binding["calls"] or bare in names):  # type: ignore[operator]
            return "method-of-referenced-type"
        return ""
    if bare in names:
        return "named-in-crate-path"
    return ""


_TIER = re.compile(r"^\**\s*(R|P|C)(?:\s*/\s*(R|P|C))?\s*\**$")
_PATH = re.compile(r"([A-Za-z0-9_./-]+\.rs):(\d+)")
_SIG_ITEM = re.compile(
    r"pub\s+(?:(?:const|async|unsafe|extern\s+\"[^\"]*\")\s+)*"
    r"(fn|struct|enum|trait|const|type)\s+([A-Za-z_][A-Za-z0-9_]*)"
)
_SKIP_MARK = re.compile(r"\*\(([^)]*)\)\*")
_SECTION_CRATE = re.compile(r"axeyum-([a-z0-9-]+)")
_SECTION_TIER = re.compile(r"tier\s+([RPC])\b", re.IGNORECASE)

#: Section-heading -> crate, for inventory tables whose rows carry no crate cell.
FILE_CRATE_DEFAULT = {
    "smt-solver.md": "axeyum-solver",
    "cas.md": "axeyum-cas",
    "kernel-kg.md": "axeyum-lean-kernel",
}


def _cells(line: str) -> list[str]:
    body = line.strip()
    if body.startswith("|"):
        body = body[1:]
    if body.endswith("|"):
        body = body[:-1]
    return [c.strip() for c in body.split("|")]


def parse_inventories(root: Path, crates: list[str], file_index: dict[str, set[str]]) -> list[dict[str, object]]:
    """Rows of the three hand-written inventories, with their tier.

    The three tables do not share a column layout (`smt-solver.md` alone has
    four), so nothing here is positional: the tier is whichever cell IS a tier,
    the path is whichever cell holds a `foo.rs:123`, the signature is whichever
    cell declares an item. A row that carries no identifiable item is skipped
    and counted, never guessed at.
    """
    rows: list[dict[str, object]] = []
    for path in sorted((root / INVENTORY_DIR).glob("*.md")):
        default_crate = FILE_CRATE_DEFAULT.get(path.name, "")
        section = ""
        section_crate = default_crate
        section_tier = ""
        for lineno, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            if line.startswith("#"):
                # A `###` subsection INHERITS its parent's crate and tier. It is
                # only a `##` that resets them to the file default. Without this
                # every row under `### IR value/sort types` was filed against
                # `axeyum-solver` -- including `TermStats`, which the binding
                # imports from `axeyum-ir` and which therefore appeared in the
                # backlog as unbound while `crates/axeyum-py/src/ir/types.rs`
                # was using it.
                level = len(line) - len(line.lstrip("#"))
                section = line.lstrip("# ").strip()
                found = _SECTION_CRATE.search(section)
                if found is not None and f"axeyum-{found.group(1)}" in crates:
                    section_crate = f"axeyum-{found.group(1)}"
                elif level <= 2:
                    section_crate = default_crate
                tier = _SECTION_TIER.search(section)
                if tier is not None:
                    section_tier = tier.group(1).upper()
                elif level <= 2:
                    section_tier = ""
                continue
            if not line.strip().startswith("|") or set(line.strip()) <= set("|- :"):
                continue
            cells = _cells(line)
            if not cells or cells[0].lower() in ("path:line", "item", "crate", "artifact", "file"):
                continue
            tier = ""
            crate = ""
            location = ""
            signature = ""
            python_name = ""
            for cell in cells:
                bare = cell.strip("`* ")
                if not tier and _TIER.match(cell):
                    tier = _TIER.match(cell).group(0).strip("* ")
                if not crate and f"axeyum-{bare}" in crates:
                    crate = f"axeyum-{bare}"
                if not crate and bare in crates:
                    crate = bare
                if not location and _PATH.search(cell):
                    location = _PATH.search(cell).group(0)
                if _SIG_ITEM.search(cell) and len(cell) > len(signature):
                    signature = cell
                if not python_name and _SKIP_MARK.search(cell):
                    python_name = _SKIP_MARK.search(cell).group(1)
            items = [name for _, name in _SIG_ITEM.findall(signature)]
            if not items:
                # Rows that list bare names in backticks, e.g. `level_zero/level_succ`.
                # NOT_AN_ITEM exists because this fallback once produced the item
                # `false` (from a cell reading "hardcoded `false`, fail-closed")
                # and put it in the backlog as an unbound tier-R row.
                for cell in cells[:3]:
                    items.extend(
                        name
                        for name in re.findall(r"`([A-Za-z_][A-Za-z0-9_]*)`", cell)
                        if name not in NOT_AN_ITEM
                    )
                    if items:
                        break
            if not items:
                continue
            if not crate:
                crate = section_crate
            if location:
                stem = location.split(":")[0].split("/")[-1]
                owners = file_index.get(stem, set())
                if len(owners) == 1:
                    crate = next(iter(owners))
                elif len(owners) > 1 and crate in owners:
                    pass  # ambiguous file name; the section already named the crate
            rows.append(
                {
                    "source": f"{INVENTORY_DIR}/{path.name}:{lineno}",
                    "section": section,
                    "crate": crate or default_crate,
                    "tier": tier or section_tier,
                    "path": location,
                    "items": sorted(set(items)),
                    "inventory_skip": python_name,
                }
            )
    if not rows:
        raise CoverageError(f"{INVENTORY_DIR} produced zero rows -- the parser or the tables changed")
    return rows


def load_deferrals(root: Path) -> dict[str, dict[str, str]]:
    """The hand-maintained deferral file. A missing reason is refused."""
    path = root / DEFERRALS
    if not path.exists():
        raise CoverageError(f"{DEFERRALS} does not exist; create it (it may be `{{}}`)")
    document = json.loads(path.read_text(encoding="utf-8"))
    entries = document.get("deferrals") if isinstance(document, dict) else None
    if not isinstance(entries, dict):
        raise CoverageError(f"{DEFERRALS}: top level must be an object with a `deferrals` object")
    out: dict[str, dict[str, str]] = {}
    for key in sorted(entries):
        value = entries[key]
        if not isinstance(value, dict):
            raise CoverageError(f"{DEFERRALS}: {key} must be an object with a `reason`")
        reason = value.get("reason")
        if not isinstance(reason, str) or not reason.strip():
            raise CoverageError(f"{DEFERRALS}: {key} has no non-empty `reason` -- an unexplained deferral is a forgotten item")
        if ":" not in key:
            raise CoverageError(f"{DEFERRALS}: {key} must be keyed `<crate>:<item>`")
        out[key] = {"reason": reason.strip(), "slice": str(value.get("slice", ""))}
    return out


def deferral_for(crate: str, names: list[str], module: str, deferrals: dict[str, dict[str, str]]) -> str:
    """The deferral key covering any of `names` in `crate`, or ""."""
    for key in deferrals:
        key_crate, _, pattern = key.partition(":")
        if key_crate != crate:
            continue
        for name in names:
            candidates = {name, f"{module}::{name}" if module else name, module}
            if pattern.endswith("*"):
                prefix = pattern[:-1]
                if any(candidate.startswith(prefix) for candidate in candidates):
                    return key
            elif pattern in candidates:
                return key
    return ""


def git_commit(root: Path) -> str:
    try:
        done = subprocess.run(
            ["git", "-C", str(root), "rev-parse", "HEAD"],
            capture_output=True,
            text=True,
            check=False,
        )
    except OSError:
        return "unknown"
    return done.stdout.strip() if done.returncode == 0 and done.stdout.strip() else "unknown"


def build(root: Path) -> dict[str, object]:
    surface = scan_public_surface(root)
    crates = sorted(surface)
    file_index: dict[str, set[str]] = {}
    for crate, items in surface.items():
        for item in items:
            file_index.setdefault(str(item["file"]).split("/")[-1], set()).add(crate)
    binding = scan_binding(root)
    inventory = parse_inventories(root, crates, file_index)
    deferrals = load_deferrals(root)
    deferral_hits: dict[str, int] = {key: 0 for key in deferrals}

    referenced_names: dict[str, set[str]] = {}
    deferred_items: dict[str, int] = {key: 0 for key in deferrals}
    per_crate: list[dict[str, object]] = []
    for crate in crates:
        items = surface[crate]
        rows: list[str] = []
        hits = names = 0
        for item in sorted(items, key=lambda i: (str(i["file"]), int(i["line"]), str(i["name"]))):
            if not item["reachable"]:
                continue
            evidence = reference_evidence(item, binding)
            names += 1
            # The module used for matching is derived from the FILE, not from
            # inline `mod` blocks: `src/reconstruct/quant_bv.rs` is the module
            # `reconstruct::quant_bv` even though nothing in the source says so,
            # and a deferral covering a whole route has to be able to say
            # `axeyum-solver:reconstruct::*`.
            file_module = (
                str(item["file"]).split("/src/", 1)[-1].removesuffix(".rs").replace("/", "::")
            )
            key = deferral_for(
                crate,
                [str(item["bare"]), str(item["name"])],
                str(item["module"]) or file_module,
                deferrals,
            )
            if key:
                deferred_items[key] += 1
            if evidence:
                hits += 1
                referenced_names.setdefault(crate, set()).add(str(item["name"]))
                referenced_names[crate].add(str(item["bare"]))
            # One `|`-joined string per item rather than a nested array: with
            # `indent=2` a four-element array costs six lines, and this ledger
            # carries every public item in the workspace. One line per item
            # keeps the artifact diffable -- a new `pub fn` is a one-line diff.
            rows.append(f"{item['kind']}|{item['name']}|{item['file']}:{item['line']}|{evidence}")
        per_crate.append(
            {
                "crate": crate,
                "public": names,
                "referenced": hits,
                "items": rows,
                "items_format": "kind|name|file:line|reference_evidence",
            }
        )

    by_crate = {entry["crate"]: entry for entry in per_crate}
    for entry in per_crate:
        entry["inventoried"] = 0
        entry["tier_unassigned"] = 0
        entry["tier_r"] = 0
        entry["tier_r_unreferenced"] = 0
        entry["deferred"] = 0
        entry["backlog"] = []

    inventory_rows: list[dict[str, object]] = []
    excluded = 0
    for row in inventory:
        crate = str(row["crate"])
        entry = by_crate.get(crate)
        if entry is None:
            continue
        if crate == BINDING.split("/")[-1]:
            # Rows filed against the binding itself -- the `Cargo.toml` feature
            # matrix in `smt-solver.md` §7. They name items that belong to other
            # crates and are already counted there; counting them again here
            # would be double-counting, and dropping them silently would hide
            # part of the population. Counted, named, excluded.
            excluded += 1
            continue
        known = referenced_names.get(crate, set())
        names_here = [str(n) for n in row["items"]]
        is_referenced = any(name in known for name in names_here)
        key = deferral_for(crate, names_here, "", deferrals)
        if key:
            deferral_hits[key] += 1
        tier = str(row["tier"])
        entry["inventoried"] = int(entry["inventoried"]) + 1
        if not tier:
            entry["tier_unassigned"] = int(entry["tier_unassigned"]) + 1
        record = dict(row)
        record["referenced"] = is_referenced
        record["deferral"] = key
        inventory_rows.append(record)
        if "R" not in tier:
            continue
        entry["tier_r"] = int(entry["tier_r"]) + 1
        if key:
            entry["deferred"] = int(entry["deferred"]) + 1
            continue
        if is_referenced:
            continue
        entry["tier_r_unreferenced"] = int(entry["tier_r_unreferenced"]) + 1
        entry["backlog"].append(  # type: ignore[union-attr]
            {
                "items": names_here,
                "path": row["path"],
                "source": row["source"],
                "section": row["section"],
                "inventory_skip": row["inventory_skip"],
            }
        )

    totals = {
        "crates": len(crates),
        "public": sum(int(e["public"]) for e in per_crate),
        "referenced": sum(int(e["referenced"]) for e in per_crate),
        "inventoried": sum(int(e["inventoried"]) for e in per_crate),
        "tier_r": sum(int(e["tier_r"]) for e in per_crate),
        "tier_unassigned": sum(int(e["tier_unassigned"]) for e in per_crate),
        "deferral_entries": len(deferrals),
        "deferred_public_items": sum(deferred_items.values()),
        "inventory_rows_excluded_binding": excluded,
        "tier_r_unreferenced": sum(int(e["tier_r_unreferenced"]) for e in per_crate),
        "deferred": sum(int(e["deferred"]) for e in per_crate),
        "inventory_rows": len(inventory_rows),
    }
    return {
        "schema": "python-coverage-v1",
        "generated_by": "scripts/gen-python-coverage.py",
        "git_commit": git_commit(root),
        "git_commit_note": "excluded from --check: a file cannot carry the id of the commit containing it",
        "binding": {
            "crate": BINDING,
            "files": binding["files"],
            "pyclasses": binding["pyclasses"],
            "pyfunctions": binding["pyfunctions"],
            "fn_definitions": binding["fn_definitions"],
            "crates_referenced": sorted(binding["per_crate"]),
        },
        "totals": totals,
        "crates": per_crate,
        "inventory": inventory_rows,
        "deferrals": {
            key: {
                "reason": value["reason"],
                "slice": value["slice"],
                "matched_rows": deferral_hits[key],
                "matched_public_items": deferred_items[key],
            }
            for key, value in deferrals.items()
        },
    }


def census_line(ledger: dict[str, object]) -> str:
    totals = ledger["totals"]  # type: ignore[index]
    return (
        f"PYTHON_COVERAGE|crates={totals['crates']}|public={totals['public']}"
        f"|referenced={totals['referenced']}|inventoried={totals['inventoried']}"
        f"|tier_r_unreferenced={totals['tier_r_unreferenced']}|deferred={totals['deferred']}"
    )


def render_json(ledger: dict[str, object]) -> str:
    return json.dumps(ledger, indent=2, sort_keys=True, ensure_ascii=True) + "\n"


def render_markdown(ledger: dict[str, object]) -> str:
    totals = ledger["totals"]  # type: ignore[index]
    binding = ledger["binding"]  # type: ignore[index]
    out: list[str] = []
    out.append("# Python binding coverage ledger")
    out.append("")
    out.append(
        "Generated by `scripts/gen-python-coverage.py`. Do not edit. "
        "Source of truth for plan 02's exit criterion "
        "(`docs/python-2026-08/02-python-api.md`); the slice plan that consumes it is "
        "[`docs/python-2026-08/09-coverage-plan.md`](../../python-2026-08/09-coverage-plan.md)."
    )
    out.append("")
    out.append(f"`{census_line(ledger)}`")
    out.append("")
    out.append(
        "**`referenced` is an upper bound on `bound`.** It means the binding names the item "
        "with comments stripped -- not that a Python callable exists, is correct, or is tested. "
        "The backlog below is therefore a lower bound on what plan 02 still owes."
    )
    out.append("")
    out.append(
        f"Binding: `{binding['crate']}`, {binding['files']} files, "
        f"{binding['pyclasses']} `#[pyclass]`, {binding['pyfunctions']} `#[pyfunction]`, "
        f"{binding['fn_definitions']} `fn` definitions."
    )
    out.append("")
    out.append("## Per crate")
    out.append("")
    out.append(
        "| crate | public | referenced | inventoried | untiered | tier-R | "
        "tier-R unreferenced | deferred |"
    )
    out.append("|---|--:|--:|--:|--:|--:|--:|--:|")
    for entry in ledger["crates"]:  # type: ignore[index]
        out.append(
            f"| `{entry['crate']}` | {entry['public']} | {entry['referenced']} | "
            f"{entry['inventoried']} | {entry['tier_unassigned']} | {entry['tier_r']} | "
            f"{entry['tier_r_unreferenced']} | {entry['deferred']} |"
        )
    out.append(
        f"| **total** | **{totals['public']}** | **{totals['referenced']}** | "
        f"**{totals['inventoried']}** | **{totals['tier_unassigned']}** | "
        f"**{totals['tier_r']}** | **{totals['tier_r_unreferenced']}** | "
        f"**{totals['deferred']}** |"
    )
    out.append("")
    out.append(
        f"`untiered` is the honest hole in this join: {totals['tier_unassigned']} inventory rows "
        "sit in tables with no tier column and under a heading that names no tier, so they are "
        "NOT in the backlog even though some of them are read-only surface. Tiering them is "
        "an inventory edit, not a code change. "
        f"{totals['inventory_rows_excluded_binding']} further rows are filed against "
        f"`{BINDING}` itself (the `Cargo.toml` feature matrix) and are excluded as "
        "double-counting."
    )
    out.append("")
    out.append("## Backlog -- tier-R inventory rows neither referenced nor deferred")
    out.append("")
    out.append(
        "One bullet per inventory row. A row marked *(skip v1)* / *(later)* / *(v2)* in the "
        "inventory is flagged: the inventory recorded an intent, but plan 02's criterion asks "
        "for a recorded reason, which lives in "
        f"[`{DEFERRALS}`](../../../{DEFERRALS})."
    )
    out.append("")
    empty = True
    for entry in ledger["crates"]:  # type: ignore[index]
        backlog = entry["backlog"]
        if not backlog:
            continue
        empty = False
        out.append(f"### `{entry['crate']}` -- {len(backlog)} rows")
        out.append("")
        for row in backlog:
            names = ", ".join(f"`{name}`" for name in row["items"])
            where = f" (`{row['path']}`)" if row["path"] else ""
            mark = f" -- inventory marks *{row['inventory_skip']}*" if row["inventory_skip"] else ""
            out.append(f"- {names}{where}{mark} -- {row['source']}")
        out.append("")
    if empty:
        out.append("None. Every tier-R inventory row is referenced or carries a recorded deferral.")
        out.append("")
    out.append("## Recorded deferrals")
    out.append("")
    out.append(
        f"{totals['deferral_entries']} entries in "
        f"[`{DEFERRALS}`](../../../{DEFERRALS}), covering "
        f"{totals['deferred']} tier-R inventory rows and "
        f"{totals['deferred_public_items']} public Rust items. `deferred` in the census line "
        "and in the table above is the FIRST of those two numbers -- the one plan 02's exit "
        "criterion is about."
    )
    out.append("")
    out.append(
        "`rows` counts matched inventory rows, `items` matched public Rust items. A deferral "
        "matching zero of both is not an error -- the inventories do not cover every crate -- "
        "but it is worth a look, because it usually means the item was renamed."
    )
    out.append("")
    out.append("| key | rows | items | reason | slice |")
    out.append("|---|--:|--:|---|---|")
    for key, value in sorted(ledger["deferrals"].items()):  # type: ignore[index]
        reason = str(value["reason"]).replace("|", "\\|")
        out.append(
            f"| `{key}` | {value['matched_rows']} | {value['matched_public_items']} | "
            f"{reason} | {value['slice'] or '--'} |"
        )
    out.append("")
    return "\n".join(out)


def scan_claims(root: Path) -> list[str]:
    """Documents claiming plan 02's tier-R exit criterion is satisfied."""
    hits: list[str] = []
    for pattern in CLAIM_SCAN_GLOBS:
        for path in sorted(root.glob(pattern)):
            text = path.read_text(encoding="utf-8", errors="replace")
            for lineno, line in enumerate(text.splitlines(), 1):
                if NOT_A_CLAIM.search(line):
                    continue
                for claim in CLAIM_PATTERNS:
                    if claim.search(line):
                        hits.append(f"{path.relative_to(root)}:{lineno}: {line.strip()[:160]}")
    return hits


def _normalise(text: str) -> str:
    return re.sub(r'"git_commit": "[^"]*"', '"git_commit": "<normalised>"', text)


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--check", action="store_true", help="fail when either artifact is stale")
    parser.add_argument("--json", action="store_true", help="print the ledger; write nothing")
    parser.add_argument("--root", type=Path, default=ROOT)
    args = parser.parse_args(argv)

    try:
        ledger = build(args.root)
    except (CoverageError, OSError, json.JSONDecodeError) as error:
        print(f"python-coverage: {error}", file=sys.stderr)
        return 2

    if args.json:
        print(render_json(ledger), end="")
        return 0

    rendered = {JSON_OUT: render_json(ledger), MD_OUT: render_markdown(ledger)}
    stale: list[str] = []
    for relative, content in rendered.items():
        path = args.root / relative
        current = path.read_text(encoding="utf-8") if path.exists() else ""
        if _normalise(current) == _normalise(content):
            continue
        stale.append(relative)
        if not args.check:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content, encoding="utf-8")

    print(census_line(ledger))
    unreferenced = int(ledger["totals"]["tier_r_unreferenced"])  # type: ignore[index]
    claims = scan_claims(args.root)
    if unreferenced > 0 and claims:
        print(
            f"python-coverage: {unreferenced} tier-R inventory rows are neither referenced nor "
            "deferred, and the exit criterion is claimed met:",
            file=sys.stderr,
        )
        for hit in claims:
            print(f"  CLAIM {hit}", file=sys.stderr)
        return 1
    if stale and args.check:
        for relative in stale:
            print(f"  STALE {relative}")
        print("  regenerate: python3 scripts/gen-python-coverage.py")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))

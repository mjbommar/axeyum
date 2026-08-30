"""Parsing and receipt-building logic for the Mathlib module-import baseline.

This is the ONE place that knows how to turn a Mathlib checkout into a
compact, reproducible receipt (L1 phase G0, docs/plan/graph-directed-library-
roadmap-2026-08-30.md, ADR-0717). Both `gen-module-baseline.py` and
`check-module-baseline.py` import this module rather than each re-implementing
parsing, so there is exactly one parser to hash for "parser identity" and no
way for generate/verify logic to drift apart.

Determinism is a public promise here (CLAUDE.md): every list this module
produces is built from a `sorted(...)` call with an explicit key, never from
raw filesystem or dict/set iteration order. If a receipt ever differs between
two runs against the same source tree, look here first for an unsorted
iterable that leaked into the output.

No Mathlib checkout is vendored into this repository. The parser reads
whatever directory it is pointed at (default: the pinned checkout produced by
`scripts/provision-lean-import-toolchain.sh`, normally
`/data0/axeyum/lean-import-toolchain/mathlib4`) and never writes to it.
"""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
from collections import Counter
from pathlib import Path
from typing import Optional

SCHEMA_VERSION = 1

# Matches a real Lean4 import command after comments and string literals have
# been stripped: optional `public`/`private`, optional `meta`, then `import`,
# optional `all` (Lean's transitive/unfold import modifier), then a dotted
# module identifier. Anchored to line start (Lean import commands are always
# their own statement) so nothing mid-expression can match.
IMPORT_RE = re.compile(
    r"(?m)^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?"
    r"([A-Za-z][A-Za-z0-9_.]*)"
)


def strip_comments_and_strings(text: str) -> str:
    """Remove Lean block comments (nestable), line comments, and string
    literals from `text`, replacing removed spans with nothing (block/line
    comments) or a single space (strings), so byte offsets do not matter and
    no comment or string content can be mistaken for an import statement.

    This is the fix for a real false-positive class: Mathlib module doc
    comments illustrate import syntax with literal lines like `import A` /
    `import B` inside a `/-! ... -/` block (see
    Mathlib/Tactic/MinImports.lean), and a naive line-oriented grep counts
    those as edges.
    """
    out = []
    i = 0
    n = len(text)
    depth = 0
    while i < n:
        if depth > 0:
            if text.startswith("/-", i):
                depth += 1
                i += 2
                continue
            if text.startswith("-/", i):
                depth -= 1
                i += 2
                continue
            i += 1
            continue
        if text.startswith("/-", i):
            depth = 1
            i += 2
            continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            if j == -1:
                break
            i = j
            continue
        c = text[i]
        if c == '"':
            out.append(" ")
            i += 1
            while i < n and text[i] != '"':
                if text[i] == "\\":
                    i += 2
                else:
                    i += 1
            i += 1
            continue
        out.append(c)
        i += 1
    return "".join(out)


def _module_name(lean_file: Path, mathlib_parent: Path) -> str:
    rel = lean_file.relative_to(mathlib_parent)
    return str(rel.with_suffix("")).replace("/", ".")


def discover_lean_files(mathlib_dir: Path) -> list[Path]:
    """Return every `.lean` file under `<mathlib_dir>/Mathlib`, sorted by
    relative path for determinism. `mathlib_dir` is the mathlib4 repo root
    (the directory containing the `Mathlib/` subdirectory), matching the
    layout `scripts/provision-lean-import-toolchain.sh` produces.
    """
    root = mathlib_dir / "Mathlib"
    if not root.is_dir():
        return []
    return sorted(root.rglob("*.lean"))


def parse_module_graph(mathlib_dir: Path) -> dict:
    """Parse every `.lean` file under `<mathlib_dir>/Mathlib` and return the
    raw graph facts: the module set, and the multiset of (importer, target)
    edges split into internal (target is also a parsed module) and external.

    Edge counts are RAW import-statement counts, not deduplicated per
    (importer, target) pair -- two separate `import`/`meta import` lines
    naming the same target count as two edges. This matches the methodology
    behind the evidence baseline recorded in the roadmap (8,094 modules,
    25,495 internal direct-import edges, measured on server5) and was
    verified to reproduce it exactly against the pinned checkout.
    """
    mathlib_dir = Path(mathlib_dir)
    files = discover_lean_files(mathlib_dir)
    mathlib_parent = mathlib_dir

    modules: list[str] = [_module_name(f, mathlib_parent) for f in files]
    module_set = set(modules)

    internal_edges: list[tuple[str, str]] = []
    external_edges: list[tuple[str, str]] = []

    for f in files:
        mod = _module_name(f, mathlib_parent)
        text = f.read_text(encoding="utf-8", errors="replace")
        stripped = strip_comments_and_strings(text)
        for m in IMPORT_RE.finditer(stripped):
            target = m.group(1)
            if target in module_set:
                internal_edges.append((mod, target))
            else:
                external_edges.append((mod, target))

    return {
        "modules": modules,
        "module_set": module_set,
        "internal_edges": internal_edges,
        "external_edges": external_edges,
    }


def compute_degree_rows(internal_edges: list[tuple[str, str]]) -> dict:
    """Compute in-degree (import COUNT, i.e. how many statements import this
    module) and out-degree (how many statements this module's file issues)
    from the raw edge multiset, sorted deterministically by (-count, name).
    """
    indeg = Counter(dst for _src, dst in internal_edges)
    outdeg = Counter(src for src, _dst in internal_edges)
    top_indegree = sorted(indeg.items(), key=lambda kv: (-kv[1], kv[0]))
    top_outdegree = sorted(outdeg.items(), key=lambda kv: (-kv[1], kv[0]))
    return {
        "indegree": indeg,
        "outdegree": outdeg,
        "top_indegree": top_indegree,
        "top_outdegree": top_outdegree,
    }


def sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def compute_tree_hash(mathlib_dir: Path) -> tuple[str, int]:
    """Deterministic content hash over every `.lean` file under
    `<mathlib_dir>/Mathlib`: sha256 of the sorted `relpath\\tsha256(content)\\n`
    lines. This is the "hash for the external source" -- it catches ANY
    content drift (a stray local edit, a different checkout) independent of
    whatever commit hash a `.git` directory claims, and it needs no `git`
    command to verify, so it also works against a bare directory fixture.

    Returns (hash_hex, file_count).
    """
    files = discover_lean_files(mathlib_dir)
    lines = []
    for f in files:
        rel = f.relative_to(mathlib_dir)
        digest = sha256_hex(f.read_bytes())
        lines.append(f"{rel.as_posix()}\t{digest}\n")
    blob = "".join(lines).encode("utf-8")
    return sha256_hex(blob), len(files)


def git_commit(mathlib_dir: Path) -> Optional[str]:
    """Best-effort `git rev-parse HEAD` inside `mathlib_dir`. Returns None if
    it is not a git checkout (e.g. a test fixture) rather than raising, so
    callers must supply an explicit `--commit` override for non-git sources.
    """
    try:
        out = subprocess.run(
            ["git", "-C", str(mathlib_dir), "rev-parse", "HEAD"],
            capture_output=True,
            text=True,
            timeout=30,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    if out.returncode != 0:
        return None
    return out.stdout.strip()


def parser_identity() -> dict:
    """Hash of THIS file's own source -- the "parser identity" half of the
    drift guard. Any change to the parsing logic in this module changes this
    hash, independent of any change to the Mathlib source it parses.
    """
    self_path = Path(__file__).resolve()
    digest = sha256_hex(self_path.read_bytes())
    return {"path": "scripts/lib/module_baseline.py", "sha256": digest}


TOP_N_INDEGREE = 15
TOP_N_OUTDEGREE = 10


class SourceUnreachable(RuntimeError):
    """Raised when the source directory does not exist or is not a Mathlib
    checkout shape (no `Mathlib/` subdirectory)."""


class EmptySource(RuntimeError):
    """Raised when the source directory parses to zero modules. A run that
    parses nothing must never report a clean baseline -- see CLAUDE.md's
    'checker that cannot fail is worse than no checker'."""


def build_receipt(mathlib_dir: Path, commit_override: Optional[str] = None) -> dict:
    """Build the full compact receipt dict for `mathlib_dir`. Raises
    SourceUnreachable / EmptySource rather than returning a receipt describing
    nothing -- absence must be loud, never a silent zero.
    """
    mathlib_dir = Path(mathlib_dir)
    if not mathlib_dir.is_dir():
        raise SourceUnreachable(f"mathlib directory does not exist: {mathlib_dir}")
    if not (mathlib_dir / "Mathlib").is_dir():
        raise SourceUnreachable(
            f"no Mathlib/ subdirectory under {mathlib_dir} -- not a mathlib4 checkout"
        )

    graph = parse_module_graph(mathlib_dir)
    modules = graph["modules"]
    if len(modules) == 0:
        raise EmptySource(f"zero .lean modules found under {mathlib_dir}/Mathlib")

    internal_edges = graph["internal_edges"]
    external_edges = graph["external_edges"]
    degrees = compute_degree_rows(internal_edges)

    indeg = degrees["indegree"]
    no_importer_sinks = sorted(m for m in modules if indeg.get(m, 0) == 0)

    tree_hash, file_count = compute_tree_hash(mathlib_dir)
    commit = commit_override if commit_override is not None else git_commit(mathlib_dir)

    receipt = {
        "schema_version": SCHEMA_VERSION,
        "generated_by": "scripts/gen-module-baseline.py",
        "source": {
            "kind": "mathlib4",
            "commit": commit,
            "tree_hash_sha256": tree_hash,
            "file_count": file_count,
        },
        "parser": parser_identity(),
        "totals": {
            "modules": len(modules),
            "internal_edges": len(internal_edges),
            "external_edges": len(external_edges),
            "no_importer_sink_count": len(no_importer_sinks),
        },
        "top_indegree": [
            {"module": m, "indegree": c}
            for m, c in degrees["top_indegree"][:TOP_N_INDEGREE]
        ],
        "top_outdegree": [
            {"module": m, "outdegree": c}
            for m, c in degrees["top_outdegree"][:TOP_N_OUTDEGREE]
        ],
    }
    return receipt


def receipt_to_json(receipt: dict) -> str:
    """Canonical serialization: sorted keys, fixed indent, trailing newline.
    Two runs over the same source and parser must produce byte-identical
    output through this function.
    """
    return json.dumps(receipt, indent=2, sort_keys=True) + "\n"

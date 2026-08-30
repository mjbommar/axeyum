#!/usr/bin/env python3
"""Step 0 of a brief, run by the DISPATCHER instead of asked of the lane.

Measured 2026-08-29 over 272 lane status documents: mutation testing, which has
a harness and a gate, is followed 46% of the time; `examples/shape_search`,
which has only prose behind it, is used **4.8%** of the time -- and retrieval is
what this repository's own cost model names as the binding constraint on
marginal cost per theorem. Compliance tracks MECHANIZATION, not emphasis.

Thirteen-plus recorded instances of a lane re-deriving something that already
existed. The instruction "check whether it already exists" is in bold in every
brief and is still missed, because doing it well takes several careful tool
calls at the exact moment a lane is most eager to start.

So this tool does it for the lane, before the brief is written. It emits the
evidence a brief should CONTAIN rather than ASK FOR:

  1. Does the target already exist?  -- by comparing the fact's
     `formal.statement` against RENDERED TYPES from the kernel environment,
     never against names. A name search cannot find a lemma whose name you do
     not know, which is the case that has cost real work.
  2. What near-misses exist?         -- delegated to `examples/shape_search`,
     the shape index that already answers this. Not reimplemented.
  3. Which modules to read           -- including the duplicate-basename trap:
     `nat_prelude/` and `int_prelude/` share TEN basenames (algebra crt defs
     division euler fibonacci gcd ops order parity) and 58 repeat kernel-wide,
     so "look in gcd.rs" names two different files.
  4. Is the target already blocked?  -- held-out blind-evaluation population, a
     mutation negative control, or structurally blocked by the divergence
     registry. Delegated to `check-dispatchable-frontier.py`, which already
     computes exactly this partition.

Output is TEXT, pasteable into a brief. The consumer is a brief.

    python3 scripts/brief-step0.py F:ml430-nat-gcd-comm-…  [more ids…]
    python3 scripts/brief-step0.py --mathlib Nat.gcd_comm
    python3 scripts/brief-step0.py --refresh        # rebuild the snapshot
    python3 scripts/brief-step0.py --self-check     # the controls, no targets

# Speed, and why there is a snapshot at all

A brief-time tool that needs a fresh `--release` kernel build will not be run,
and not running it is the exact failure this exists to fix. Measured on s4:

    kernel_declaration_projection (all preludes, rendered types)   33 s
    shape_search --include-constructed                             30 s
    shape_search (no constructed preludes)                          1 s
    THIS TOOL against a warm snapshot                             < 1 s

So the environment is read ONCE into a content-addressed snapshot and every
query after that is a dictionary lookup.

# Staleness is structural, not advisory

A stale prebuilt reported a lemma ABSENT hours after it landed, and separately
reported a number from code that had since gained a size cap. A stale binary
misreports in every direction, so staleness here is not a warning the reader
may skip:

* The snapshot FILENAME carries `git rev-parse HEAD:crates/axeyum-lean-kernel`,
  so a snapshot built from a different kernel tree cannot be read as if it were
  current -- there is no in-band field to overlook.
* When no snapshot matches the current tree, the nearest is used and the
  DIFFERENCE is computed and printed: the declaration-name leaves that appear
  in today's sources and not in the snapshot's. If that set is empty the
  snapshot is reported EQUIVALENT (behind HEAD, but no new declaration names);
  otherwise it is STALE, every ABSENT verdict is marked PROVISIONAL and named
  against those leaves, and the process exits 4.
* The asymmetry is stated rather than implied: a stale snapshot can produce a
  false ABSENT (a declaration landed since) but not a false PRESENT.

Note the leaf-name delta is derived from SOURCE TEXT (`kernel.name_str(ns,
"leaf")` call sites) and is therefore a heuristic. It is used only to decide
whether the snapshot is stale -- never to answer whether a declaration exists.
This repository's standing rule that the theorem inventory cannot be read from
source text is intact: every verdict below is read from a kernel-built
snapshot.

# Every negative carries a positive control, in the same run

An empty answer and a broken query are the same observation. Before any
verdict, the matcher is run against a probe statement whose match certainly
exists (`∀ a b : ℕ, a + b = b + a` must retrieve `Nat.add_comm` at score 1.0).
If the probe fails, the run is UNANSWERABLE (exit 3) and prints no verdicts at
all -- a broken snapshot must never read as "nothing exists".

Exit status:
    0  report produced, snapshot matches the current kernel tree (or is
       EQUIVALENT to it)
    1  no target could be resolved -- nothing was reported
    2  usage error
    3  UNANSWERABLE: the built-in control probe failed, so no negative in this
       run would have meant anything
    4  report produced, but from a STALE snapshot; ABSENT verdicts are
       provisional
    5  a target is HELD-OUT and was refused; sections 1-3 were withheld for it

# A held-out target is refused, and only sections 1-3 are withheld

On 2026-08-29 an already-proved sweep ran this tool over all 181 open facts and
closed ten preregistered blind-evaluation rows. The sibling that answers the
narrower name-only question, `check-autogenesis-already-proved.py`, refuses a
held-out id even when it is named explicitly; this one did not, and the
unguarded one is the one that got used.

The guard here is not a copy of the sibling's. This tool's consumer is the
DISPATCHER, so "this target is held-out, do not dispatch it" is the most useful
sentence it can produce, and a tool that goes silent on exactly that target
sends the dispatcher to a less careful method. So the BLOCK is reported first
and loudly -- it used to be section 4, printed after the already-proved verdict,
which is the warning arriving after the leak -- and sections 1, 2 and 3 are
withheld, because naming the declaration that already proves a blind
proposition, or the near miss, or the module to read, IS the proof route.

There is no override flag: the legitimate route to working a held-out row is an
ADR-0542 amendment, which leaves a breach record where a flag leaves nothing.
"""

from __future__ import annotations

import argparse
import collections
import importlib.util
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import time
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
FACTS = ROOT / "artifacts" / "facts"
KERNEL_SRC = "crates/axeyum-lean-kernel"
PROJECTION_EXAMPLE = "kernel_declaration_projection"
SHAPE_EXAMPLE = "shape_search"

# The control probe. Its match certainly exists in every kernel this repository
# builds, so a run in which it does NOT match is a broken query, not a negative
# result. Kept deliberately boring: a probe that is interesting is a probe that
# can legitimately stop matching.
PROBE_STATEMENT = "∀ a b : ℕ, a + b = b + a"
PROBE_EXPECT = "Nat.add_comm"

# Carrier and sort tokens are dropped from the comparison multiset. A rendered
# type spells the carrier once per binder AND once per implicit type argument of
# `Eq` (`Eq.{1} AxNat …`), while a surface statement spells it once per binder
# group. Counting them makes an exact statement match score below an unrelated
# one; they are recorded as a CARRIER SET instead, which is the part that
# actually discriminates ℕ from ℤ from ℝ.
CARRIERS = {
    "AxNat": "Nat", "Nat": "Nat", "ℕ": "Nat",
    "Int": "Int", "ℤ": "Int",
    "Rat": "Rat", "ℚ": "Rat",
    "CReal": "CReal", "AxReal": "AxReal", "ℝ": "CReal",
    "Complex": "Complex", "ℂ": "Complex",
    "CPoint": "CPoint",
    "Prop": "Prop", "Sort": "Prop", "Type": "Prop", "Bool": "Bool",
    "String": "String",
}

# Lean-surface notation -> the kernel constant it renders as. Small, explicit
# and printed with every match, so a wrong entry is visible in the output rather
# than hidden inside a score.
NOTATION = {
    "↔": "Iff", "∧": "And", "∨": "Or", "¬": "Not",
    "=": "Eq", "≠": "Ne",
    "≤": "le", "<": "lt", "≥": "le", ">": "lt",
    "+": "add", "-": "sub", "*": "mul", "/": "div", "%": "mod",
    "∣": "dvd", "^": "pow",
    "∃": "Exists",
    "≡": "ModEq",
}
NUMERALS = {"0": "zero", "1": "one"}
# Binders, punctuation and elaboration noise that carry no kernel constant.
SURFACE_NOISE = {
    "forall", "fun", "let", "in", "if", "then", "else", "with", "by",
    "have", "show", "from", "this",
}

MODULE_GLOB = "crates/axeyum-lean-kernel"


# ---------------------------------------------------------------------------
# snapshot


def kernel_tree_sha(root: pathlib.Path) -> tuple[str, bool]:
    """`(tree sha of the kernel crate at HEAD, whether it is dirty on disk)`."""
    sha = subprocess.run(
        ["git", "-C", str(root), "rev-parse", f"HEAD:{KERNEL_SRC}"],
        capture_output=True, text=True, check=False).stdout.strip()
    dirty = subprocess.run(
        ["git", "-C", str(root), "status", "--porcelain", "--", KERNEL_SRC],
        capture_output=True, text=True, check=False).stdout.strip() != ""
    return sha or "unknown", dirty


def source_name_leaves(root: pathlib.Path) -> set[str]:
    """Declaration-name leaves visible in `kernel.name_str(ns, "leaf")` calls.

    A HEURISTIC, and used for exactly one purpose: deciding whether a snapshot
    built from an older kernel tree could be missing declarations. It never
    answers "does X exist" -- that is read from the kernel-built snapshot.
    """
    pattern = re.compile(r'name_str\(\s*[A-Za-z_0-9]+\s*,\s*"([A-Za-z0-9_.]+)"')
    leaves: set[str] = set()
    src = root / MODULE_GLOB / "src"
    base = src if src.is_dir() else root / MODULE_GLOB
    for path in base.rglob("*.rs"):
        try:
            leaves.update(pattern.findall(path.read_text(errors="replace")))
        except OSError:
            continue
    return leaves


def cache_dir() -> pathlib.Path:
    override = os.environ.get("AXEYUM_BRIEF_STEP0_CACHE")
    if override:
        return pathlib.Path(override)
    base = os.environ.get("XDG_CACHE_HOME") or str(pathlib.Path.home() / ".cache")
    return pathlib.Path(base) / "axeyum" / "brief-step0"


def snapshot_path(sha: str) -> pathlib.Path:
    return cache_dir() / f"snapshot-{sha}.json"


# Env overrides so the controls can drive a FIXTURE binary. Also useful when a
# lane wants to point at a build it made somewhere else.
BINARY_OVERRIDE = {
    PROJECTION_EXAMPLE: "AXEYUM_BRIEF_STEP0_PROJECTION_BIN",
    SHAPE_EXAMPLE: "AXEYUM_BRIEF_STEP0_SHAPE_BIN",
}


def find_binary(root: pathlib.Path, name: str) -> pathlib.Path | None:
    """Prefer this worktree's build, then the shared checkout's, then PATH."""
    override = os.environ.get(BINARY_OVERRIDE.get(name, ""))
    if override:
        path = pathlib.Path(override)
        return path if path.is_file() else None
    candidates = [root / "target" / "release" / "examples" / name]
    shared = subprocess.run(
        ["git", "-C", str(root), "rev-parse", "--path-format=absolute",
         "--git-common-dir"],
        capture_output=True, text=True, check=False).stdout.strip()
    if shared:
        candidates.append(
            pathlib.Path(shared).parent / "target" / "release" / "examples" / name)
    for candidate in candidates:
        if candidate.is_file() and os.access(candidate, os.X_OK):
            return candidate
    found = shutil.which(name)
    return pathlib.Path(found) if found else None


def newest_source_mtime(root: pathlib.Path) -> float:
    base = root / MODULE_GLOB
    return max((path.stat().st_mtime for path in base.rglob("*.rs")), default=0.0)


def build_snapshot(root: pathlib.Path, *, rebuild: bool,
                   allow_stale_binary: bool) -> dict[str, Any]:
    """Run `kernel_declaration_projection` and fold its rows into a snapshot.

    A snapshot produced by a binary OLDER than the kernel sources describes the
    environment that binary was compiled against, not today's. Stamping it with
    today's tree sha would make the freshness check below report EXACT about a
    44-hour-old answer -- the precise failure this tool exists to prevent, and
    the one it walked into on its first run. So the binary's own freshness is
    checked here, and a stale binary either stops the refresh or produces a
    snapshot whose recorded tree can never match anything.
    """
    if rebuild:
        wrapper = root / "scripts" / "cargo-serialized.sh"
        cargo = ([str(wrapper)] if wrapper.is_file() else ["cargo"])
        cmd = cargo + ["build", "--release", "-p", "axeyum-lean-kernel",
                       "--example", PROJECTION_EXAMPLE]
        print(f"[refresh] {' '.join(cmd)}", file=sys.stderr)
        done = subprocess.run(cmd, cwd=root, check=False)
        if done.returncode != 0:
            raise SystemExit(f"ERROR: build failed with status {done.returncode}")
    binary = find_binary(root, PROJECTION_EXAMPLE)
    if binary is None:
        raise SystemExit(
            f"ERROR: no {PROJECTION_EXAMPLE} binary; run with --refresh --build")
    binary_mtime = binary.stat().st_mtime
    source_mtime = newest_source_mtime(root)
    binary_stale = binary_mtime < source_mtime
    if binary_stale and not allow_stale_binary:
        raise SystemExit(
            f"ERROR: {binary} was built {(source_mtime - binary_mtime) / 3600:.1f} h "
            f"before the newest kernel source. It indexes the environment it was "
            f"COMPILED against, so a snapshot from it would be stamped with a "
            f"kernel tree it does not describe.\n"
            f"  rebuild:  python3 scripts/brief-step0.py --refresh --build\n"
            f"  or accept a permanently-STALE snapshot: --allow-stale-binary")
    print(f"[refresh] {binary}", file=sys.stderr)
    started = time.monotonic()
    done = subprocess.run([str(binary)], cwd=root, capture_output=True, text=True,
                          check=False)
    if done.returncode != 0:
        raise SystemExit(f"ERROR: {binary} exited {done.returncode}")
    elapsed = time.monotonic() - started

    rows: dict[str, dict[str, Any]] = {}
    for line in done.stdout.splitlines():
        parts = line.split("\t")
        if len(parts) < 8:
            continue
        label, kind, name, rendered = parts[0], parts[1], parts[2], parts[7]
        row = rows.setdefault(
            name, {"name": name, "kind": kind, "type": rendered, "groups": []})
        if label not in row["groups"]:
            row["groups"].append(label)
    sha, dirty = kernel_tree_sha(root)
    if binary_stale:
        # Deliberately unmatchable: `snapshot-stale-binary-…` is not a tree sha,
        # so `load_snapshot` can never report EXACT for it.
        sha = f"stale-binary-{int(binary_mtime)}"
    return {
        "schema_version": 1,
        "kind": "axeyum-brief-step0-snapshot",
        "kernel_tree": sha,
        "binary": str(binary),
        "binary_built_at": time.strftime("%Y-%m-%dT%H:%M:%S%z",
                                         time.localtime(binary_mtime)),
        "binary_stale": binary_stale,
        "kernel_tree_dirty": dirty,
        "head": subprocess.run(["git", "-C", str(root), "rev-parse", "HEAD"],
                               capture_output=True, text=True,
                               check=False).stdout.strip(),
        "built_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "build_seconds": round(elapsed, 1),
        "read_from": f"Kernel::environment() via examples/{PROJECTION_EXAMPLE}",
        "declaration_count": len(rows),
        "name_leaves": sorted(source_name_leaves(root)),
        "declarations": sorted(rows.values(), key=lambda r: r["name"]),
    }


def load_snapshot(root: pathlib.Path) -> tuple[dict[str, Any] | None, dict[str, Any]]:
    """Return `(snapshot, freshness)`; snapshot is None when none is cached."""
    sha, dirty = kernel_tree_sha(root)
    exact = snapshot_path(sha)
    if exact.is_file():
        snapshot = json.loads(exact.read_text())
        if snapshot.get("binary_stale"):
            return snapshot, {
                "state": "STALE", "path": exact, "kernel_tree": sha,
                "worktree_dirty": dirty, "new_leaves": [],
                "reason": "produced by a projection binary older than the "
                          "kernel sources; it indexes the environment it was "
                          "COMPILED against",
            }
        return snapshot, {
            "state": "EXACT", "path": exact, "kernel_tree": sha,
            "worktree_dirty": dirty, "new_leaves": [], "reason": "",
        }
    available = sorted(cache_dir().glob("snapshot-*.json"),
                       key=lambda p: p.stat().st_mtime, reverse=True) \
        if cache_dir().is_dir() else []
    if not available:
        return None, {"state": "MISSING", "path": None, "kernel_tree": sha,
                      "worktree_dirty": dirty, "new_leaves": [], "reason": ""}
    snapshot = json.loads(available[0].read_text())
    if snapshot.get("binary_stale"):
        return snapshot, {
            "state": "STALE", "path": available[0], "kernel_tree": sha,
            "worktree_dirty": dirty, "new_leaves": [],
            "reason": "produced by a projection binary older than the kernel "
                      "sources; it indexes the environment it was COMPILED "
                      "against",
        }
    new_leaves = sorted(source_name_leaves(root) - set(snapshot.get("name_leaves", [])))
    return snapshot, {
        "state": "STALE" if new_leaves else "EQUIVALENT",
        "path": available[0], "kernel_tree": sha, "worktree_dirty": dirty,
        "new_leaves": new_leaves,
        "reason": "declaration-name leaves appear in today's sources that the "
                  "snapshot does not carry" if new_leaves else "",
    }


# ---------------------------------------------------------------------------
# the matcher: surface statement vs RENDERED TYPE, never a name


IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_.']*")


def rendered_bag(rendered: str) -> tuple[collections.Counter, set[str]]:
    """Kernel constants of a rendered type, as a multiset, plus its carriers."""
    text = re.sub(r"\.\{[^}]*\}", "", rendered)
    bag: collections.Counter = collections.Counter()
    carriers: set[str] = set()
    for token in IDENT.findall(text):
        if re.fullmatch(r"x\d+", token):
            continue
        leaf = token.split(".")[-1]
        root = token.split(".")[0]
        if token in CARRIERS or leaf in CARRIERS:
            carriers.add(CARRIERS.get(token) or CARRIERS[leaf])
            continue
        if root in CARRIERS or root in {"Nat", "Int", "Rat"}:
            bag[leaf] += 1
        else:
            bag[leaf] += 1
    return bag, carriers


DECL_PREFIX = re.compile(r"^\s*(theorem|axiom|def|definition|lemma)\s+\S+\s*:\s*")
RENDERED_TELL = re.compile(r"\(x\d+\s*:|Eq\.\{|Sort\s*\(")


def strip_decl_prefix(statement: str) -> str:
    return DECL_PREFIX.sub("", statement, count=1).strip()


def is_rendered(statement: str) -> bool:
    """Is this `formal.statement` a KERNEL rendered type rather than Lean surface?

    The ledger carries both dialects. Some facts were written by pasting an
    inventory row -- `theorem Int.gcd_comm : ((x0 : Int) -> …)` -- and running
    those through the surface normalizer is not merely imprecise, it is WRONG in
    a way that looks like a result: `->` becomes `sub` and `lt` (from `-` and
    `>`), `x0`/`x1` become constants, and the target scores 0.18 against its own
    declaration. Measured on `F:int-gcd-comm` before this dispatch existed.
    """
    return bool(RENDERED_TELL.search(statement))


def statement_bag(statement: str) -> tuple[collections.Counter, set[str]]:
    """The comparison multiset, from whichever dialect the ledger used."""
    text = strip_decl_prefix(statement)
    return rendered_bag(text) if is_rendered(text) else surface_bag(text)


def surface_bag(statement: str) -> tuple[collections.Counter, set[str]]:
    """Same multiset, derived from a Lean-surface `formal.statement`.

    Deliberately shallow: notation maps to the kernel constant it renders as,
    identifiers contribute their last component, binder variables are dropped.
    The bag is PRINTED with every match, so a bad mapping shows up in the report
    rather than hiding inside a score.
    """
    bag: collections.Counter = collections.Counter()
    carriers: set[str] = set()
    # Binder groups `{m n : ℕ}` / `(a b : ℤ)` -- the variables are noise, the
    # ascribed type is the carrier.
    binders: set[str] = set()
    for opener, names, sort in re.findall(
            r"([({\[⦃])\s*([^:)}\]⦄]+?)\s*:\s*([^)}\]⦄]+)[)}\]⦄]", statement):
        del opener
        for var in names.split():
            binders.add(var)
        for token in IDENT.findall(sort) + re.findall(r"[ℕℤℚℝℂ]", sort):
            if token in CARRIERS:
                carriers.add(CARRIERS[token])
    # ASCII `->` FIRST: otherwise `-` becomes `sub` and `>` becomes `lt`, and
    # the target scores against its own declaration at 0.18.
    body = statement.replace("->", " ")
    for symbol, constant in NOTATION.items():
        body = body.replace(symbol, f" {constant} ")
    for glyph in "ℕℤℚℝℂ":
        if glyph in statement:
            carriers.add(CARRIERS[glyph])
    body = re.sub(r"[∀{}()\[\],:⦃⦄→\n]", " ", body)
    for token in body.split():
        if token in NUMERALS:
            bag[NUMERALS[token]] += 1
            continue
        if not IDENT.fullmatch(token):
            continue
        if token in binders or token in SURFACE_NOISE:
            continue
        leaf = token.split(".")[-1]
        if token in CARRIERS or leaf in CARRIERS:
            carriers.add(CARRIERS.get(token) or CARRIERS[leaf])
            continue
        if len(leaf) == 1 and leaf.islower():
            continue  # an unbound single-letter variable
        bag[leaf] += 1
    return bag, carriers


def score(target: collections.Counter, candidate: collections.Counter) -> float:
    """Multiset Jaccard. 1.0 means the constants and their counts agree."""
    if not target and not candidate:
        return 0.0
    inter = sum((target & candidate).values())
    union = sum((target | candidate).values())
    return inter / union if union else 0.0


def rank(statement: str, declarations: list[dict[str, Any]], limit: int
         ) -> tuple[list[tuple[float, dict[str, Any]]], collections.Counter, set[str]]:
    want, want_carriers = statement_bag(statement)
    scored: list[tuple[float, dict[str, Any]]] = []
    for row in declarations:
        got, got_carriers = rendered_bag(row["type"])
        value = score(want, got)
        if want_carriers and got_carriers and not (want_carriers & got_carriers):
            value *= 0.5  # a ℕ statement matching an ℝ declaration is a near miss
        if value > 0.0:
            scored.append((value, row))
    scored.sort(key=lambda pair: (-pair[0], pair[1]["name"]))
    return scored[:limit], want, want_carriers


# ---------------------------------------------------------------------------
# modules (item 3): the duplicate-basename trap


def module_index(root: pathlib.Path) -> dict[str, list[str]]:
    base = root / MODULE_GLOB / "src"
    index: dict[str, list[str]] = {}
    if not base.is_dir():
        return index
    for path in base.rglob("*.rs"):
        index.setdefault(path.stem, []).append(
            str(path.relative_to(root / MODULE_GLOB / "src")))
    for paths in index.values():
        paths.sort()
    return index


def declaring_files(root: pathlib.Path, name: str) -> list[str]:
    """Source files that name this declaration's leaf, best effort.

    Names reach the kernel through `kernel.name_str(ns, "leaf")`, so the leaf
    IS a source string even though `.theorem("…")` is not. Reported as a
    pointer, not as evidence of existence.
    """
    leaf = name.split(".")[-1]
    base = root / MODULE_GLOB / "src"
    if not base.is_dir():
        return []
    done = subprocess.run(
        ["/usr/bin/grep", "-rlF", f'"{leaf}"', str(base)],
        capture_output=True, text=True, check=False)
    return sorted(str(pathlib.Path(line).relative_to(base))
                  for line in done.stdout.splitlines() if line)


# ---------------------------------------------------------------------------
# blocked (item 4): delegated to check-dispatchable-frontier.py


def load_frontier_module(root: pathlib.Path):
    path = root / "scripts" / "check-dispatchable-frontier.py"
    if not path.is_file():
        return None
    spec = importlib.util.spec_from_file_location("axeyum_dispatchable", path)
    if spec is None or spec.loader is None:
        return None
    module = importlib.util.module_from_spec(spec)
    try:
        spec.loader.exec_module(module)
    except Exception:  # noqa: BLE001 -- a broken sibling must not kill the report
        return None
    return module


class HeldOutUnanswerable(RuntimeError):
    """The partition data could not be read, so blindness cannot be checked."""


def is_held_out(module, fact_id: str) -> bool:
    """FAIL-CLOSED. An unreadable partition is not a licence to report.

    `blocked_report` degrades to an UNANSWERABLE line and keeps going, which is
    right for a section that only annotates. It is wrong here: this answer gates
    whether the retrieval sections run at all, and a frontier module that failed
    to import would otherwise read as "not held-out" and publish a proof route
    for a blind row.
    """
    if module is None:
        raise HeldOutUnanswerable(
            "check-dispatchable-frontier.py did not load, so no target's "
            "partition can be read")
    try:
        held, _mutation = module.load_partitions(module.DEFAULT_NURSERY,
                                                 module.DEFAULT_EXTENSION)
    except SystemExit as exc:
        raise HeldOutUnanswerable(f"the nursery manifests are unreadable: {exc}")
    if not held:
        raise HeldOutUnanswerable(
            "the held-out population is empty; this check would pass vacuously "
            "for every target")
    return fact_id in held


def blocked_report(module, fact_id: str, statement: str) -> list[str]:
    if module is None:
        return ["blocked: UNANSWERABLE -- check-dispatchable-frontier.py did not load"]
    lines: list[str] = []
    try:
        held, mutation = module.load_partitions(module.DEFAULT_NURSERY,
                                                module.DEFAULT_EXTENSION)
        registry = module.load_registry(module.DEFAULT_REGISTRY)
    except SystemExit as exc:
        return [f"blocked: UNANSWERABLE -- {exc}"]
    lines.append(
        f"positive control: {len(held)} held-out ids, {len(mutation)} mutation "
        f"controls, {len(registry)} diverging constructions loaded")
    verdicts: list[str] = []
    if fact_id in held:
        verdicts.append(
            "HELD-OUT -- blind evaluation population (ADR-0542). Dispatching "
            "this spends the whole statement-shape family, not one row.")
    if fact_id in mutation or "-mutation-" in fact_id:
        verdicts.append(
            "MUTATION CONTROL -- deliberately perturbed, often false, never "
            "closable. Do not dispatch.")
    hits = module.blockers_for(statement, registry) if statement else []
    for hit in hits:
        verdicts.append(
            f"DIVERGENCE-BLOCKED on {hit['mathlib_constant']} "
            f"({hit['class']}) -- a construction-level divergence no proof "
            f"effort resolves.")
    lines.extend(verdicts or ["DISPATCHABLE -- not held-out, not a mutation "
                              "control, no registry blocker."])
    return lines


# ---------------------------------------------------------------------------
# near misses (item 2): delegated to examples/shape_search


def rendered_heads(statement: str) -> tuple[str | None, list[str]]:
    """`(conclusion head, hypothesis heads)` from a KERNEL rendered type.

    Peels `(xN : T) ->` binders off the front. A binder whose type is a carrier
    (`(x0 : AxNat)`) is a quantified VARIABLE, not a hypothesis, so only the
    others contribute heads -- which is the same distinction `shape_index`
    makes when it files `Nat -> Nat -> Nat.le -> …`.
    """
    text = statement.strip()
    hyps: list[str] = []
    binder = re.compile(r"^\(*\s*\(x\d+\s*:\s*")
    while binder.match(text):
        text = binder.sub("", text, count=1)
        depth, index = 0, 0
        while index < len(text):
            char = text[index]
            if char in "({[":
                depth += 1
            elif char in ")}]":
                if depth == 0:
                    break
                depth -= 1
            index += 1
        head = head_of_rendered(text[:index])
        if head and head not in CARRIERS:
            hyps.append(head)
        text = text[index + 1:].lstrip()
        text = text[2:].lstrip() if text.startswith("->") else text
    return head_of_rendered(text), hyps


def head_of_rendered(chunk: str) -> str | None:
    chunk = re.sub(r"\.\{[^}]*\}", "", chunk).strip().lstrip("(").strip()
    match = IDENT.match(chunk)
    return match.group(0) if match else None


def surface_heads(statement: str) -> tuple[str | None, list[str]]:
    """`(conclusion head, hypothesis heads)` for a `shape_search` query."""
    statement = strip_decl_prefix(statement)
    if is_rendered(statement):
        return rendered_heads(statement)
    body = statement
    body = re.sub(r"^\s*(∀|∃)[^,]*,", "", body).strip()
    depth = 0
    chunks: list[str] = []
    current = ""
    index = 0
    while index < len(body):
        char = body[index]
        if char in "({[":
            depth += 1
        elif char in ")}]":
            depth -= 1
        if depth == 0 and body.startswith("→", index):
            chunks.append(current)
            current = ""
            index += 1
            continue
        current += char
        index += 1
    chunks.append(current)
    heads = [head_of(chunk) for chunk in chunks]
    concl = heads[-1] if heads else None
    hyps = [head for head in heads[:-1] if head]
    return concl, hyps


def head_of(chunk: str) -> str | None:
    chunk = chunk.strip()
    if not chunk:
        return None
    for symbol in ("↔", "∧", "∨", "=", "≠", "≤", "<", "≥", ">", "∣"):
        if symbol in chunk:
            return NOTATION[symbol]
    match = IDENT.search(chunk)
    return match.group(0) if match else None


LOGIC_HEADS = {"Iff", "And", "Or", "Not", "Eq", "Ne", "Exists", "True", "False"}


def qualify(head: str, carrier: str | None) -> str:
    """`le` over ℕ is the kernel constant `Nat.le`, not `le`.

    `shape_search` compares WHOLE rendered names, so an unqualified operator
    head is answered UNANSWERABLE (exit 3) rather than absent -- correct, and
    useless. Logic constants are already whole names and are left alone.
    """
    if head in LOGIC_HEADS or "." in head or head[:1].isupper():
        return head
    return f"{carrier}.{head}" if carrier else head


def run_shape_search(root: pathlib.Path, concl: str | None, hyps: list[str],
                     carriers: set[str], timeout: int) -> list[str]:
    binary = find_binary(root, SHAPE_EXAMPLE)
    if binary is None:
        return [f"shape_search: NOT BUILT. Run: cargo build --release "
                f"-p axeyum-lean-kernel --example {SHAPE_EXAMPLE}"]
    if not concl and not hyps:
        return ["shape_search: no head could be derived from the statement -- "
                "query it by hand."]
    age = time.time() - binary.stat().st_mtime
    out = [f"(binary {binary}, built {age / 3600:.1f} h ago -- a stale "
           f"shape_search reports a RECENT declaration as ABSENT)"]
    # Try each carrier's qualification in turn. Exit 3 means the query named a
    # constant the index does not carry, which is a QUERY fault, not a negative
    # result -- so it is worth another spelling before reporting anything.
    variants = [carrier for carrier in sorted(carriers)] or [None]
    variants.append(None)
    for carrier in variants:
        argv = [str(binary)]
        if carriers & {"CReal", "Complex", "CPoint"}:
            argv.append("--include-constructed")
        if concl:
            argv += ["--concl", qualify(concl, carrier)]
        for hyp in hyps[:3]:
            argv += ["--hyp", qualify(hyp, carrier)]
        argv += ["--limit", "8"]
        out.append(f"$ {' '.join(argv)}")
        try:
            done = subprocess.run(argv, cwd=root, capture_output=True, text=True,
                                  timeout=timeout, check=False)
        except subprocess.TimeoutExpired:
            out.append(f"DID NOT RUN -- exceeded {timeout}s. Treat as "
                       f"unmeasured, never as absent.")
            return out
        out += (done.stdout + done.stderr).strip().splitlines()
        out.append(f"(exit {done.returncode}; 3 = UNANSWERABLE, not absent)")
        if done.returncode != 3:
            return out
    return out


# ---------------------------------------------------------------------------
# facts


def load_facts() -> dict[str, dict[str, Any]]:
    facts: dict[str, dict[str, Any]] = {}
    if not FACTS.is_dir():
        return facts
    for path in sorted(FACTS.glob("*.json")):
        try:
            doc = json.loads(path.read_text())
        except json.JSONDecodeError:
            continue
        ident = doc.get("id")
        if isinstance(ident, str):
            doc["_path"] = str(path.relative_to(ROOT))
            facts[ident] = doc
    return facts


def resolve(token: str, facts: dict[str, dict[str, Any]]) -> list[str]:
    if token in facts:
        return [token]
    lowered = token.lower()
    hits = [i for i in facts if lowered in i.lower()]
    if hits:
        return sorted(hits)
    # `--mathlib Nat.gcd_comm` -> the mirror whose id encodes that name.
    slug = re.sub(r"[^a-z0-9]+", "-", token.lower()).strip("-")
    return sorted(i for i in facts if slug and slug in i.lower())


# ---------------------------------------------------------------------------
# report


def emit(lines: list[str]) -> None:
    print("\n".join(lines))


def freshness_banner(fresh: dict[str, Any], snapshot: dict[str, Any]) -> list[str]:
    state = fresh["state"]
    out = [f"SNAPSHOT   {state}  kernel_tree={fresh['kernel_tree'][:12]} "
           f"declarations={snapshot.get('declaration_count', 0)} "
           f"built={snapshot.get('built_at', '?')}"]
    if fresh["worktree_dirty"]:
        out.append("           worktree kernel sources are DIRTY -- the "
                   "snapshot cannot reflect uncommitted declarations")
    if state == "EQUIVALENT":
        out.append(f"           built from {snapshot.get('kernel_tree', '?')[:12]}, "
                   "behind HEAD, but NO new declaration-name leaf appears in "
                   "today's sources")
    if state == "STALE":
        out.append(f"           reason: {fresh.get('reason', 'unknown')}")
        out.append(f"           projection binary {snapshot.get('binary', '?')} "
                   f"built {snapshot.get('binary_built_at', '?')}")
        if fresh["new_leaves"]:
            out.append(f"           {len(fresh['new_leaves'])} declaration-name "
                       f"leaf/leaves appear in today's sources and not in it.")
            out.append(f"           e.g. {', '.join(fresh['new_leaves'][:12])}")
        out.append("           => every ABSENT below is PROVISIONAL. A stale "
                   "snapshot can produce a false ABSENT, never a false PRESENT.")
        out.append("           Refresh: python3 scripts/brief-step0.py "
                   "--refresh --build")
    return out


def control_probe(declarations: list[dict[str, Any]]) -> tuple[bool, str]:
    ranked, _, _ = rank(PROBE_STATEMENT, declarations, 3)
    if not ranked:
        return False, "the probe statement matched nothing at all"
    best_score, best = ranked[0]
    names = [row["name"] for _, row in ranked]
    if PROBE_EXPECT not in names:
        return False, (f"probe {PROBE_STATEMENT!r} did not retrieve "
                       f"{PROBE_EXPECT}; top was {best['name']} at {best_score:.2f}")
    return True, (f"probe {PROBE_STATEMENT!r} retrieves {PROBE_EXPECT} "
                  f"(top-3 {', '.join(names)})")


def report_target(root: pathlib.Path, fact: dict[str, Any], snapshot: dict[str, Any],
                  fresh: dict[str, Any], modules: dict[str, list[str]],
                  frontier, args) -> bool:
    """Report on one target. Returns True if it was refused as held-out.

    A held-out target gets the BLOCK and nothing else -- see `refuse_held_out`.
    """
    ident = fact.get("id", "?")
    formal = fact.get("formal") or {}
    statement = formal.get("statement") or ""
    declarations = snapshot["declarations"]

    head = ["", "=" * 78,
            f"TARGET  {ident}",
            f"        {fact.get('title', '')}",
            f"        status={fact.get('epistemic_status', '?')}/"
            f"{fact.get('external_status', '?')}  fragment="
            f"{formal.get('fragment', '?')}  file={fact.get('_path', '?')}"]

    try:
        held = is_held_out(frontier, ident)
    except HeldOutUnanswerable as exc:
        emit(head + ["-" * 78] + refuse_held_out(ident, unanswerable=str(exc)))
        return True
    if held:
        emit(head + ["-" * 78] + refuse_held_out(ident))
        return True

    out = head + [
        f"        formal.statement: {statement or '(none)'}",
        "-" * 78,
        "1. ALREADY IN THE ENVIRONMENT?  (rendered types, never names)"]

    if not statement:
        out.append("   UNANSWERABLE -- this fact carries no `formal.statement`, "
                   "so there is nothing to compare a rendered type against.")
    else:
        ranked, want, carriers = rank(statement, declarations, args.limit)
        out.append(f"   dialect: "
                   f"{'kernel-rendered' if is_rendered(strip_decl_prefix(statement)) else 'lean-surface'}")
        out.append(f"   statement constants: "
                   f"{dict(sorted(want.items())) or '{}'}  carriers="
                   f"{sorted(carriers) or '[]'}")
        exact = [(value, row) for value, row in ranked if value >= 0.999]
        if exact:
            out.append(f"   verdict: PRESENT -- {len(exact)} declaration(s) whose "
                       f"rendered type has exactly these constants")
            out.append("   NOTE a constant multiset cannot see argument ORDER, so "
                       "left/right variants collide (`Int.add_assoc` and "
                       "`Int.add_left_comm` both score 1.00 against `a+b+c = "
                       "a+(b+c)`). READ the rendered type before flipping a "
                       "status; 1.00 is a candidate, not a verdict.")
        elif ranked and ranked[0][0] >= args.threshold:
            out.append(f"   verdict: LIKELY PRESENT -- best score "
                       f"{ranked[0][0]:.2f} (threshold {args.threshold})")
        else:
            provisional = " (PROVISIONAL -- snapshot STALE)" \
                if fresh["state"] == "STALE" else ""
            out.append(f"   verdict: ABSENT{provisional} -- nothing scores "
                       f">= {args.threshold} over "
                       f"{len(declarations)} declarations")
        for value, row in ranked:
            files = declaring_files(root, row["name"]) if args.files else []
            out.append(f"   [{value:.2f}] {row['name']}  {row['kind']}  "
                       f"groups=[{','.join(row['groups'])}]")
            out.append(f"          {row['type'][:400]}")
            if files:
                out.append(f"          declared near: {', '.join(files[:4])}")

    out += ["-" * 78,
            "2. NEAR MISSES BY SHAPE  (delegated to examples/shape_search)"]
    if statement and not args.no_shape_search:
        concl, hyps = surface_heads(statement)
        _, carriers = statement_bag(statement)
        out.append(f"   derived heads: concl={concl!r} hyps={hyps!r}")
        out += [f"   {line}" for line in
                run_shape_search(root, concl, hyps, carriers, args.shape_timeout)]
    elif args.no_shape_search:
        out.append("   skipped (--no-shape-search)")
    else:
        out.append("   skipped -- no statement to derive heads from")

    out += ["-" * 78,
            "3. MODULES TO READ  (duplicate basenames named BOTH ways)"]
    topics = topic_tokens(ident, statement, str(fact.get("title", "")))
    out.append(f"   topics from the target: {sorted(topics) or '[]'}")
    named = 0
    for topic in sorted(topics):
        paths = modules.get(topic)
        if not paths:
            continue
        named += 1
        flag = "  <-- SHARED BASENAME, read BOTH" if len(paths) > 1 else ""
        out.append(f"   {topic}.rs -> {', '.join(paths)}{flag}")
    if named == 0:
        out.append(f"   no module basename matches a topic token "
                   f"(positive control: {len(modules)} distinct basenames "
                   f"indexed under {MODULE_GLOB}/src)")

    out += ["-" * 78, "4. IS THE TARGET BLOCKED?"]
    out += [f"   {line}" for line in blocked_report(frontier, ident, statement)]
    emit(out)
    return False


def refuse_held_out(fact_id: str, unanswerable: str | None = None) -> list[str]:
    """What a brief about a held-out target should say, and nothing more.

    WHY THIS REFUSES SECTIONS 1-3 BUT NOT THE VERDICT ITSELF
    --------------------------------------------------------
    `check-autogenesis-already-proved.py` refuses a held-out id outright, even
    when named explicitly, and says so in its docstring. This tool was written
    hours later for the same question and had no such guard, and on 2026-08-29
    an already-proved sweep used THIS one and closed ten preregistered
    blind-evaluation rows (`92a61164e`). Two implementations of "is this already
    proved", one with the guard and one without, and the unguarded one got used.

    Copying the sibling's blanket refusal would be the wrong repair, because the
    two tools have different consumers. The sibling screens a SET and its output
    is a report; going quiet costs a row's line. This one is run by the
    DISPATCHER on a specific target, and its whole output is what a brief should
    contain -- so "this is held-out, do not dispatch it" is the single most
    valuable thing it can say, and a tool that exits silently on the one target
    where the dispatcher most needs an answer just sends them to a less careful
    method. That is how the sweep happened.

    So the split is by SECTION, not by target:

      * The BLOCK is reported, loudly and first. It was previously section 4,
        printed AFTER the already-proved verdict -- the warning arrived after
        the leak.
      * Sections 1-3 are withheld. Naming the kernel declaration whose rendered
        type matches a blind proposition IS the proof route; so is a
        shape-indexed near miss, and so is "read these modules". Those three are
        what spends the row, and they are the only three withheld.

    There is deliberately NO override flag. An escape hatch a lane can pass is
    how a guard stops being one, and the legitimate way to work a held-out row
    already exists: record an ADR-0542 amendment, after which the row is not
    held-out and this tool answers it normally. The amendment IS the flag, and
    it leaves a breach record behind where a flag leaves nothing.
    """
    if unanswerable is not None:
        return [
            "REFUSED: UNANSWERABLE -- blindness could not be checked",
            f"   {unanswerable}",
            "   Sections 1-3 are withheld: an unreadable partition is not a "
            "licence to publish a proof route.",
        ]
    return [
        "REFUSED: HELD-OUT -- blind evaluation population (ADR-0542)",
        f"   {fact_id} is preregistered held-out. Dispatching it spends the "
        f"whole statement-shape family, not one row.",
        "   Sections 1-3 (already-in-the-environment, near misses, modules) are "
        "WITHHELD: naming the declaration that already proves a blind "
        "proposition is itself the leak.",
        "   This is not a tool limitation to work around. If the family's blind "
        "value is genuinely already spent, record an ADR-0542 amendment in "
        "artifacts/autogenesis/mathlib-nursery-split-policy-v1.json; the row is "
        "then no longer held-out and this tool reports on it normally.",
    ]


# Ledger bookkeeping that is not a mathematical topic. A fact id is
# `F:ml430-<slug>-<hash>`, so without this the topic list is dominated by the
# mirror prefix and the hash and the module section says nothing.
TOPIC_NOISE = {
    "ml430", "mathlib", "source", "proposition", "the", "and", "for", "with",
    "declared", "pinned", "iff", "eq", "not", "all", "any", "one", "two",
}


def topic_tokens(ident: str, statement: str, title: str = "") -> set[str]:
    """Candidate MODULE basenames for this target.

    Drawn from the fact id, the Mathlib declaration name in the title, and the
    statement's identifiers. Pure-digit and hex-looking components are dropped:
    a fact id ends in a content hash, and without this the topic list is that
    hash plus `ml430`.
    """
    tokens = set(re.split(r"[^a-z0-9]+", ident.lower()))
    for token in IDENT.findall(statement) + IDENT.findall(title):
        tokens.update(part.lower() for part in token.split("."))
    tokens.discard("")
    keep = set()
    for token in tokens:
        if len(token) < 3 or token in TOPIC_NOISE:
            continue
        if token.isdigit():
            continue
        if len(token) >= 6 and re.fullmatch(r"[0-9a-f]+", token) and any(
                char.isdigit() for char in token):
            continue  # a content hash, not a topic
        keep.add(token)
    return keep


# ---------------------------------------------------------------------------


def self_check(root: pathlib.Path) -> int:
    """The controls a caller can run without any target: probe + delegation."""
    snapshot, fresh = load_snapshot(root)
    print(f"self-check: cache={cache_dir()}")
    if snapshot is None:
        print("self-check: NO SNAPSHOT -- run --refresh --build first",
              file=sys.stderr)
        return 3
    print("\n".join(freshness_banner(fresh, snapshot)))
    ok, detail = control_probe(snapshot["declarations"])
    print(f"self-check: control probe {'OK' if ok else 'FAILED'} -- {detail}")
    frontier = load_frontier_module(root)
    print(f"self-check: dispatchable-frontier module "
          f"{'loaded' if frontier else 'NOT LOADED'}")
    modules = module_index(root)
    shared = {name: paths for name, paths in modules.items() if len(paths) > 1}
    print(f"self-check: {len(modules)} module basenames, {len(shared)} shared "
          f"across directories")
    return 0 if ok and frontier and modules else 3


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__.splitlines()[0],
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("targets", nargs="*",
                        help="fact ids (F:…), substrings of one, or "
                             "Mathlib declaration names")
    parser.add_argument("--mathlib", action="append", default=[],
                        help="a Mathlib declaration name to resolve to a mirror")
    parser.add_argument("--refresh", action="store_true",
                        help="rebuild the environment snapshot and exit")
    parser.add_argument("--build", action="store_true",
                        help="with --refresh, cargo-build the projection example first")
    parser.add_argument("--allow-stale-binary", action="store_true",
                        help="with --refresh, accept a projection binary older "
                             "than the kernel sources; the snapshot is then "
                             "stamped unmatchable and always reads STALE")
    parser.add_argument("--self-check", action="store_true",
                        help="run the controls with no target and exit")
    parser.add_argument("--limit", type=int, default=6,
                        help="candidates printed per target (default 6)")
    parser.add_argument("--threshold", type=float, default=0.75,
                        help="score at or above which a candidate reads as present")
    parser.add_argument("--no-shape-search", action="store_true",
                        help="print section 2's command instead of running it")
    parser.add_argument("--shape-timeout", type=int, default=90,
                        help="seconds before shape_search is reported as DID NOT RUN")
    parser.add_argument("--files", action="store_true", default=True,
                        help="report the source files naming each candidate")
    parser.add_argument("--no-files", dest="files", action="store_false")
    parser.add_argument("--allow-stale", action="store_true",
                        help="exit 0 rather than 4 when the snapshot is stale")
    args = parser.parse_args()

    root = ROOT
    if args.refresh:
        snapshot = build_snapshot(root, rebuild=args.build,
                                  allow_stale_binary=args.allow_stale_binary)
        cache_dir().mkdir(parents=True, exist_ok=True)
        path = snapshot_path(snapshot["kernel_tree"])
        path.write_text(json.dumps(snapshot))
        print(f"wrote {path} -- {snapshot['declaration_count']} declarations, "
              f"{snapshot['build_seconds']}s")
        return 0
    if args.self_check:
        return self_check(root)

    tokens = list(args.targets) + list(args.mathlib)
    if not tokens:
        parser.print_help()
        return 2

    snapshot, fresh = load_snapshot(root)
    if snapshot is None:
        print("ERROR: no snapshot for any kernel tree. Run:\n"
              "  python3 scripts/brief-step0.py --refresh --build",
              file=sys.stderr)
        return 3

    ok, detail = control_probe(snapshot["declarations"])
    print("\n".join(freshness_banner(fresh, snapshot)))
    print(f"CONTROL    {'OK' if ok else 'FAILED'} -- {detail}")
    if not ok:
        print("UNANSWERABLE: the control probe failed, so no ABSENT in this run "
              "would have meant anything. Refresh the snapshot.", file=sys.stderr)
        return 3

    facts = load_facts()
    modules = module_index(root)
    frontier = load_frontier_module(root)

    resolved: list[str] = []
    for token in tokens:
        hits = resolve(token, facts)
        if not hits:
            print(f"\nTARGET  {token}\n        UNRESOLVED -- no fact id contains "
                  f"that token (positive control: {len(facts)} facts loaded)")
            continue
        if len(hits) > 6:
            print(f"\nTARGET  {token}\n        AMBIGUOUS -- {len(hits)} fact ids "
                  f"contain that token; first few: {', '.join(hits[:6])}")
            continue
        resolved.extend(hits)

    if not resolved:
        print("\nnothing to report: no target resolved to a fact.", file=sys.stderr)
        return 1

    refused = 0
    for ident in resolved:
        if report_target(root, facts[ident], snapshot, fresh, modules,
                         frontier, args):
            refused += 1

    print("")
    print("=" * 78)
    # Refusal outranks staleness: a stale ABSENT is a caveat on a verdict that
    # was printed, and this is a verdict that deliberately was not.
    if refused:
        print(f"{refused} of {len(resolved)} target(s) REFUSED as held-out; "
              f"nothing was reported for them (exit 5).")
        return 5
    if fresh["state"] == "STALE" and not args.allow_stale:
        print("SNAPSHOT WAS STALE -- ABSENT verdicts above are PROVISIONAL "
              "(exit 4).")
        return 4
    return 0


if __name__ == "__main__":
    sys.exit(main())

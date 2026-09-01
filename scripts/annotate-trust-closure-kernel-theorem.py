#!/usr/bin/env python3
"""Fill `formal.kernel_theorem` for trust-closure `unresolved` facts whose
declaration is already spelled, unambiguously, in the fact's own evidence.

`scripts/check-trust-closure.py`'s `subject_of()` resolves a kernel-lean
fact's subject in order: (1) `formal.kernel_theorem` if the KEY is present
(including `null`, which means "not about exactly one kernel theorem" and is
deliberate); (2) an unambiguous `evidence[].kernel_declaration`; (3) a
dotted-name regex over the fact's own `checker_command`s. 90 facts fail all
three (measured 2026-08-31) and count toward `kernel_facts` without counting
as `subjects` -- the ratio `resolved/kernel_facts` sits at 0.9586 against a
floor of 0.9579, one bad landing from red.

Investigating those 90 (docs/plan/status/resolve-kernel-subjects.md) found
they are NOT one population. Three structurally different reasons a fact
lands here:

1. **Genuinely under-annotated** (the `formal.kernel_theorem` field was never
   set): the declaration is spelled either in the fact's own `title` -- the
   `ml430` mirror convention "Mathlib v4.30 source proposition <Name>" -- or
   as an evidence `id` beginning `kernel-<Name>`, AND that exact name is a
   `theorem`-kind declaration in the environment `kernel_declaration_projection`
   walks. This script fixes exactly this case.

2. **Checked through an EPHEMERAL, isolated kernel instance that is never
   merged into the persistent environment.** Most `ml430-*` facts whose
   evidence names a `checker_operation` driver such as
   `axeyum-lean-import/sealed-kernel-capsule-v1`,
   `axeyum-lean-import/modeq-family-*`,
   `axeyum-lean-import/imported-candidate-*`,
   `axeyum-lean-import/conclusion-directed-transport-v1`, or
   `axeyum-lean-import/bounded-induction-*` are proved and admitted through a
   FRESH `Kernel::add_declaration` created just for that one check ("a
   two-fresh-kernel proof"), then discarded. Their Mathlib-style dotted name
   (e.g. `Int.fib_add_two`, `Nat.gcd_greatest`, `Nat.ModEq.refl`) VERIFIABLY
   does not exist in `kernel_declaration_projection`'s output -- confirmed by
   direct lookup, not inferred. No annotation can fix this: there genuinely
   is no persistent declaration to point at. This script does not touch
   these; see the module's own report for the list.

3. **The fact is not about exactly one kernel theorem at all** -- a package
   bundling two or more (`F:excluded-middle-not-intuitionistic` names both
   `ipc_excluded_middle_not_provable` and `ipc_soundness`;
   `F:nra-refutations-reconstruct-over-constructed-reals` is explicitly "Two
   ... certificates"), a meta-fact about module size or interface structure
   rather than a theorem, or a per-query ad hoc Lean reconstruction with no
   stable declaration name (`F:schedule-critical-chain-infeasible`,
   `F:ordered-ring-farkas-refutation`, the `shipped-front-door-*` pair). These
   are the deliberate-null shape and belong in `formal.kernel_theorem: null`,
   not in this script's output -- but marking them is a judgement call this
   script does not make automatically, because a wrong `null` reason is worse
   than an honest "still unresolved".

Restricted to THEOREM-kind candidates on purpose: an earlier draft of this
scan also matched `Definition`s (e.g. `Nat.ascFactorial`, `Int.fib`) and
would have mis-annotated `F:ml430-nat-one-ascfactorial-8bacb017` (whose real
subject `Nat.one_ascFactorial` does not exist) with the wrong declaration
`Nat.ascFactorial` -- silently pointing the trust-closure guards at the
wrong term. `theorem_names` below excludes every other kind for exactly this
reason.

Usage:
    python3 scripts/annotate-trust-closure-kernel-theorem.py --check
        # report only; exit 1 if any unresolved fact has an unambiguous
        # theorem-kind candidate that has not yet been written -- this is
        # the ratchet: a new landing fact with this exact shape turns it red.
    python3 scripts/annotate-trust-closure-kernel-theorem.py --apply
        # write formal.kernel_theorem for every unambiguous candidate found.
    python3 scripts/annotate-trust-closure-kernel-theorem.py --apply --projection FILE
        # use a pre-captured `kernel_declaration_projection` TSV instead of
        # running the release example (matches check-trust-closure.py).

Exit status: 0 = nothing to do (check) or all writes applied cleanly
(apply); 1 = --check found unapplied candidates, or --apply hit a
verification failure after writing (should not happen; would mean this
script's own candidate was wrong).
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import pathlib
import re
import sys
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
FACTS = ROOT / "artifacts/facts"

TITLE_RE = re.compile(r"^Mathlib v4\.30 source proposition (\S+)$")
KERNEL_ID_RE = re.compile(r"kernel-([A-Za-z][A-Za-z0-9_'.]*)")
DECL_PREFIX_RE = re.compile(r"^(?:def|theorem)\s+\S+\s*:\s*(.*)$", re.DOTALL)


def _load_module(name: str, path: pathlib.Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def find_candidate(
    data: dict[str, Any],
    theorem_names: set[str],
    by_type: dict[str, list[str]] | None = None,
) -> str | None:
    """Priority: title (ml430 mirror) > unambiguous evidence-id prefix >
    exact canonical_type match (any declaration kind).

    Deliberately does NOT fall back to a full-text scan of the whole fact:
    measured, that scan matches unrelated dependency theorems mentioned in
    `supports`/`notes` prose (e.g. it would call `Nat.mul_comm` the subject of
    `F:ml430-nat-gcd-fib-add-self-5a92d5e3`, which is wrong) far too often to
    trust automatically.

    The type-match tier is the gold standard -- it is not a name heuristic,
    it compares the fact's own `formal.statement` (when `formal.language ==
    "lean4"`, i.e. already in kernel-rendered form) against every
    declaration's `Kernel::render_lean` type, stripping an optional leading
    `def <Name> : ` / `theorem <Name> : `. An exact string match cannot be a
    false positive the way a name-presence heuristic can (this is what
    caught `F:rat-normalize-reduces`, whose subject is the DEFINITION
    `Rat.normalize`, not a theorem -- theorem_names alone would have missed
    it, and a name-based scan risked the same wrong-kind trap that
    `Nat.ascFactorial` demonstrated).
    """
    title = data.get("title") or ""
    m = TITLE_RE.match(title)
    if m and m.group(1) in theorem_names:
        return m.group(1)

    id_cands = set()
    for e in data.get("evidence") or []:
        eid = e.get("id") or ""
        m2 = KERNEL_ID_RE.match(eid)
        if m2 and m2.group(1) in theorem_names:
            id_cands.add(m2.group(1))
    if len(id_cands) == 1:
        return next(iter(id_cands))

    if by_type is not None:
        formal = data.get("formal") or {}
        if formal.get("language") == "lean4":
            stmt = formal.get("statement") or ""
            texts = {stmt}
            m3 = DECL_PREFIX_RE.match(stmt)
            if m3:
                texts.add(m3.group(1))
            matched: set[str] = set()
            for t in texts:
                if t in by_type:
                    matched.update(by_type[t])
            if len(matched) == 1:
                return next(iter(matched))

    return None


def _patch_kernel_theorem(text: str, name: str) -> str:
    """Insert `"kernel_theorem": "<name>"` as the first key of the `formal`
    object, matching the shape ADR-1005-era facts already use. Fails loudly
    (raises) rather than guessing at a shape it does not recognise, per the
    standing rule that a checker (and a fixer) must fail on the unexpected
    rather than silently doing nothing.
    """
    pattern = re.compile(r'("formal"\s*:\s*\{)')
    matches = list(pattern.finditer(text))
    if len(matches) != 1:
        raise RuntimeError(f"expected exactly one 'formal': {{ in file, found {len(matches)}")
    insert_at = matches[0].end()
    insertion = f'\n    "kernel_theorem": {json.dumps(name)},'
    return text[:insert_at] + insertion + text[insert_at:]


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--apply", action="store_true")
    parser.add_argument("--projection", type=pathlib.Path, default=None)
    parser.add_argument("--facts", type=pathlib.Path, default=FACTS)
    args = parser.parse_args(argv)

    if not args.check and not args.apply:
        args.check = True  # default to the safe, read-only mode

    tc = _load_module("_trust_closure", ROOT / "scripts/check-trust-closure.py")

    proj_text = tc.projection_rows(args.projection)
    decls = tc.parse_projection(proj_text)
    theorem_names = {n for n, d in decls.items() if d.kind == "theorem"}
    by_type: dict[str, list[str]] = {}
    for name, d in decls.items():
        by_type.setdefault(d.canonical_type, []).append(name)

    facts = tc.load_facts(args.facts)
    dd = _load_module("_depends_derived", ROOT / "scripts/check-fact-depends-derived.py")
    subjects = tc.collect_subjects(facts, decls, dd)

    to_apply: list[tuple[str, str]] = []
    for ident in sorted(subjects.unresolved):
        data = facts[ident]
        formal = data.get("formal") or {}
        if "kernel_theorem" in formal:
            continue  # already deliberately marked (null or otherwise)
        cand = find_candidate(data, theorem_names, by_type)
        if cand is not None:
            to_apply.append((ident, cand))

    print(f"trust-closure unresolved: {len(subjects.unresolved)}")
    print(f"unambiguous, unapplied theorem-kind candidates: {len(to_apply)}")
    for ident, cand in to_apply:
        print(f"  {ident} -> {cand}")

    if args.check:
        return 1 if to_apply else 0

    # --apply
    written = []
    for ident, cand in to_apply:
        path = args.facts / (ident.replace("F:", "F-") + ".json")
        text = path.read_text(encoding="utf-8")
        data_before = json.loads(text)
        assert "kernel_theorem" not in (data_before.get("formal") or {})
        new_text = _patch_kernel_theorem(text, cand)
        parsed = json.loads(new_text)  # must still be valid JSON
        if parsed.get("formal", {}).get("kernel_theorem") != cand:
            print(f"VERIFY-FAILED: {ident} did not round-trip after patch", file=sys.stderr)
            return 1
        path.write_text(new_text, encoding="utf-8")
        written.append(ident)

    print(f"\nwrote formal.kernel_theorem for {len(written)} facts")

    # Re-derive subjects from the now-mutated fact set on disk and confirm
    # the count actually moved by exactly len(written).
    facts_after = tc.load_facts(args.facts)
    subjects_after = tc.collect_subjects(facts_after, decls, dd)
    delta = len(subjects.unresolved) - len(subjects_after.unresolved)
    print(
        f"unresolved before={len(subjects.unresolved)} "
        f"after={len(subjects_after.unresolved)} delta={delta}"
    )
    if delta != len(written):
        print(
            f"VERIFY-FAILED: expected unresolved to drop by {len(written)}, "
            f"dropped by {delta}",
            file=sys.stderr,
        )
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))

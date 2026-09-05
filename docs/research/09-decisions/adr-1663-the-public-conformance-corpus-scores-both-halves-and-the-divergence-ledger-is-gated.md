# ADR-1663: The public conformance corpus scores both halves, and the divergence ledger is gated

Status: accepted
Date: 2026-09-05
Index-summary: The public corpus is `leanprover/lean-kernel-arena` (204 tests; 118 accept / 73 reject / 13 either), not the 189/121/62/6 the requirements doc cites; on its 186-case published tarball this kernel scores **108/113 accepts and 70/73 rejects** (69/73 on the run that found the defect below), against the in-tree `parse-only` control's **110/113 and 21/73** — so 21 of the reject half is earned by the reader and **49 by the trusted gate**. Eight divergences are published in a gated `docs/plan/lean-divergences.md` in lean4lean's shape; one (duplicate universe binders) was closed in the kernel; the `imax` over-completeness and the `max-to-imax` mutant are recorded as a **sanctioned** divergence on upstream's own `outcome: either` classification, closing the question ADR-1600 §4 left open.

## Context

Item 7 of the Next Ten in [`docs/math-department/14-lean-lang.md`](../../math-department/14-lean-lang.md)
is reviewer 10's: *"the kernel **is** the paper; the paper needs the public
conformance corpus, both halves"*, against *"32 hand-authored differential
cases against a corpus of 189 (121 accept / 62 reject / 6 either) nobody has
run; no divergence ledger."*

Two things had to be settled before any of that could be measured.

**Which corpus.** [`docs/plan/lean-kernel-requirements-2026-08-13.md`](../../plan/lean-kernel-requirements-2026-08-13.md)
§4.4 and R8.5 cite *"189 tests, 121 accept / 62 reject / 6 either"* and a
`parse-only` control scoring *"121/121 on accepts and 6/62 on rejects"* — with
no citation. Nothing in the tree names the corpus, and those numbers have been
copied into `14-lean-lang.md` and into briefs as if they were current.

**Why the reject half is the only half worth quoting.** The requirements doc
already states the reason and it is worth restating, because it is the entire
design of this gate: a checker that accepts everything it can parse scores
perfectly on the accept half. That is not a hypothetical — the corpus ships
such a checker as a control precisely so that no positive-only score can be
mistaken for a result.

## Decision

**The corpus is `leanprover/lean-kernel-arena`** (<https://arena.lean-lang.org>),
pinned at `abc55357aee17c59dfdbf39c8a2e19739e23dd10` plus its published test
tarball pinned by SHA-256, both in `scripts/fetch-references.sh`. **Every score
is reported as two numbers, never one, and always beside the `parse-only`
control's.** **Every divergence is published in
[`docs/plan/lean-divergences.md`](../../plan/lean-divergences.md)** in
lean4lean's shape, carrying the standing rule that an unlisted divergence is a
bug, **gated by a checker that derives the divergence set from the authorities
and never from a list of its own.**

**The `189 / 121 / 62 / 6` figures are stale and are not to be repeated.**
Measured from the corpus's own machine-readable `results.json` at
`abc55357`, 2026-09-02: **204 tests, 118 accept / 73 reject / 13 either.**
The control's shape survives the correction exactly — `parse-only` scores
**118/118 on accepts and 6/73 on rejects** upstream — which is why the doc's
argument was right even though its arithmetic was old.

**The `imax` over-completeness is a sanctioned divergence, not a defect to
close.** [ADR-1600](adr-1600-the-kernels-metatheoretic-status-what-is-trusted-and-what-is-not.md)
§4 left open whether to record a controlled exemption for
`level.max-kind:1322:max-to-imax` or to make this kernel's level check as
incomplete as Lean's. This ADR records the exemption, on evidence from the
reference corpus rather than on our own preference; see *Evidence*.

## Evidence

### The corpus, and what is runnable

The arena defines each case in YAML and builds it into `lean4export` NDJSON —
format **3.1.0**, exactly what `axeyum-lean-import` pins. Twelve cases are
committed as static NDJSON; the rest need a Lean 4.29.1 toolchain, `lake`, and
network access to fetch `lean4export`. The published tarball
(`lean-arena-tests.tar.gz`, sha256 `7e396d5d…`) contains every case under
10 MB, already exported, as `good/` and `bad/`: **113 accept, 73 reject, 186
total**. That is what makes the corpus runnable here without a Lean toolchain,
and it is what was scored.

Not scored, and said rather than smoothed over: the 13 `either` corner cases
are not in the tarball, and upstream excludes the five cases over 10 MB
(`mathlib`, `std`, `cslib`, `cedar`, `init`) — which are the largest accepts.
So the accept half measured here is 113 of the corpus's 118.

### Both halves, and the control

`crates/axeyum-lean-import/examples/kernel_conformance_check.rs` runs one case
per process under the arena's own external-checker contract (0 accept, 1
reject, 2 declined, 3 checker error). One case per process is not fussiness:
the corpus's performance cases are built to make a checker diverge, and the
first in-process sweep wedged with no way to say which case had taken it.

Measured 2026-09-05 at corpus digest `85fcd016…`
(`python3 scripts/check-kernel-conformance.py`):

| mode | half | total | correct | wrong | declined | no verdict |
|---|---|---:|---:|---:|---:|---:|
| full | accept | 113 | **108** | 4 | 0 | 1 |
| full | reject | 73 | **70** | 1 | 2 | 0 |
| parse-only (control) | accept | 113 | 110 | 2 | 0 | 1 |
| parse-only (control) | reject | 73 | **21** | 50 | 2 | 0 |

The reject half read **69 / 2 wrong** on the first run; one of those two is the
defect closed below, and the numbers here are the run after the fix. Both are
given because the first is what found it.

The control is the same reader with the trusted gate's verdict discarded
(`census_ndjson`, which records kernel declines instead of failing on them),
so the difference between the two rows is attributable and not rhetorical:

> **21 of the reject half is earned by the reader and recursor regeneration;
> the remaining 49 by the trusted gate.** A reject-half score quoted without
> that split does not say which layer earned it.

This matters concretely. `rec-k-lie`, `nat-rec-k-lie`, `large-elim-param`,
`large-elim-prop-bool` and `level-imax-leq` are all rejected — correctly — but
all five are in the 21, i.e. rejected by the recursor-regeneration comparison
(*"exported recursor K-like flag differs from the kernel-derived one"*, *"…
universe-parameter arity differs"*) rather than by the property each case was
built to probe. `level-imax-leq` is the sharpest instance: it is the
`nanoda_lib` `imax`-leq soundness bug that §4.5 of the requirements doc records
as **UNKNOWN** for this kernel, and we reject the stream at line 69 on an
unrelated K-flag mismatch, so **this run does not close that UNKNOWN**. The
level check itself is measured separately (below) and answers correctly on the
same shape.

Two §4.6 "known gaps" are settled by the run. *"No K-like reduction"* is
**closed**: `k_like_reduction` exists in `tc.rs` and the `rec-k-lie` /
`nat-rec-k-lie` soundness cases are rejected. *"No unit-like defeq"*, which
§4.6 predicted would block *"a block of conformance tests"*, blocks exactly
**two** (`107_unitEta1`, `108_unitEta2`) — and they are the only two accept-half
cases this kernel rejects from inside the trusted gate.

### The level shapes, re-measured rather than inherited

`cargo run --release -p axeyum-lean-kernel --example level_conformance_probe`,
2026-09-05:

```
LEVEL-PROBE name=probe5-imax-assoc  lhs=imax(u,imax(v,w)) rhs=imax(max(u,v),w) axeyum=true  lean=false verdict=more-complete-than-lean
LEVEL-PROBE name=max-to-imax        lhs=max(u,1)          rhs=imax(u,1)        axeyum=true  lean=false verdict=more-complete-than-lean
LEVEL-PROBE name=negative-control   lhs=imax(0,v)         rhs=succ(imax(0,v))  axeyum=false lean=false verdict=agree
LEVEL-PROBE name=positive-control   lhs=max(u,v)          rhs=max(v,u)         axeyum=true  lean=true  verdict=agree
```

Probe 5 of the requirements doc still diverges and so does the `max-to-imax`
shape. Both report `true`, which a degenerate `|_, _| true` would also print,
so the probe carries both controls; the negative one is the very shape the
arena's `level-imax-normalization` case exploits to derive `False`, and it
answers `false`.

**The decision to sanction rather than close rests on upstream's own
classification.** `tests/corner-cases/imax-right-successor.yaml` in the arena
is exactly this shape and carries `outcome: **either**`, with the note that a
checker *"may reject these hand-crafted exports using a more conservative
normalization, or accept them by recognizing that the right operand is
nonzero."* An `either` outcome is the reference corpus stating that checkers
may legitimately differ here. Deliberately making a correct decision procedure
incomplete, inside the soundness-critical core, to imitate a difference the
reference corpus does not consider a defect, is the wrong trade.

What follows and must be said wherever completeness is claimed: **this kernel
accepting a term does not imply Lean's kernel accepts it.** The implication
holds in the other direction on everything measured so far
(`stricter_than_lean=0` across 291 mutants, ADR-1600 §4).

### What was closed

`bad/tutorial/019_tut06_bad01` declares a `def` with `levelParams := [u, u]`.
Lean refuses it; this kernel admitted it. It was one of exactly two reject-half
cases accepted here, and the only one that is a defect rather than a deliberate
design difference (the other is D1, `Type`-valued theorems, which ADR-0760
already grades).

`Kernel::check_declaration` gained step (1a): the binding list may not repeat a
name, returning `KernelError::DuplicateUniverseParam`. Both existing checks are
*relative* — inference and def-eq treat `[u, u]` exactly as `[u]`, since each
occurrence of `u` in the term is the same `Param` node either way — so a
repeated binder was invisible to everything the kernel ran, the same mechanism
that left the binding list decorative before
`declaration_universe_params_must_be_bound.rs`. It matters because `Const(c, us)`
substitutes **positionally**: `@c.{a, b}` against `[u, u]` has two candidate
substitutions for one name and the declaration does not denote one thing.

`crates/axeyum-lean-kernel/tests/declaration_universe_params_must_be_distinct.rs`
tests both directions: the duplicate is refused with the variant that names the
repeated parameter, **and** one binder, two distinct binders, and no binders are
all still admitted — without that control the guard is satisfied by a kernel
that refuses every polymorphic declaration. `cargo test -p axeyum-lean-kernel
--lib` was then re-run whole (2,284 passed, 0 failed, 1 ignored, 3,067 s),
because a wrong version of this check would refuse a declaration every prelude
in the tree relies on and the targeted test could not see that.

**Scope, stated rather than implied.** `check_declaration` gates
`Axiom`/`Definition`/`Theorem`/`Opaque`; the inductive gate does its own
checking and does not route through it, so an inductive family's binding list
is **not** covered. The arena's case is a `def`, so the corpus does not
currently distinguish the two, and the ledger's D2 says so.

### The gates

`scripts/check-kernel-conformance.py` has nine guards and a `--self-test` that
fires each one on the fixture that names it. G6 is the one that makes the rest
mean anything: it **requires** the control to score at least 40 fewer on the
reject half, so a harness that quietly stopped exercising the kernel fails
instead of reporting a perfect score. Floors pin both halves (108 accepts, 70 rejects); ceilings pin the
known divergences, so a *new* one fails rather than being absorbed -- the
"we accept what Lean rejects" ceiling is **1** after the closure below, so a
second such case fails the gate. G9 re-runs
the divergent cases plus a fixed sample live and requires them to reproduce the
committed rows; mutating one committed `class` field with the verdict unchanged
fires G9 alone, verified.

`scripts/check-lean-divergences.py` enforces the ledger in the direction that
matters: it reads three authorities — the conformance summary's mismatches, the
differential's `EXPLAINED_INCOMPLETENESS`, and the replay census's
`Representability::reason` classes — and fails if the ledger does not name what
they report. L5 exists because the obvious failure mode is vacuity: an
authority that returns zero keys would make L2 pass silently, so a zero count
is itself a failure.

## Alternatives

**Build the corpus from source instead of using the published tarball.** It
would add the 13 `either` cases and the five large accepts, and it needs elan,
Lean 4.29.1, `lake` and network access to fetch `lean4export` — none of which
is present on most fleet hosts, and `command -v lean` is empty even on the one
that has it. Rejected for now; the tarball is pinned by SHA-256 so the scored
bytes are identified, and the exclusions are stated rather than hidden.

**Score one number.** Rejected on the corpus's own evidence: `parse-only`
scores 118/118 upstream and 110/113 here.

**Make the level check as incomplete as Lean's.** Rejected; see *Evidence*.

**Reject `unsafe`/`partial` declarations instead of declining them** (D4).
Rejected: declining is the fail-closed answer and a decline is not a reject.
Both are scored in their own columns and the two cases are never counted as
correct.

**Let the ledger's checker hold the list of divergences.** Rejected outright —
that is the checker-that-measures-the-maintainer's-memory pattern this
repository has already shipped once.

## Consequences

**Easier.** Reviewer 10's question is answerable with a command instead of an
adjective, and the answer names both halves and the control. A new divergence
in any of the three authorities now fails a gate until it is written down, so
the ledger cannot silently fall behind the tree.

**Harder.** Two floors and four ceilings now have to move deliberately. A
change that improves the reject half without the control moving fails G6, which
is intended: it means the improvement was in the reader, not the kernel.

**Revisited.** D2 is closed here, and the reject floor moved 69 -> 70 with the
soundness-divergence ceiling 2 -> 1 in the same change. D5 (unit-like defeq), D6 (dense
internalization indices) and D8 (`perf/app-lam`, no verdict in 600 s at 3.0 GB
RSS) are each bounded and named with their obstruction. D3 is settled as
sanctioned unless upstream reclassifies `imax-right-successor` away from
`either`, which is the trigger to reopen it. When a Lean 4.29.1 toolchain
exists on a fleet host, building the corpus from source adds the `either` cases
and the five large accepts, and the floors should be re-derived from that run
rather than adjusted.

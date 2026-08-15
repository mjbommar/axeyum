# 01 — Collect

> **Rewritten 2026-08-15 by lane `formalized-collect`, against measurements
> rather than the first draft's assumptions.** Every number below either carries
> a source and a date, or says it is unverified. The first draft's figures were
> taken from a survey and are corrected in place; the section
> [What the first draft got wrong](#what-the-first-draft-got-wrong) lists the
> corrections rather than hiding them.

**The question.** What do we hold locally, in what format, under what licence,
and at what cost?

## What we hold today, measured

```
references/                 lean4 (shallow clone); NO mathlib clone
artifacts/lean-imports/     5 pinned lean4export NDJSON 3.1.0 streams,
                            4,919 records, 263 KB, Lean 4.30.0, sha256-pinned
docs/plan/fixtures/         17 hand-picked v4.30 export fixtures
Lean toolchain              4.30.0 installed under ~/.elan (NOT on PATH)
lean4export binary          built at commit a3e35a58, toolchain v4.30.0
```

The five streams in `artifacts/lean-imports/` are the first corpus artifacts
this strand has produced, and each is cited by a fact in `artifacts/facts/` on
the `imported-kernel-lean` route (ADR-0454). They are *dependency-closed slices*:
`lake env lean4export Init -- <Declaration>` emits the requested constant plus
its transitive closure, so each file is self-contained.

## The measurement that should drive this phase

**Do not plan around how much we can download. Plan around how much the importer
accepts.** Measured 2026-08-15, by exporting 40 well-known `Init`/`Std`
declarations one at a time and running
`cargo run -p axeyum-lean-import --example lean4export_import`:

| outcome | count |
|---|---|
| imported, whole closure admitted | **13 / 40** |
| rejected by our kernel | 27 / 40 |

Nothing was rejected by the *reader*: the wire format, the record set, the name
and level tables and the inductive/quotient packaging all worked on real Lean
output at every size tried. **Every failure was our kernel declining a
declaration on definitional equality**, in four clusters:

| blocker | first-failing declaration(s) | count |
|---|---|---|
| structural-recursion unfolding (`brecOn` / `below` / `match_n` / `._f`) | `Nat.zero_add._f`, `Nat.succ_add._f`, `Nat.add_assoc._f` | 8 |
| `rfl`-proved equations of a `brecOn`-compiled function | `Nat.add_succ`, `Nat.mul_succ`, `Nat.pow_succ` | 7 |
| `HEq` elimination | `eq_of_heq` | 5 |
| `noConfusion` auxiliaries | `_private.Init.Prelude.0.noConfusion_of_Nat.aux._f` | 5 |
| other type mismatches | `List.append_nil`, `Nat.succ_sub_succ_eq_sub` | 2 |

Reproduce with (from a built `lean4export` checkout at the pinned commit):

```sh
lake env ./.lake/build/bin/lean4export Init -- Nat.add_comm > /tmp/x.ndjson
cargo run -q -p axeyum-lean-import --example lean4export_import -- /tmp/x.ndjson
# Error: Kernel { line: 866, declaration: "Nat.zero_add._f",
#         source: TypeMismatch { expected: ExprId(2952), got: ExprId(3059) } }
```

Three consequences for collection, and they invert the first draft's plan:

1. **Corpus size is not the binding constraint. `Nat.add` is.** `Nat.add` is
   compiled through `Nat.brecOn` / `Nat.below` / `Nat.add.match_1`, and
   `Nat.add_succ` is proved by `rfl`, so admitting it requires reducing through
   that encoding. Until that works, a larger corpus buys nothing: **the most
   cited theorem in our own fact ledger, `Nat.add_comm`, cannot be imported.**
2. **A megabyte-scale download is premature.** Five 6–150 KB streams already
   expose the whole blocker census. Cloning Mathlib before the census is closed
   would be collecting to look busy.
3. **The right next collection artifact is a decline census, not a corpus.**
   Export a few hundred `Init` declarations, import each, and count blockers by
   cluster. That is a coverage number the kernel lane can work against, and it
   costs minutes.

## The corpora, ranked by what they are worth to us

### Tier 1 — Lean 4 / Mathlib. Start here, and for now finish here.

**Why first:** it is the only corpus we can already read, and the reader works.

- Mathlib size, `leanprover-community.github.io/mathlib_stats.html`, fetched
  2026-08-15: **135,592 definitions, 284,457 theorems, 772 contributors**.
- Dependency graph, [arXiv:2604.24797](https://arxiv.org/abs/2604.24797) ("The
  Network Structure of Mathlib", Li–Peng–Severini–Shafto, April 2026), pinned to
  Mathlib commit `534cf0b` of 2026-02-02: **308,129 declarations, 8,436,366
  edges, 7,563 modules**. Verified against the abstract.
  **These two figures do not reconcile** — different snapshot dates and a
  different definition of "declaration". Cite one with its source and date; do
  not average them or treat either as canonical.
- Apache-2.0, so redistribution and derived artifacts are unproblematic.
- **There is no published bulk `lean4export` dump of Mathlib.** Searched
  2026-08-15: no size figure, no HuggingFace/Zenodo artifact, nothing in the
  Mathlib docs pipeline. LeanDojo Benchmark 4 (~122,517 theorems, 259,580
  tactics, 167,779 premises) is *proof-state and tactic training data*, not a
  kernel-level export, and is not a substitute. So the export must be produced,
  and its size is unknown until we produce it.

**`lean4export` is alive and moving faster than our pin.** Verified via the
GitHub API 2026-08-15: `leanprover/lean4export`, Apache-2.0, pushed 2026-08-11,
83 of the last ~105 commits dated in 2026, HEAD `lean-toolchain` at
`leanprover/lean4:v4.34.0-rc1` (bumped 2026-08-10). NDJSON is now its **only**
output format and `format_ndjson.md` still declares version **3.1.0**, so our
reader's format profile is current even though our toolchain pin (4.30.0) is
four releases behind. Related tooling, same check:

| tool | state |
|---|---|
| `leanprover/lean4checker` | **archived**, last pushed 2026-03-25 |
| `digama0/lean4lean` | active (2026-08-14); a Lean-in-Lean checker, does not consume NDJSON |
| `ammkrn/nanoda_lib` | active (2026-08-12); a Rust checker that *does* consume lean4export output — the closest thing to a peer for `axeyum-lean-import` |
| `gebner/trepplein`, `trepplein4` | stale, no 2026 activity |

**Collect:** a pinned Mathlib revision, its `lean4export` NDJSON, and the
toolchain manifest that produced it — together, hashed. `artifacts/lean-imports/MANIFEST.json`
is the shape: exporter commit, Lean version, Lean githash, format version,
per-stream SHA-256, the exact reproduction command, and a recorded determinism
check. An export without its producing revision is unreproducible.

### Tier 2 — the HOL family, via OpenTheory. Verify it still works before planning on it.

**Isabelle's Archive of Formal Proofs**, fetched from `isa-afp.org` 2026-08-15:
**1,017 entries, 604 authors, ~324,200 lemmas, ~5,360,300 lines**, newest entry
2026-08-05 — actively maintained. Licence is **per entry**: each is BSD-style or
GNU LGPL, at the author's choice, with authors retaining copyright. There is no
single AFP licence, so a derived artifact inherits per-entry terms.
No current machine-readable bulk export was found (no live `isabelle dump` /
PIDE-XML corpus, and the Isabelle-MMT work traces to arXiv:1905.07244, 2019).

**OpenTheory is the interchange format for the HOL family, and it looks
dormant.** `opentheory.gilith.com` is live and reports 54 theory packages, but
the newest packages shown date to about 2020, and the `gilith/hol-light`
OpenTheory-export fork was last pushed **2020-02-12** while mainline
`jrh13/hol-light` was pushed 2026-08-10. The first draft said "there is a path,
and it is not ours to build." The honest version: **there was a path, and
whether it still runs against 2026 HOL Light is untested.** Test it before
planning a phase on it — the test is cheap and the answer changes the tier.

### Tier 3 — Mizar and Rocq, for reference not ingestion

- **Mizar Mathematical Library.** Licence, verified 2026-08-15 via
  `JUrban/MMLLicense` and arXiv:1107.3212: **dual GNU GPL v3-or-later and
  CC BY-SA v3-or-later**, copyright with the Association of Mizar Users,
  contributors signing a Fiduciary License Agreement. So it is copyleft and
  share-alike, **not** un-redistributable — the first draft's "more restrictive"
  was vague in a way that would have misled a licence review. Size figures
  (~1,400 articles, >13,000 definitions, >65,000 theorems; MML 5.94.1493 of
  2025-05-30) come from search snippets only: `mizar.org` and
  `mizar.uwb.edu.pl` refused connections on 2026-08-15. **Treat the size as
  unverified.** Its Tarski–Grothendieck foundation is far from our kernel; it is
  a coverage map, not an import target. MPTP shows no maintenance since ~2013.
- **Rocq/Coq Mathematical Components.** Current LOC and theorem counts could not
  be verified (the metrics live at `math-comp.github.io/htmldoc/libgraph.html`,
  not fetched). Export tooling has *regressed*: `coq-serapi` is
  maintenance-only and has moved to `rocq-archive/`, with the project pointing
  users at `coq-lsp` instead; CoqInE (Coq→Dedukti) is alive but explicitly
  work-in-progress on universe polymorphism. Do not plan a phase around either.

### Tier 4 — not libraries, but corpora we should hold anyway

- **TPTP** — current release **v9.3.0, 2026-06-20** (fetched from tptp.org).
  Problem counts found in search results (22K–25K) are inconsistent and likely
  stale; confirm against the v9.3.0 release notes before quoting one. Licence
  terms not re-confirmed this round.
- **SMT-LIB** benchmarks — already partially held under `corpus/`.
- **OEIS** — **398,315 sequences** as of 2026-08-14. **Licence is unresolved**:
  sources disagree between CC BY-NC 3.0 and CC BY-SA 4.0 plus an end-user
  agreement. NC versus SA is a materially different obligation; resolve it at
  `oeis.org/wiki` before deriving anything from it.

## What collection actually costs

1. **Building to export.** Mathlib's NDJSON does not exist until Mathlib is
   built. Neither the build wall-clock nor the `lake exe cache get` download size
   is published; both must be measured. Budget a Lean toolchain and tens of GB.
   *A Lean 4.30.0 toolchain and a built `lean4export` already exist on this box*
   — the expensive part is Mathlib itself, not the exporter.
2. **Storage and the checkout.** `references/` is gitignored and repopulated by
   `scripts/fetch-references.sh`; anything corpus-sized should follow that
   pattern and live on `/nas3/data/axeyum/` rather than in git. The five streams
   here total 263 KB and are committed deliberately, because a fact that cites
   bytes must be able to re-read them.
3. **Memory.** Every large artifact this project has handled has hit a
   materialisation limit. The independently relevant number is now published:
   [arXiv:2607.00815](https://arxiv.org/abs/2607.00815) ("LRAT-Catcher",
   Szeider, 2026-07-01) measures Mathlib's `lrat_proof` peaking at **96.6 GB on
   a 628 MB certificate** where native reflection uses **8.9 GB** — and the blowup
   is strongly non-linear (a 6.5 MB pigeonhole certificate already costs 36.6 GB).
   Verified against the paper. Ask what the *streaming* story is, not what the
   peak is.
4. **Licence hygiene.** Apache-2.0 (Lean/Mathlib) is clean. AFP is per-entry.
   Mizar is copyleft/share-alike. OEIS is unresolved. Record the licence *with*
   the pin, because a derived artifact in our ledger inherits it.

## What to do first

Reordered, because the census changed the priorities.

1. **Run the decline census.** Export a few hundred `Init` declarations
   individually, import each, and report admitted/declined with the blocker
   cluster for each decline. Cheap, and it is the number the kernel lane needs.
   This is `03`'s S2 ("make declines first-class") pulled ahead of S1, because
   at a 13/40 admission rate a hard-failing importer measures only the first
   blocker in a stream.
2. **Then add Mathlib to `scripts/fetch-references.sh`** at a pinned revision —
   still cheap and reversible, but no longer the first move, since we cannot yet
   read what we would download.
3. **Pin revision + toolchain + export together, hashed.** Already done for the
   five streams; `artifacts/lean-imports/MANIFEST.json` is the template.
   **Check overlap with our own preludes before landing an imported fact.** The
   sixth candidate here, `Nat.not_succ_le_zero`, turned out to be proved already
   in our Nat prelude, axiom-free — and the two are the same proposition under
   two different formal statements (ours over the kernel's `Nat.le`, Lean's
   through the `LE` class). That is `02-synthesize.md`'s alignment problem
   arriving on the first five imports, and it costs one command
   (`nat_theorem_inventory`) to detect.
4. **Re-pin the toolchain deliberately.** We are on Lean 4.30.0 against an
   exporter that tracks 4.34.0-rc1. Moving is a decision with a cost (every
   committed stream re-exports and every pinned SHA-256 changes), so make it
   once, on purpose, and not as a side effect of something else.

## What the first draft got wrong

| claim | correction |
|---|---|
| "115,000+ definitions, 232,000 theorems" | 135,592 / 284,457 (mathlib_stats, 2026-08-15). The old figures were roughly a year stale. |
| AFP "4.8 MLOC" | ~5,360,300 lines, 1,017 entries, ~324,200 lemmas (isa-afp.org, 2026-08-15). |
| AFP "BSD-style terms" | Per-entry BSD **or** LGPL, author's choice. There is no single AFP licence. |
| Mizar "more restrictive" | Dual GPL-3.0-or-later and CC BY-SA 3.0 — copyleft, and redistributable under those terms. Its 3.7 MLOC figure is unverified; primary sites were unreachable. |
| OpenTheory: "there is a path, and it is not ours to build" | The path's HOL Light side has not been touched since 2020 while HOL Light ships weekly. Untested against 2026 HOL Light. |
| OEIS "380,000+ integer sequences" | 398,315 (2026-08-14) — and the licence is contested (NC vs SA), which the draft did not mention. |
| Rocq: "a plausible third target" | Weaker than that now: `coq-serapi` is archived/maintenance-only and CoqInE is explicitly WIP. |
| "Produce one `lean4export` NDJSON of a dependency-closed slice" as step 2 | Done, five times, in under an hour — the step was much cheaper than the draft assumed, and it revealed that the binding constraint is the kernel, not collection. |
| Implicit assumption that the importer's limit is scale | The importer's limit is **definitional equality on `Nat.add`**. 13 of 40 real `Init` theorems import; the reader itself declined nothing. |

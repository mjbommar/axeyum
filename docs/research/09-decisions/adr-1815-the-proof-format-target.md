# ADR-1815: Alethe stays the only emitted proof format; no Ethos/Eunoia route, because it would have zero consumers while our existing one is not running

Status: accepted
Index-summary: Stay Alethe-only — an Ethos/Eunoia emitter would have zero consumers (no in-tree code, `references/ethos` absent), while Alethe already has an in-tree checker that runs (`check_alethe`, `alethe.rs:938`) and an external one that does not (both Carcara gates skip green). Measured first-hand on cvc5 1.3.4: its default `(get-proof)` is CPC, and its Alethe printer holes 9 of 35 steps on a two-line QF_LIA refutation and 2 of 12 on a two-line QF_S one — so cvc5 interop argues for neither format. Names the consumer that would reopen this.
Date: 2026-09-09

## Context

We emit Alethe from a substantial surface and pin a list of the rules an
external checker accepts. Roadmap item 4.3 of
[`docs/solver-comparison-2026-09/11-roadmap-and-plan.md`](../../solver-comparison-2026-09/11-roadmap-and-plan.md)
asks whether to stay Alethe-only or add an Ethos/Eunoia route, on the grounds
that cvc5's *default* format is CPC/Eunoia rather than Alethe, that cvc5's
Alethe printer holes most of its rules including the whole strings family, and
that there is a rule-naming break between what cvc5 emits and what Carcara
checks. It adds a constraint: **do not do both without a consumer.**

That constraint decides the question, but not for the reason the roadmap
expected.

### What we actually emit, and who checks it

Fifteen `*alethe*.rs` files, 17,574 lines. The roadmap's "twelve" is correct for
the literal `*_alethe*.rs` glob (eleven library modules plus
`crates/axeyum-solver/tests/word_alethe.rs`, which is a test) but undercounts:
it misses `crates/axeyum-cnf/src/alethe.rs` (5,153 lines),
`crates/axeyum-solver/src/alethe_lra.rs` (1,446), and
`crates/axeyum-bench/examples/alethe_portability_probe.rs` (375). Say "twelve
`*_alethe*.rs` modules" or the sentence reads as false.

`CARCARA_CHECKED_RULES` is at `crates/axeyum-cnf/src/alethe.rs:696`, body
`:697-876`, and has **exactly 180 entries**, one per line. Roadmap item 0.1 is
**DONE**: `"minus_simplify"` is present at `:802` (and `"unary_minus_simplify"`
at `:869`). Several docs still say 179 and describe 0.1 as outstanding —
`docs/solver-comparison-2026-09/03-cvc5.md:929`,
`08-proof-checking-ecosystem.md:33`,
`docs/solver-inventory-2026-09/08-models-proofs-and-evidence.md:59` and `:286`,
the gap analysis at `10-gap-analysis.md:33`, and the roadmap row itself at
`11-roadmap-and-plan.md:36`. All stale.

Alethe has **two** consumers here, and they are in very different states.

1. **An in-tree checker that runs.** `check_alethe`
   (`crates/axeyum-cnf/src/alethe.rs:938`, and `check_alethe_with` at `:957`)
   dispatches per rule — e.g. `"bitblast_add" => check_bitblast_add(lhs, rhs)`
   at `:2084`. Pure Rust, no external binary, no skip path.
2. **An external checker that does not.** Both Carcara gates skip green.
   `crates/axeyum-cnf/tests/carcara_checked_rules_parity.rs:119-128` prints
   `[skip] references/carcara not present …` and returns; the derivation it
   would perform (parse `get_rule`'s match arms out of the clone, subtract
   `DELIBERATELY_EXCLUDED = ["hole", "lia_generic", "rare_rewrite"]` at `:39`,
   assert set equality) is real code that has never run in this tree.
   `crates/axeyum-solver/tests/carcara_crosscheck.rs:175` skips with
   `AXEYUM-CARCARA-SKIPPED no carcara binary`. `references/` here contains one
   file, `README.md`.

So the pinned 180-name list is, **as executed evidence, a hand-written
literal**. The claim "derived from the clone" is true of the source and false of
every run. That is exactly the shape CLAUDE.md warns about — a test named
"matches the authority" that measures the maintainer's memory whenever the
authority is absent — and it is the single most important fact bearing on this
decision.

### We are a producer, not a consumer

`parse_alethe` exists (`crates/axeyum-cnf/src/alethe.rs:299`, re-exported at
`lib.rs:85`), but every call site is a round-trip test of our own writer. No CLI
flag ingests a proof; the same is true of `parse_drat`/`parse_lrat`. The only
external-checker traffic is outbound.

This matters because the roadmap's naming-break argument is about the *inbound*
direction. cvc5 emits `bv_bitblast_step_bvadd`; the string
`bv_bitblast_step` appears **zero times** anywhere in `crates/`. We emit
`bitblast_add` (`crates/axeyum-solver/src/bitblast_alethe.rs:466`), which is
pinned at `alethe.rs:711` and checked in-tree at `:2084`. **The naming break
costs us nothing, because we never read a cvc5 proof.** It would only matter if
we became a consumer, and nothing in the roadmap proposes that.

### cvc5's proof formats, measured first-hand rather than cited

`references/cvc5` is ABSENT, so the roadmap's "97 of 172 rules translated" could
not be re-derived. But cvc5 1.3.4 is on this host
(`/nas3/data/axeyum/harness/bin/cvc5`), so the two claims that matter were
measured directly, 2026-09-09.

**Default format is CPC, not Alethe — confirmed.** `(get-proof)` with no flag on
`(> x 3) ∧ (< x 2)` returns `define` / `assume` / `step … :args` with rules
`evaluate`, `refl`, `nary_cong`, `trans`, `arith_poly_norm` — CPC shape, no `cl`
clause syntax anywhere.

**cvc5's Alethe output is not Carcara-checkable even on trivial refutations.**
Re-running the same two queries under `--proof-format-mode=alethe`:

| Query | `:rule` steps | `:rule hole` steps |
|---|---|---|
| `QF_LIA`: `(> x 3) ∧ (< x 2)` | 35 | **9** |
| `QF_S`: `s = "ab" ∧ (str.len s) = 3` | 12 | **2** |

Every hole carries `:args ("untranslated rewrite")`. In the string case one of
the two holes is `(step t4 (cl (= (str.len "ab") 2)) :rule hole …)` — the only
step that does any string reasoning at all. And `hole` is precisely what our own
parity test lists as `DELIBERATELY_EXCLUDED`, i.e. deliberately not in
`CARCARA_CHECKED_RULES`.

This is stronger than the doc's 97-of-172 count and points the same way: **there
is no cvc5 interop to be had in Alethe, and cvc5's preference for CPC is not an
argument that CPC would serve us better.** It is an argument that cvc5's Alethe
support is a secondary path in cvc5, which is a fact about cvc5.

### What an Ethos route would have on the other side

Nothing. `references/ethos/` is ABSENT (it is a listed clone target —
`references/README.md`, `scripts/fetch-references.sh:26`). Grepping `crates/`
for `ethos|Ethos|eunoia|Eunoia|CPC` returns one hit, and it is `gethostname`.
There is no in-tree Ethos/Eunoia/CPC code of any kind.

## Decision

**Stay Alethe-only. Do not add an Ethos/Eunoia emission route, because it would
have zero consumers, while the format we already emit has an in-tree consumer
that runs and an external consumer that is not running — and the effort a second
format would take is exactly the effort that would make the first one's external
check able to fail.**

Four commitments:

1. **One emitted proof format: Alethe.** No second emitter is added.
2. **The naming break is closed as a non-issue for us**, and is not to be
   carried forward as a gap. It is inbound-only; we are outbound-only. If it is
   quoted again it must be quoted with that caveat, and the "30 cvc5-emitted
   names with no Carcara checker" figure must be re-derived first — it was
   computed against a 179-entry list and the list is now 180.
3. **The Carcara gate is a prerequisite, not a parallel track.** Roadmap item
   0.2 is what turns "we emit a checkable proof" from a claim into an
   observation. Until `AXEYUM_REQUIRE_CARCARA=1` makes an absent binary a
   failure and a renamed rule fail the gate, no proof-format comparison we make
   is testable, and adding a second format multiplies an unverified surface
   rather than an verified one.
4. **The door is left open with a named condition.** An Ethos/Eunoia route
   becomes worth building when **a consumer exists that we would actually run**.
   Concretely, any one of: (a) `references/ethos` is fetched and the Ethos
   checker is wired as a second, independent external check on the same
   refutations Carcara sees — the same additive-second-checker logic ADR-1813
   applies to oracles; (b) a downstream user of ours asks for CPC because their
   toolchain consumes it; (c) we decide to become a proof *consumer*, at which
   point the format question is about what cvc5 emits well, and the measurement
   above says that is CPC, not Alethe. Absent one of those, this ADR holds.

## Evidence

- `crates/axeyum-cnf/src/alethe.rs:696` (definition), body `:697-876`, **180**
  entries counted programmatically (`awk` over the body, lines matching `^\s*"`).
- `crates/axeyum-cnf/src/alethe.rs:802` — `"minus_simplify"` present; item 0.1
  is done.
- `crates/axeyum-cnf/tests/carcara_checked_rules_parity.rs:119-128` — the skip
  that returns green; `:39` — `DELIBERATELY_EXCLUDED`.
- `crates/axeyum-solver/tests/carcara_crosscheck.rs:175` — the second skip.
- `crates/axeyum-cnf/src/alethe.rs:938`, `:957`, `:2084` — the in-tree checker
  that does run.
- `crates/axeyum-solver/src/bitblast_alethe.rs:466` and `alethe.rs:711` — we
  emit and pin `bitblast_add`; `grep -rn bv_bitblast_step crates/ --include=*.rs`
  → 0.
- The two cvc5 1.3.4 runs above, default and `--proof-format-mode=alethe`, with
  the hole counts.
- `references/` contains one file; `references/ethos`, `references/carcara`,
  `references/cvc5` and `references/stp` are all absent.

## Alternatives

- **Add an Ethos/Eunoia emitter alongside Alethe.** Rejected on the roadmap's
  own constraint: no consumer. It would also violate the discipline this
  repository keeps learning — a producer whose output nothing checks cannot
  fail, and shipping a second such producer while the first one's external check
  skips green is manufacturing unfalsifiable surface at double the rate.
- **Switch from Alethe to CPC on the grounds that cvc5 defaults to it.**
  Rejected. cvc5's default tells us what cvc5's own toolchain checks, not what
  ours does. Switching would discard 17,574 lines of emitter plus a working
  in-tree checker in exchange for a format with no checker on our side at all.
- **Drop Alethe emission entirely and rely on the Lean kernel route.**
  Rejected, and the reason is a sharp edge worth recording:
  `prove_unsat_to_lean_module` (`crates/axeyum-solver/src/reconstruct.rs:2375`)
  takes `(arena, assertions)` — the **original** assertions — not
  `Vec<AletheCommand>`. Lean and Alethe are therefore two independent
  re-derivations of one verdict, not two checkers of one artifact, so Lean is
  not a substitute consumer for the Alethe artifact. And it is not uniformly
  stronger: `reconstruct.rs:2360-2368` records that for roughly 29 fragments the
  returned module is a 21-line `StructuralAttestation` shim — `axiom P`,
  `axiom Not P`, `theorem _ : False` — that kernel-checks, is `sorry`-free, and
  contains **none** of the reasoning.
- **Decide nothing until `references/` is populated.** Rejected. The decision
  does not depend on the absent clones: it depends on whether an Ethos consumer
  exists here, and it does not. Populating `references/` changes commitment 3's
  urgency, not commitment 1.

## Consequences

**What this buys.** One format, one emitter surface, and a clear statement that
the next unit of proof-format work is item 0.2 rather than a new backend. The
inbound/outbound distinction is written down, so the cvc5 naming break stops
being cited as our problem.

**What is LOST by deciding this way.**

- **We give up interoperability with cvc5's checked ecosystem.** Ethos checks
  cvc5's CPC against 51 signature files; that is a mature, actively-developed
  checking path and we will not be on it. If Alethe's ecosystem stalls — Carcara
  is one research group's tool — we are on the losing format and will have to
  pay this migration later, with more emitter code than we have today.
- **We keep a single external checker, and it is currently not running.**
  ADR-1813 argues against single-oracle blindness for verdicts; the same
  argument applies to proofs, and this ADR consciously declines to fix it now.
  The in-tree `check_alethe` is a genuine consumer but it is *ours* — it shares
  our understanding of the rules, so it cannot catch a systematic
  misunderstanding of Alethe semantics. Only an external checker can, and we
  have none running.
- **We accept that "every unsat carries a machine-checkable proof" remains
  partly aspirational.** `Evidence` has 64 variants; **3** carry Alethe
  (`UnsatAletheProof` at `evidence.rs:387`, `UnsatArithAletheProof` at `:398`,
  `UnsatGuardedQuantAletheProof` at `:414`), 8 carry an
  `Option<String> lean_module`, and the remaining ~50 are bespoke structured
  certificates or `Evidence::Unsat(None)` (8 construction sites, all in
  `evidence.rs`: `:2162`, `:2282`, `:2348`, `:2406`, `:2643`, `:3144`, `:3814`,
  `:4119`). The trust ledger (`crates/axeyum-solver/src/trust.rs`) carries 22
  `EvidenceRoute` entries, 12 `certifies: true` and 10 `certifies: false`, of
  which 4 name `NO_CHECKER` (`:307`, `:318`, `:371`, `:406`). Alethe is one
  evidence family among many, not the trunk — a second *format* would not change
  that ratio, which is another reason it is the wrong next move.

## What would falsify this decision

1. **Carcara stops being maintained, or diverges from the Alethe our emitters
   target**, such that the 180-name list cannot be kept current against a live
   clone. Alethe would then have no viable external checker and the format
   choice reopens immediately.
2. **The Carcara gate lands (item 0.2) and fails broadly on proofs our in-tree
   `check_alethe` accepts.** That would mean our two consumers disagree about
   Alethe, our emitters encode our own reading of the format, and a second,
   independently-specified format (CPC has an executable signature language,
   which Alethe does not) becomes an argument about correctness rather than
   interoperability.
3. **A real consumer appears for CPC** — condition 4(b) above. One named,
   external user is enough; a hypothetical is not.
4. **We become a proof consumer.** The moment we want to *read* a cvc5 proof,
   the measurement above inverts the decision: cvc5's CPC is complete where its
   Alethe holes, and the naming break stops being a non-issue.
5. **The hole rate measured here turns out to be an artifact of cvc5 1.3.4 or of
   these two tiny queries.** Nine holes in 35 steps on a two-line QF_LIA
   refutation is a strong signal, but it is two data points on one version. A
   sweep showing cvc5's Alethe printer is near-complete on realistic inputs
   would weaken the "no interop to be had" half of the argument — though not the
   "no consumer" half, which is what the decision actually rests on.

# Retrieval audit for 2026-09-01

Lane `retrieval-audit-0901`, run 2026-09-02. The first of the daily audits
[ADR-0608](../09-decisions/adr-0608-retrieval-is-by-shape-and-absence-is-distinct-from-unanswerable.md)'s
structural remedy calls for: one lane per day reads the previous day's commits
for rederived lemmas and dedupes them, so a duplicate costs hours rather than
weeks. Method is the appendix of
[2026-08-27-retrieval-is-the-bottleneck.md](2026-08-27-retrieval-is-the-bottleneck.md)
repeated, not a new one. The running ledger lives at the foot of that file.

**Headline: one literal duplicate, landed 16 h 29 min after the declaration it
duplicates, deduped here (`b4fb008d8`). Three further rederivations that are
not literal duplicates, all in the hiding place no gate can reach. And the L0
duplicate gate had been RED on `main` for about 25 hours with nobody running
it.**

## 0. Correction to the brief's window

The brief sized 2026-09-01 at "~465 commits". Measured on this worktree
(branched from `origin/main` at `5c8eaf7b8`, then merged local `main` at
`524df45e2` so the audit sees the whole day):

| | count |
|---|---|
| commits with a 2026-09-01 committer date, reachable from `main` | **240** |
| of those, touching `crates/axeyum-lean-kernel` | **69** |
| commits with a 2026-09-01 committer date across **all** refs | 243 |

So ~240, not ~465. The 465 is not reproducible from any ref in this
repository; whoever quotes it next should re-derive it. Nothing in the audit
depends on which number is right — the candidate set comes from the commits
themselves — but the day's throughput claims do.

The window runs `2026-09-01T00:00-04:00` to `2026-09-01T20:42-04:00` (the last
commit on local `main`). There are no 2026-09-02 commits on any ref to audit;
the lane's branch point is 15:18 on 2026-09-01.

## 1. Candidates (17)

The classifier's only job is to produce the candidate set; a crude classifier
that flags a whole shape is not a measurement. Phrase family = the appendix's
(`already exist`, `already prov`, `already had`, `already covers`, `not new`,
`instead of re-deriv`, `duplicate`) plus the brief's (`turns out`, `rederiv`,
`re-deriv`, `found .* existing`, `promote`, `hoist`, `unexpose`) plus
`was already` / `is already` / `were already`, `redundan`, `dedup`,
`no need to`, `did not need`, `unnecessary`, `verbatim`, `same proposition`,
`two proofs`, `second proof` and `existing (lemma|declaration|theorem|helper)`
— matched over subject **and** body, case-insensitive.

Over the 69 kernel-path commits: **17 candidates**. (Over all 240 commits: 63
candidates, dominated by `re-derive` used in the CAS-certificate sense, an
unrelated subject; the kernel-path set is the one judged here.)

| # | commit | subject | matched | verdict |
|---|---|---|---|---|
| 1 | `461a58573` | move 13 self-contained modules into per-module registries | `promote` | **no** — promoting a throwaway *script*, not a lemma |
| 2 | `b3b449dfc` | compute the build order instead of validating a hand-written one | `duplicate` | **no** — a duplicate *provider* in a build-order table |
| 3 | `b339a4191` | hoist the recursor-uparams helper above the statements | `hoist` | **no** — code motion inside one file for `items_after_statements` |
| 4 | `ce3a4cbac` | 5 more of the held-out family | `turns out` | **no** — and a *positive*: see §3 |
| 5 | `088e698aa` | close `F:ml430-nat-log-eq-one-iff` | `did not need` | **no** — quoting the module doc's own prior wording |
| 6 | `ac1d00fd7` | six log/clog `ml430` mirrors | `existing … boundary theorem` | **no** — "composing exclusively out of existing machinery", correct reuse |
| 7 | `cfb7014dc` | `Rat.det_row_selection_of_duplicate` | `duplicate`, `reuse` | **no** as a rederivation — a *near-miss avoided*, see §3 |
| 8 | `774a1f741` | route notes for the determinant selection lemma | `duplicate`, `reuse` | **YES** — §2.2 |
| 9 | `6a59f015b` | register coverage inventory + drop redundant `Shape` match | `redundan` | **no** — clippy `match_same_arms` |
| 10 | `36f85826f` | declare `Nat.factorizationLCMLeft/Right` | `re-deriv` | **no** — deliberately re-deriving a *window measurement*, and correct to |
| 11 | `8f4ecba76` | row multilinearity for `Rat.det` | `is already` | **no** as a rederivation — found `row_add_split`, see §3 |
| 12 | `0d955c59a` | the draw is authorable | `re-deriv` | **no** — re-deriving `select()`'s entries |
| 13 | `3e1641f24` | `succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul` | `existing nat theorem` | **YES** — §2.3 |
| 14 | `2f4e70d6b` | `Int.gcd_ne_one_iff_gcd_mul_right_ne_one` | `duplicate` | **YES** — §2.4 |
| 15 | `3c4241b0d` | register `prime_dvd_mul'` / … | `existing nat lemma` | **no** — correct reuse of `Int.euclid_lemma` |
| 16 | `d5ae2082a` | `prime_dvd_mul'` / … untested | `existing Int.euclid_lemma` | **no** — same, the wip half |
| 17 | `907002cfc` | five `ml430` prime/factorial/lcm mirrors, axiom-free | `verbatim` | **YES**, though not through this phrase — §2.1 |

Note what the phrase family did **not** catch. The literal duplicate (§2.1) was
found by `shape_search --duplicates`, not by any commit message. Its own lane's
message says the rendered types "match each fact's `formal.statement`
verbatim" — the lane checked its declaration against the *fact* and never
against the *environment*, which is exactly the gap the shape index closes.
**Commit-message archaeology is a lower bound and the tool is not; run both.**

## 2. Confirmed (4)

### 2.1 LITERAL DUPLICATE — `Nat.prime_coprime_factorial_of_lt` (deduped, `b4fb008d8`)

`shape_search --include-constructed --duplicates` reported **16** groups
against a **15**-entry allowlist. The one unadjudicated group:

    DUPLICATE  Nat -> Nat -> And -> Nat.lt -> Eq
      Nat.coprime_factorial_of_lt_prime  Nat.prime_coprime_factorial_of_lt

Same shape is not the finding; same *proposition* is.
`kernel_declaration_projection` renders both, in all eight prelude groups that
carry them, as

    ((x0 : AxNat) -> ((x1 : AxNat) -> ((x2 : And (AxNat.le (AxNat.succ
    (AxNat.succ AxNat.zero)) x0) (((x2 : AxNat) -> ((x3 : AxNat.dvd x2 x0) ->
    Or (Eq.{1} AxNat x2 (AxNat.succ AxNat.zero)) (Eq.{1} AxNat x2 x0))))) ->
    ((x3 : AxNat.lt x1 x0) -> Eq.{1} AxNat (AxNat.gcd x0
    (AxNat.factorial x1)) (AxNat.succ AxNat.zero)))))

character for character. The proofs are the same induction on `n` with `p` and
the primality hypothesis held outside it, the same `gcd_dvd_right` +
`eq_one_of_dvd_one` base, the same `le_succ`/`le_trans` weakening of the IH;
they differ only in whether `coprime_of_lt_prime` is flipped through `gcd_comm`
or `coprime_symmetric`, and in whether `factorial_succ` is applied explicitly
or left to defeq.

**The two landed 16 hours 29 minutes apart.**

| | landed | file | consumers |
|---|---|---|---|
| `Nat.coprime_factorial_of_lt_prime` | `82637fefb` 2026-08-31T11:56:34-04:00 | `nat_prelude/gauss_lemma.rs` (ADR-1070) | mirrored at `Int` by `int_prelude/gauss_factorial_coprime.rs` |
| `Nat.prime_coprime_factorial_of_lt` | `351bb27b5` 2026-09-01T04:25:22-04:00 | `nat_prelude/prime_dvd_factorial_lcm.rs` | one, in its own file |

Survivor by ADR-0608's rule (earliest landed, most consumers): the
`gauss_lemma` one. Build order cooperates — `declare_gauss_lemma_all` runs at
`nat_prelude.rs:7527`, 101 steps before `declare_prime_dvd_factorial_lcm_all`
at 7628 — so the surviving name is already admitted where the repointed
consumer needs it.

**Hiding places, both of them:**

* **(1) general infrastructure filed under its first consumer.** A
  prime/factorial coprimality lemma belongs, by any reasonable guess, in
  `primes.rs` or a factorial module. It is in `gauss_lemma.rs` because Gauss's
  lemma's connecting theorem needed it first — the exact shape of
  `CReal.congrOfUniformlyContinuous`.
* **(4) there is no single spelling.** `coprime_factorial_of_lt_prime` and
  `prime_coprime_factorial_of_lt` are the *same five words in a different
  order*: the survivor follows this repository's `X_of_Y` convention, the
  duplicate follows Mathlib's `Nat.Prime.coprime_factorial_of_lt` namespace
  order. `--name-like` normalises case, `_` and `.`; it does **not** normalise
  word order, and no name-based tool can. Only the shape index reached this.

Projection invariant, measured before and after in this worktree:

| | |
|---|---|
| rows | 14,673 → 14,665 |
| removed | **8** — `Nat.prime_coprime_factorial_of_lt`, one per prelude group (nat, integer, characterization, rat, creal, complex, cpoint, ipc) |
| added | 0 |
| changed | **8** — `Nat.prime_dvd_factorial_iff_le`, **columns 5 and 6 only** (value constants and direct dependencies, which now name the survivor). Rendered type unchanged on all 8; axiom footprint unchanged (0) on all 8. |

The 8 changed rows are the repoint the dedupe is made of, not drift: the
"differs only by the deleted rows" invariant holds on the type and footprint
columns, and the dependency column has to move when a consumer is repointed.
Nothing else in the projection moved.

The ledger row was repointed, never deleted.
`F:ml430-nat-prime-coprime-factorial-of-lt-2dbea201` is `train` partition — not
held-out, checked in `artifacts/autogenesis/nursery-v2-extension.json` before
anything was touched — and its `formal.statement`, its reader-facing
`statement` and therefore both pinned digests are **byte-identical** across the
change. Only `formal.kernel_theorem` moved, under an amendment in
`settled-fact-statement-pins.json` recording
`from_kernel_theorem`/`to_kernel_theorem` with `from_sha256 == to_sha256`.

**Corroboration that arrived by itself.**
`check-fact-depends-derived.py` then failed with an edge nobody had to be told
about: `F:int-coprimefactorialofltprime`'s proof term *directly uses*
`Nat.coprime_factorial_of_lt_prime`. The Int mirror had been consuming the
survivor all along while the ledger recorded the duplicate — independent
evidence, read out of the proof terms rather than out of the source, that the
survivor is the one with consumers.

**And the gate was red.** `check-shape-duplicates.py` is an L0 gate
(`check.sh`, `local-ci.sh`, `ci.yml`, held there by
`check-l0-gate-enforcement.py`). It exited 1 on this tree, and the duplicate
landed at 04:25 on 2026-09-01 — about **25 hours** red before this lane ran it.
That is the gate working; what did not work is that no lane in the window ran
it, and it is the argument for a daily audit rather than a gate alone.

### 2.2 The 2-point swap function, third construction — `774a1f741` / `5e6f1fae7`

The determinant selection lemma's injective case needs "swap two indices". The
lane found **two** existing constructions and could reuse neither:

* `nat_prelude/transposition.rs`'s pointwise lemmas — `pub(crate)` but tied to
  `&mut NatDev<'_>`, not generic over `NatOps`, so uncallable from `IntDev`.
* `int_prelude/prod.rs`'s `point_swap` family — `pub(super)`, invisible outside
  `int_prelude`.

and designed a third ("a fresh, simpler 2-level `Nat.beq`-based `swap_fn`").
**Not landed** — the lane shipped only the free half
(`Rat.det_row_selection_of_duplicate`) — so this is a re-derivation designed
and costed, not one on disk. Recorded; nothing deleted.

Hiding place: **(2), by way of visibility.** Both prior constructions exist and
are named; neither is reachable. A carrier-typed or `pub(super)` helper is, to
every other module, indistinguishable from an absent one, and no index over
`kernel.environment()` sees it because it declares nothing.

### 2.3 Five `Nat` helpers re-derived in the Int prelude — `3e1641f24`

The commit says so itself: `dvd_elim_nat`, `dvd_intro_nat`, `mul_left_comm_nat`,
`mul_mul_mul_comm_nat` and `dvd_cancel_left_of_pos_nat` are "private local
copies of constructions this repository already keeps per-file
(`nat_prelude/dvd_mul_split.rs`, `lcm_gcd_lemmas.rs`)".

**It is not five copies, it is a convention.** Counted across
`crates/axeyum-lean-kernel/src`:

| private helper | file-local copies |
|---|---|
| `dvd_elim` | **13** |
| `absurd` | **12** |
| `dvd_intro` | **10** |
| `or_cases` | **6** |
| `dvd_cancel_left_of_pos` | 3 |
| `mul_mul_mul_comm` | 3 |

`dvd_elim` alone lives in `coprime_lemmas.rs`, `divisibility.rs`,
`divisor_sum_scale.rs`, `div_mod_lemmas.rs`, `dvd_mul_split.rs`,
`irrational.rs`, `lcm_gcd_lemmas.rs`, `lcm.rs`, `perfect.rs`, `prime_char.rs`,
`primes.rs` and `totient_gcd_mul.rs` — twelve files, plus the Int copy.

Hiding place: **(2), inline and unnamed.** None of these declares anything, so
none has a type, so `shape_search --duplicates` is structurally blind to every
one of them — the blind spot ADR-0608 states rather than implies. Nothing is
deleted here: each is a few lines, and unifying them is a real refactor with a
`NatOps`-genericity question inside it. That is a task, not an audit finding.

### 2.4 `Int.eq_em`'s decidability construction, duplicated — `2f4e70d6b`

Also self-reported: deciding `Eq Nat (gcd x m) one` through `Nat.beq`'s
soundness and completeness is "the same construction `int_prelude::decide`
builds privately for `Int.eq_em`, duplicated locally per this file's own
convention". Same hiding place, same reason, same non-action.

## 3. Near-misses and adjacent findings (not counted)

These are the day's *good* retrieval outcomes and the defect class the appendix
reports separately. They belong in the record so tomorrow's audit does not
re-flag them.

* **`ce3a4cbac` did the search correctly and said so.** Before naming
  `Nat.mul_self_le_mul_self_iff` and its two siblings: "Checked absent from the
  whole constructed inventory before naming, with a positive control in the
  same command (`Nat.mul_le_mul_left`, 8 rows) — an empty grep alone would have
  proved nothing." That is the discipline, executed. It also found that
  `every_int_declaration_is_checked_and_axiom_free`'s `starts_with("Int.")`
  scope left **13** `Nat.`-named declarations made *from the Int prelude* with
  no axiom-freedom check anywhere, and closed it with an environment-derived
  assertion.
* **`cfb7014dc` bumped nine `matrix_det.rs` helpers `fn` → `pub(super)` "so the
  new sibling module can reuse them instead of duplicating".** The §2.3
  convention, declined once, deliberately. This is the cheap fix for hiding
  place 2 and it is available far more often than it is taken.
* **`8f4ecba76` found `row_add_split`** — "a private two-term additivity
  phrased in the private `rset_row` builders, whose only consumer was
  `det_row_swap`" — and superseded rather than re-derived it. Hiding place 1,
  caught by reading.
* **`3284c490a` corrected a stale ABSENT in a curriculum doc**:
  `graded-statement-families.md` said LA-3 had "no rank function at all
  (ABSENT)" while `Rat::matrix_rank` exists (`axeyum-cas/src/lib.rs:6883`). A
  doc-level instance of the same defect, outside the kernel, and the reason the
  appendix counts curriculum rows as instances.
* **`cb42e82b8`: 26 of 27 declined facts are now `proved`**, closed by
  hand-authored declarations that never invoked a producer. This is the
  *ledger* not knowing rather than a *lane* not knowing — a different defect,
  reported separately here as the appendix reports its own two.

## 4. Per-hiding-place counts

Using the four hiding places from the design review and its appendix.

| hiding place | confirmed instances | of which literal duplicates |
|---|---|---|
| 1 — general infrastructure filed under its first consumer | 1 (§2.1, jointly) | 1 |
| 2 — a reusable step built inline, private, or not visible | 3 (§2.2, §2.3, §2.4) | 0 |
| 3 — a stated hypothesis weaker than everyone assumes | 0 | 0 |
| 4 — there is no single spelling | 1 (§2.1, jointly) | 1 |
| **total (distinct instances)** | **4** | **1** |

§2.1 sits in hiding places 1 and 4 at once and is counted once in the total.

**Every one of the three non-literal instances is hiding place 2, and hiding
place 2 is the one no gate here can reach.** The gate found the only instance
it was capable of finding, and found it on the first run of the day. That is
the shape of the remaining problem, stated as a measurement rather than a
worry: shape-indexed retrieval has closed the *declared* half, and the
*undeclared* half — 13 copies of `dvd_elim`, 12 of `absurd` — is untouched by
any tool and is where three of four instances now live.

## 5. Was the tooling used?

| population | denominator | `shape_search` | `brief-step0` / `just brief` |
|---|---|---|---|
| commit messages, kernel-path, 2026-09-01 | 69 | **0** (0.0%) | 0 |
| commit messages, all paths, 2026-09-01 | 240 | 1 (0.4%) | 0 |
| lane status docs touched on 2026-09-01 | 27 | **2** (7.4%) | **0** |
| lane status docs, all time (reference) | 490 | 38 (7.8%) | 11 (2.2%) |

The one commit-message mention (`e7f172dd6`, ADR-1440) is a *design* use — the
selection lemma written as a shape — not a step-0 retrieval check.
`check-shape-duplicates.py` appears in **0** of 240 messages.

So the brief's "prose plus a tool used 4.8% of the time" holds at 7.4% on the
day's lanes, and `brief-step0` — the entry point that assembles the query for
you, and whose whole point is that it belongs to whoever *writes* the brief —
was used **zero** times. The 2026-09-01 rate is not distinguishable from the
all-time rate, which is the honest reading: nothing about that day moved it.

## 6. Baseline for tomorrow

* Duplicate groups: **15**, all allowlisted with a reason
  (`scripts/shape-duplicates-allowlist.json`, 15 entries; the doc that
  adjudicated the original ten is
  [2026-08-27-shape-search-duplicates-adjudicated.md](2026-08-27-shape-search-duplicates-adjudicated.md)).
  `check-shape-duplicates.py` exits 0 at `b4fb008d8`.
* `shape_search --include-constructed`: **2,875** declarations across
  `[logic, nat, axreal, integer, ipc, rat, characterization, string, creal,
  complex, cpoint]`, index build 36–42 s in `--release`.
* `kernel_declaration_projection`: **14,665** rows. The pre-dedupe tree was
  14,673 rows, SHA-256
  `576296bf531513e04749c77fb2162f374e3006cb837355ee0f06c7721ecd0c87` — the same
  digest `461a58573` and `b3b449dfc` both pinned, so those two refactors and
  this dedupe compose cleanly.
* Ledger: 2,343 settled facts pinned, 0 drifted, 87 amendments;
  `validate-facts.py` exit 0.

Three things to do differently, for whoever runs the 2026-09-02 audit:

1. **Run the tool first, read commit messages second.** The literal duplicate
   was invisible to every phrase in the family; the three the phrases did find
   were all self-reported and none was deletable. Commit archaeology finds
   hiding place 2 (which the tool cannot) and the tool finds literal duplicates
   (which archaeology cannot). They are complements, not a primary and a
   fallback.
2. **Check the L0 duplicate gate's own colour before anything else.** It was
   red for 25 hours here. A day where it is green is a day with no literal
   duplicate, and the audit reduces to §2's other three categories.
3. **Scope the phrase sweep to the kernel path.** Over all 240 commits the
   family gives 63 candidates against the kernel path's 17, and the extra
   46 are dominated by `re-derive` in the CAS-certificate sense — recomputing a
   certificate's distinction, an unrelated subject. Judging them cost more than
   the kernel-path set did and produced nothing.

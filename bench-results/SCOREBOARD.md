# Measured Scoreboard — axeyum vs Z3

> **Auto-generated. Do not edit by hand.** Regenerate with `python3 scripts/gen-scoreboard.py`.

A single-glance, honest view of where the pure-Rust axeyum solver stands against **z3 4.13.3** across every *measured* division. Every number here is read straight from a committed baseline JSON under `bench-results/baselines/` — nothing is hand-entered.

## How to read this

- **Decided** = `sat + unsat` — the instances axeyum *resolves*. Everything else is a **sound `unknown`** (we cannot decide it yet) or **unsupported** (the logic fragment is not wired); axeyum never guesses.
- **Decide%** = `Decided / Files`. This is the **capability frontier** — higher means axeyum decides more of the slice on its own.
- **DISAGREE** = wrong verdicts vs the ground truth (oracle disagreements + `:status` disagreements). **DISAGREE = 0 everywhere means zero wrong sat/unsat — soundness.** This is the line that must never move off zero.
- **Ground-truth** — how each division's verdict was checked: `z3-library` (the in-repo Z3 oracle), `z3-binary` (the external Z3 binary), `z3-library+binary` (a mix across the slice), or `:status` (the SMT-LIB `(set-info :status ...)` annotation, used when the Z3 oracle was vacuous/skipped for the whole slice — e.g. it rejected the logic's sort). An honest row reflects what was *actually* compared (see the **Cmp** column = instances the oracle compared).
- **PAR-2** = mean PAR-2 score in seconds (timeouts counted at 2×); lower is faster. `—` where not recorded.

## Headline

- **35 division baselines** measured vs z3 4.13.3, spanning **24 logic fragments** (BV, LIA, QF_ABV, QF_ALIA, QF_AUFBV, QF_AUFLIA, QF_AX, QF_BV, QF_BVFP, QF_DT, QF_FF, QF_FP, QF_LIA, QF_LRA, QF_NIA, QF_NRA, QF_S, QF_SEQ, QF_SLIA, QF_UF, QF_UFBV, QF_UFFF, QF_UFLIA, UF).
- **DISAGREE = 0 across all baselines** — zero wrong verdicts over 628 oracle-compared instances (992 files total, 751 decided).
- Decide-rate ranges **0%–100%** across divisions — that spread *is* the capability frontier; DISAGREE = 0 is the soundness floor that holds everywhere.

## Divisions vs Z3

Sorted by logic, then by descending decide-rate. Every committed `*solver-vs-z3*` baseline plus the synthetic graduated NRA/NIA baselines appears below.

| Division | Slice | Files | Decided | Decide% | Unknown | Unsup | Cmp | DISAGREE | Ground-truth | PAR-2 (s) |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- | ---: |
| BV | `bv-bitwuzla-regress-clean-quantified` | 5 | 5 | 100% | 0 | 0 | 0 | 0 | :status | 0.000 |
| BV | `bv-cvc5-regress-clean-quantified` | 54 | 52 | 96% | 0 | 2 | 0 | 0 | :status | 0.794 |
| LIA | `lia-cvc5-regress-clean-quantified` | 12 | 0 | 0% | 8 | 4 | 0 | 0 | :status | 30.000 |
| QF_ABV | `qf-abv-cvc5-bitwuzla-regress-clean` | 193 | 169 | 88% | 0 | 24 | 165 | 0 | z3-library+binary | 1.666 |
| QF_ALIA | `qf-alia-cvc5-regress-clean` | 6 | 6 | 100% | 0 | 0 | 5 | 0 | z3-binary | 0.000 |
| QF_AUFBV | `qf-aufbv-bitwuzla-regress-clean` | 44 | 41 | 93% | 0 | 3 | 41 | 0 | z3-library+binary | 1.979 |
| QF_AUFBV | `qf-aufbv-cvc5-regress-clean` | 9 | 5 | 56% | 1 | 3 | 4 | 0 | z3-binary | 3.334 |
| QF_AUFLIA | `qf-auflia-cvc5-regress-clean` | 7 | 5 | 71% | 2 | 0 | 4 | 0 | z3-binary | 5.715 |
| QF_AX | `qf-ax-cvc5-regress-clean` | 8 | 8 | 100% | 0 | 0 | 8 | 0 | z3-binary | 0.004 |
| QF_BV | `qf-bv-curated-bvred` | 6 | 6 | 100% | 0 | 0 | 6 | 0 | z3-library | 0.000 |
| QF_BVFP | `qf-bvfp-bitwuzla-regress-clean` | 8 | 7 | 88% | 0 | 1 | 6 | 0 | z3-library+binary | 0.005 |
| QF_DT | `qf-dt-cvc5-regress-clean` | 3 | 3 | 100% | 0 | 0 | 3 | 0 | z3-binary | 0.003 |
| QF_FF | `qf-ff-cvc5-regress-clean` | 30 | 24 | 80% | 0 | 6 | 24 | 0 | z3-library | 0.010 |
| QF_FP | `qf-fp-bitwuzla-regress-clean` | 16 | 16 | 100% | 0 | 0 | 16 | 0 | z3-library+binary | 0.010 |
| QF_LIA | `qf-lia-cvc5-regress-clean` | 11 | 10 | 91% | 1 | 0 | 9 | 0 | z3-binary | 1.819 |
| QF_LRA | `qf-lra-cvc5-regress-clean` | 11 | 9 | 82% | 2 | 0 | 5 | 0 | z3-binary | 3.637 |
| QF_NIA | `qf-nia-curated-iand` | 3 | 3 | 100% | 0 | 0 | 0 | 0 | :status | 0.003 |
| QF_NIA | `qf-nia-synthetic-graduated` | 32 | 32 | 100% | 0 | 0 | 32 | 0 | z3-binary | 6.772 |
| QF_NIA | `qf-nia-cvc5-regress-clean` | 39 | 33 | 85% | 5 | 1 | 23 | 0 | z3-binary | 2.730 |
| QF_NRA | `qf-nra-synthetic-graduated` | 33 | 30 | 91% | 3 | 0 | 30 | 0 | z3-binary | 5.455 |
| QF_NRA | `qf-nra-cvc5-regress-clean` | 38 | 32 | 84% | 6 | 0 | 32 | 0 | z3-binary | 3.169 |
| QF_S | `qf-s-cvc5-regress-clean` | 134 | 87 | 65% | 6 | 41 | 82 | 0 | z3-library+binary | 1.323 |
| QF_SEQ | `qf-seq-cvc5-regress-clean` | 33 | 26 | 79% | 6 | 1 | 15 | 0 | z3-library+binary | 3.752 |
| QF_SLIA | `qf-slia-cvc5-regress-clean` | 50 | 18 | 36% | 4 | 28 | 16 | 0 | z3-library+binary | 3.650 |
| QF_UF | `qf-uf-cvc5-regress-clean-overbound-uninterp-sorts` | 6 | 4 | 67% | 2 | 0 | 4 | 0 | z3-binary | 7.489 |
| QF_UF | `qf-uf-cvc5-regress-clean-bounded` | 82 | 44 | 54% | 13 | 24 | 37 | 0 | z3-library+binary | 4.845 |
| QF_UF | `qf-uf-cvc5-regress-clean-bounded-uninterp-sorts` | 82 | 44 | 54% | 13 | 24 | 37 | 0 | z3-library+binary | 4.845 |
| QF_UFBV | `qf-ufbv-bitwuzla-regress-clean` | 2 | 2 | 100% | 0 | 0 | 2 | 0 | z3-binary | 0.000 |
| QF_UFBV | `qf-ufbv-cvc5-regress-clean` | 4 | 4 | 100% | 0 | 0 | 4 | 0 | z3-binary | 0.001 |
| QF_UFFF | `qf-ufff-cvc5-regress-clean` | 8 | 8 | 100% | 0 | 0 | 0 | 0 | :status | 0.003 |
| QF_UFLIA | `qf-uflia-curated-named` | 2 | 2 | 100% | 0 | 0 | 2 | 0 | z3-binary | 0.001 |
| QF_UFLIA | `qf-uflia-cvc5-regress-clean` | 8 | 8 | 100% | 0 | 0 | 8 | 0 | z3-binary | 0.572 |
| QF_UFLIA | `qf-uflia-cvc5-regress-clean-bounded-uninterp-sorts` | 6 | 6 | 100% | 0 | 0 | 6 | 0 | z3-binary | 0.002 |
| QF_UFLIA | `qf-uflia-cvc5-regress-clean-overbound-uninterp-sorts` | 2 | 2 | 100% | 0 | 0 | 2 | 0 | z3-binary | 2.294 |
| UF | `uf-cvc5-regress-clean-quantified` | 5 | 0 | 0% | 0 | 5 | 0 | 0 | :status | 0.000 |

**Totals:** 992 files, 751 decided, 628 oracle-compared, **0 disagreements.**

<!-- NOTES:BEGIN (hand-written attribution notes — preserved by the generator) -->
### QF_S row re-measured 2026-07-07 (P2.7 task #49 — `str.in_re` over a symbolic `str.++`, and membership coupled with `str.++` word equations)

The membership fragment previously **declined** whenever a `str.in_re` subject was a
symbolic `str.++` (e.g. `(str.in_re (str.++ x "B" y) R)`), or when a membership atom
was coupled with `str.++` word equations. Two composition fixes land these rows:
**(1)** the parser rewrites `(str.in_re (str.++ p…) R)` into `w ∈ R ∧ w = p…` with a
fresh operand `w`, so a membership-over-concat reuses the single-variable membership
machinery inside the online CDCL(T) route; **(2)** on the sat branch the route now
witnesses each membership class, **pins** the witness as an extra word equation, and
re-solves the *augmented* word system (a concat operand's witness is searched over
`R ∩ shape`, `shape` built from the parts' own witnessed languages, so it decomposes
into the components) — the earlier design witnessed memberships independently of the
word part and desynced. `sat` stays gated **only** by the mandatory `Seq`-level model
replay against the skeleton (the concatenation *and* the membership both hold under
the model), so no wrong `sat` is possible even when the shape heuristic is imprecise;
an undecomposable shape stays first-class `unknown`. This is a **sat-side** slice —
certifying concat *emptiness* (`unsat`) is deferred, so unsat concat rows stay
`unknown`. Net (same-command HEAD re-run): **QF_S 78 → 82 decided (sat 51 → 55)** — the
five upgraded files `issue2060`, `issue5510`, `issue5520`, `issue7677-test-const-rv`,
`issue4608-re-derive` all move `unsupported → sat`, **each agreeing with the z3 binary
AND cvc5; DISAGREE=0, model-replay-failures=0** across the division. (The concurrent
`simple-nth-fail` `sat → unsupported` move is unrelated — the task #46 `str.from_code`
symbolic-argument decline.) Soundness backing: the online-membership differential fuzz
was extended to emit `str.in_re` over `str.++`-of-variables and re-run over 700
generated scripts vs **both** Z3 and cvc5 (DISAGREE=0, both verdict directions), plus a
new `qf_s_concat_membership` suite whose sat test re-checks the witnessed concatenation
is in the language through the independent reference matcher and whose negative tests
pin that an UNSAT / `re.none` membership-over-concat is never reported `sat`.

### QF_NIA cvc5 row CORRECTED DOWN 2026-07-07 (23→21) — a soundness fix, not a regression

The NIA div/mod slice (`a946f925`) committed this row at **23 decided**, but 2 of
those unsats (`div.01`, `minimal_unsat_core` — nested `div(div n n) n` chains) were
proved via an **unsound** step: `eliminate_int_divmod` folded `div`/`mod` by a
constant-zero divisor to a fixed convention value (`div a 0 = 0`), and the same
method wrong-refutes a genuinely-satisfiable underspecified formula
(`int_mod_by_zero_underspecification`, the P0 unit test). The fix (`52f3b1d1`)
makes div/mod-by-zero a fresh unconstrained variable (underspecified → free), so
those two rows — genuinely unsat under z3, but only provable here via the unsound
convention — correctly become **unknown**. The row is now **21 (sat 17, unsat 4),
DISAGREE=0**: `div.03` (integer sign lemma) + `mod.02` (self-division) are the two
soundly-decided unsats the slice actually added; the net vs the pre-slice 21 is a
sound swap. **Recovering `div.01`/`minimal_unsat_core` soundly needs congruent
uninterpreted div-0 reasoning** (same args → same free value, so a
value-independent structural contradiction still refutes) — a tracked follow-up.

### QF_NIA cvc5 row RECOVERED UP 2026-07-07 (21 → 25) — sound congruent div/mod-by-zero (P2.5 task #40)

The tracked follow-up landed. `div`/`mod`-by-zero is now treated as an
**underspecified total function**: the fresh `_/0` value stays free (so the P0
`775 < mod(0,0)` is still not refuted — a lone term has no congruence partner),
but eager **Ackermann congruence** across `_/0` groups (`a = c → v_a = v_c`, for
both the constant-divisor path in `eliminate_int_divmod` and the variable-divisor
path in `nia_linearize`) restores functional consistency. This is monotone-sound
(every congruence lemma is a valid consequence, so it can never turn a satisfiable
formula unsat), and it recovers the **value-independent structural contradictions**
the fresh-per-term relaxation lost: `div.01`, `minimal_unsat_core`, and `div.08`
(nested `div(div n n) n` chains where an asserted equality among nested quotients
propagates by congruence to contradict an asserted `distinct`, regardless of the
`_/0` value) all decide **unsat** again — matching z3. Row: **21 → 25 decided
(54% → 64%), unsat 4 → 8, DISAGREE = 0, model_replay_failures = 0, oracle
22/22 agree.** The same congruence closed a **pre-existing wrong-`sat`** in the
constant-`_/0` relaxation (`div (mod 2x 3) 0 ≠ div (mod (3−x) 3) 0`, unsat because
`2x ≡ 3−x (mod 3)`) that a fresh-per-term relaxation reported `sat` — surfaced by
the **new `qf_nia_divmod_const_differential_fuzz`** (the const-zero seed-class the
variable-divisor fuzz structurally could not generate; the P0's gate). Gated by
`nia`/`nra`/`qf_nia_divmod_var`/`qf_nia_divmod_const` differential fuzzes (all
DISAGREE = 0), `progress_frontier` (8/8), `corpus_regression`, `--workspace --lib`.

### QF_NIA cvc5 row RECOVERED UP 2026-07-07 (25 → 33) — `int.pow2` wiring + bounded value-table axioms (P2.5 task #41, slice 6)

`int.pow2` is now a first-class IR operator (`Op::IntPow2`) parsed from the cvc5
native surface `(int.pow2 x)`, evaluated by the ground evaluator with cvc5's
**total** semantics **verbatim** (authoritative source
`references/cvc5/src/theory/evaluator.cpp`): `pow2(x) = 2^x` for `x ≥ 0`, and the
**DEFINED** value `pow2(x) = 0` for `x < 0` — *not* underspecified (cvc5's
`ARITH_NL_POW2_NEG_REFINE` lemma `x < 0 ⇒ pow2(x) = 0` and its `pow2-native-0`
regression, which is *unsat* on `x < 0 ∧ pow2(x) ≠ 0`, both pin the negative case
to `0`). The NIA linearizer (`nia_linearize::abstract_pow2`, run **before**
div/mod elimination) abstracts each `pow2(x)` to a fresh integer with **six
theory-valid axiom families** (each a genuine theorem, so `unsat` transfers and a
`sat` is still replay-checked against the original `pow2` term): negative
(`x<0 ⇒ p=0`), positivity (`x≥0 ⇒ p≥1`), super-linear lower bound
(`x≥0 ⇒ p≥x+1`), evenness (`x≠0 ⇒ p=2q`), pairwise strict monotonicity
(`0≤xᵢ<xⱼ ⇒ pᵢ<pⱼ`), the exact `div`/`mod`-of-pow2 facts
(`x≥0 ⇒ div(x,pow2(x))=0 ∧ mod(x,pow2(x))=x`), and a complete **value table**
`⋁ₖ (x=k ∧ p=2^k)` for a `pow2` exponent pinned to a small window. `interval_of`
also learns the exact `pow2` interval on a bounded exponent, so the finite-box
enumeration decides bounded `pow2`-and-product rows (e.g. `2x² > pow2(x)`,
`7≤x≤9`) by concrete evaluation. All **7 committed `pow2-native` rows** decide,
matching cvc5. Row: **25 → 33 decided (64% → 85%), DISAGREE = 0,
model_replay_failures = 0.** The monotonicity axiom is guarded by `x ≥ 0` so
cvc5's `pow2-monotone-neg-soundness` (`x<y ∧ y²=4 ∧ pow2(y)≤pow2(x)`, **sat** via
`y=−2, x<−2, pow2=0`) is never wrongly refuted — the P0 negative-exponent
soundness test. Z3 has no native `int.pow2`, so the **new
`qf_nia_pow2_differential_fuzz`** encodes it independently as an exact nested-`ite`
ground-truth over the proven window and DELIBERATELY seeds the degenerate
negative and zero exponents (the fragile axis); DISAGREE = 0. Gated by
`nia`/`nra`/`qf_nia_pow2` differential fuzzes (all DISAGREE = 0),
`progress_frontier` (8/8), `corpus_regression`, `--workspace --lib`.

### QF_NRA cvc5 row re-measured 2026-07-06 (P2.5 slice 2 — `a²=−k` int↔real coercion + even-power-equality refutation)

**QF_NRA `qf-nra-cvc5-regress-clean` 26 → 27 decided (68% → 71%), unsat 12 → 13,
`unknown:Incomplete` 2 → 1; DISAGREE=0, model-replay-failures=0.** The one upgraded
file is `nl__very-simple-unsat` (`(= (* a a) (- 2))`), previously the coercion
residual the P2.5 census named. Two coupled, near-zero-risk changes close it:

- **The int↔real coercion routing.** The SMT-LIB front end parses `(- 2)` in a real
  context as `(to_real (- 2))`, so the atom reached only the (incomplete)
  Nelson-Oppen coercion relaxation and returned `unknown`. The **even-power
  refutation now sees through `to_real(<int const>)`** (`constant_real_value`) and is
  tried *before* the coercion relaxation in `check_auto_inner`; the NRA collector
  (`collect_int`) likewise coerces an integer numeral / `(- k)` under `to_real` into
  the real-poly form for direct `check_with_nra` callers. `to_real` is the exact
  ℤ ↪ ℝ embedding, so the coercion is value-preserving.
- **The even-power-*equality* arm.** `Σ tᵢ^{2kᵢ} = c` with `c < 0` is unsat because a
  sum of even powers is `≥ 0 > c` (the equality analogue of the existing
  `Σ tᵢ^{2kᵢ} < 0` refutation). Deliberately narrow — it requires at least one
  genuine even-power summand and a strictly-negative constant — re-scanned against
  the original assertion, and it only ever concludes `unsat`. `a² = 2` (sat,
  a = ±√2) stays sat: the arm declines on a nonnegative right side.

Soundness backing: **both** `nra_differential_fuzz` **and** `nia_differential_fuzz`
(shared multivariate path) vs the Z3 oracle, each **DISAGREE=0**; the change is
strictly additive (`unknown → unsat`, no decided verdict flips) and the only outcome
delta vs the prior baseline is the single `very-simple-unsat` upgrade.

### QF_S + QF_SLIA rows re-measured 2026-07-06 (P2.7 T-C.6 — lexicographic-order theory: `str.<=` / `str.<` over variables)

The lexicographic-order lever closes the last theory-coupled string gap the census
surfaced: `str.<=` / `str.<` were forced to a coarse `unknown` by the ADR-0052
bounded-string gate (a symbolic lex atom can miss a bound bite, so a bounded `unsat`
was downgraded). A new **certified refuter** (`axeyum-strings::lex_order`) decides the
reachable fragment behind an independent re-check, never trusting a search:

- **Arm A — variable-independent constant fold.** A lex atom over constant-prefixed
  concatenations decides at the first position where **both** operands have a
  determined code point (`≤` true when the left is smaller, false when larger),
  independent of any variable tail. Folding those constants through the Boolean
  skeleton can drive an assertion to `false` (`r0_QF_SLIA_leq` — a disjunction of
  always-true / always-false `str.<=` atoms).
- **Arm B — transitivity + first-character clash.** Over the `≤` atoms forced true by
  the top-level conjunction, the relation is transitively closed; a chain `s ≤* t`
  whose `lead(s)` (fixed by a word equality `s = c ++ …`) exceeds `lead(t)` forces
  `s > t` at position 0 (the prefix case is excluded), contradicting `s ≤ t`
  (`r1_QF_SLIA_strings-leq-trans-unsat` — `x ≤ y ≤ w`, `x = "G"++xp`, `w = "E"`,
  `71 > 69`).

The route only ever **adds a re-checked `unsat`** to an `unknown` (a satisfiable lex
script is already decided by the bounded encoder, whose `sat` is a concrete short
witness), so it can never override a decided verdict or fabricate one. Net (same
command, HEAD re-run): **QF_S 76 → 78 decided (unsat 25 → 27), QF_SLIA 16 → 18 decided
(unsat 8, oracle-compared 14 → 16), QF_SEQ 26 unchanged** (no sequence instance is in
the `str.<=`/`str.<`-over-strings fragment, so the lex channel never activates). Every
upgraded file agrees with the z3-binary oracle; **DISAGREE=0 and
model-replay-failures=0** across all three divisions. Soundness backing: a new
`qf_slia_lex_order_differential_fuzz` (800 generated `str.<=`/`str.<` chain scripts —
both polarities, `\u` escapes, byte-model boundary code points — vs **both** Z3 and
cvc5: z3 653/653 agree, cvc5 641/641 agree, all **DISAGREE=0**), plus an oracle-free
brute-force property test that confirms every certified `unsat` is truly unsatisfiable
over short strings (both directions).

### QF_S + QF_SLIA rows re-measured 2026-07-06 (P2.7 Phase D — constant-pattern extended functions as regex memberships + constant-fold `str.replace`)

Phase D opens the extended-function census remainder through two **exact,
polarity-guarded** parser reductions that feed the existing certified routes — no
new trusted machinery. **(1) Constant-pattern `prefixof`/`suffixof`/`contains`:** a
`(str.prefixof P X)` / `(str.suffixof S X)` / `(str.contains X C)` whose pattern is a
**string constant** and whose subject is a **single declared variable** is exactly a
regex-language membership (`X ∈ P·Σ*` / `Σ*·S` / `Σ*·C·Σ*`). Unlike the sat-implying
fresh-variable word reductions (sound only in a positive conjunction), a membership
atom is **polarity-symmetric** — the online route complements the language natively
for the negative literal — so the skeleton lifts these in **any** Boolean position
and the online CDCL(T) route decides them with the same per-class re-checked
derivative-emptiness certificate (`unsat`) and matcher-replayed model (`sat`). **(2)
Constant-fold `str.replace`:** `(str.replace H N R)` with **constant** haystack `H`
and needle `N` reduces at translation time to the exact first-occurrence splice
`H[..i] ++ R ++ H[i+|N|..]` (or `H` when `N ∉ H`; empty needle `⇒ R ++ H` at `i=0`) —
a value-preserving rewrite (verified against Z3 and cvc5), with `R` left symbolic.
A variable/compound pattern, a compound subject, or a variable haystack/needle
declines (unchanged verdict). Net (same-command HEAD re-run): **QF_S 74 → 76 decided
(unsat 23 → 25), QF_SLIA 15 → 16 decided (unsat 5 → 6), QF_SEQ 26 unchanged.** The
upgrades: `re.all` (QF_S — `x ∈ "abc"·Σ* ∧ ¬prefixof("abc",x)` is an empty class) and
`replace-find-base` (QF_S + QF_SLIA — `replace("ABCDEF","C",x)` folds to
`"AB"++x++"DEF"`, so the negated identity is `unsat`). Every upgraded file agrees with
the z3-binary oracle; **DISAGREE=0 and model-replay-failures=0** across all three
divisions. Soundness backing: the online-membership differential fuzz extended with
the Phase D constant-pattern `prefixof`/`suffixof`/`contains` atoms (both polarities,
`\u`-escaped/empty/boundary patterns), and a new
`qf_s_replace_fold_differential_fuzz` over pure-word constant-fold `str.replace`
scripts — each over 700 generated scripts vs **both** Z3 and cvc5, all **DISAGREE=0**.

### QF_NRA cvc5 row re-measured 2026-07-06 (P2.5 — census-driven levers: bounded sat-witness probe + threshold-1 monotonicity past the cap)

Two sound, cheap NRA levers move this row. **(1) A bounded rational sat-witness
probe** runs before the interval branch-and-bound: it tries a small fixed grid of
rational assignments (`{0, ±1, ±2, ±1/2}`; uniform for any variable count, full
product for ≤ 4 free reals) and returns `sat` only for a candidate that **replays
every original (division-intact) assertion true under the ground evaluator** — so
it can never emit a wrong `sat`, and closes the unbounded-free-variable `sat` class
the relaxation leaves as a timeout: the named nested-division `issue9164-2`
(`1/(a/b) > a²/a`, sat at a=1,b=2), the all-zero high-degree root `dist-big`
(`(Σvᵢ)⁴=0`), the high-power positivity `nlExtPurify-test`, and (bonus) the bounded
`poly-1025`. **(2) Threshold-1 monotonicity past the cross-product cap:** the
sign/zero refutation that already fires past the ADR-0024 cap now retries, as a
second bounded stage, with the threshold-1 monotonicity clauses (same cheap
`¬p ∨ q` shape, no McCormick/SOS) — refuting the `ones` benchmark
(`a,b,c,d ≥ 1 ∧ a·b·c·d < 1`) via the chained abstraction `r₀≥b≥1 ⇒ r₁≥c≥1 ⇒
r₂≥d≥1`. Staged *after* the sign-only solve so the extra clauses never slow the fast
zero-rule refutations (`subs0-unsat-confirm` stays `unsat`). Net (same-command HEAD
re-run, 10 s / 4 jobs): **decided 21 → 26 (sat 10 → 14, unsat 11 → 12), unknown
16 → 11, PAR-2 8.660 → 5.969, DISAGREE = 0, model-replay-failures = 0**; every mover
agrees with the z3-binary oracle. Soundness backing: **both** `nra_differential_fuzz`
(2000 seeds, 1641 jointly decided, 1478 sat replays verified) **and**
`nia_differential_fuzz` (2500 seeds, 2197 jointly decided) — shared multivariate
path — **DISAGREE = 0**; `progress_frontier`, `corpus_regression` green.

### QF_S + QF_SLIA rows re-measured 2026-07-06 (P2.7 T-C.6 — membership atoms in the online CDCL(T) route + the `\u` string-literal escape fix)

Two landings move these rows. **(1) Membership atoms in the online CDCL(T) string
route (T-C.6):** the Boolean-structured word skeleton now carries `str.in_re`
theory atoms, so the disjunctive / negated membership shapes the one-shot
side channel declines (atoms under `or` / `not(and)`) are decided — `unsat` only
behind a per-variable regex-intersection **re-checked derivative-emptiness
certificate**, `sat` only via a model whose per-class witnesses and membership-atom
truths are replayed by the **independent reference matcher** against the original
assertions. This decides the census shapes `re-mod-eq` (QF_SLIA + QF_S) and
`re-neg-unfold-rev-a` (QF_S), and the word-first-fallback `instance1079-re-loop-cong`.
**(2) A pre-existing SMT-LIB string-literal escape bug (fix(strings) seed-215):** the
byte-model encoder and word/skeleton route decoded string literals without expanding
the `\u{h…}` / `\uhhhh` Unicode escapes (the regex side always did), so `"\u{62}"`
was six raw bytes instead of the character `b` — a wrong verdict against Z3/cvc5 for
any literal with an escape (`issue9784`, `instance3303/7075-delta`, `regexp003`).
Net (same-command HEAD re-run): **QF_S 67 → 74 decided (sat 48 → 51, unsat 19 → 23;
oracle-compared 63 → 70; PAR-2 2.928 → 2.182), QF_SLIA 14 → 15 decided (unsat 4 → 5),
QF_SEQ 26 unchanged** (no `str.in_re` / no escaped literals). Every upgraded file
agrees with the z3-binary oracle; **DISAGREE=0 and model-replay-failures=0** across
all three divisions. Soundness backing: a new online-membership differential fuzz
over 700 generated Boolean-structured `str.in_re` scripts vs **both** Z3 (552 jointly
decided) and cvc5 (549) — all DISAGREE=0, both verdict directions exercised — plus
the T-C.5 regex-membership fuzz and the deterministic `\u`-escape regression suite.

### QF_S + QF_SLIA rows re-measured 2026-07-03 (P2.7 T-C.5 — regex membership via symbolic derivatives)

The `str.in_re` membership fragment now decides over **unbounded** strings via the
from-scratch symbolic-derivative engine (ADR-0054): transition-regex derivatives
with lazy `∩`/`∪`/`∁` (no determinization) and native `re.loop`. The parser gains a
regex-membership side channel (all-or-nothing over positive/negative `str.in_re`
atoms on variables/literals, length bounds, and literal pins), and the solver adds
a second-chance route strictly after the word routes decline. Verdict discipline:
`sat` only with a witness the **independent reference matcher** replays against
every atom; `unsat` only behind a **re-checked derivative-emptiness certificate**
(a finite, nullable-free, closure-verified residual set) or a matcher-refuted
ground atom. Net (same-command HEAD re-run): **QF_S 61 → 67 decided (sat 47 → 48,
unsat 14 → 19; oracle-compared 58 → 63; PAR-2 4.372 → 2.928), QF_SLIA 13 → 14
decided (unsat 3 → 4), QF_SEQ 26 unchanged** (no `str.in_re` files). The upgrades:
`norn-31`/`re-include-union`/`re-agg-total1`(+cli)/`regexp-strat-fix` (intersection/
inclusion emptiness), `a-in-comp-a` (ground complement), `re-inter-stack-ovf`
(deeply-nested `re.+`/`re.*` sat witness of length ≥ 15). Still `unknown` (out of
this slice's fragment): membership coupled with `substr`/`contains`/`to_int`
(`issue2958`, `username_checker_min`, `proof-fail-083021-delta`), disjunctive/
Boolean-`not(and)` shapes (`re-mod-eq`, `re-neg-unfold-rev-a`), and `re.all`+`prefixof`
coupling (`re.all`). DISAGREE=0 and model-replay-failures=0 across all three; the
z3-binary oracle agrees on every upgraded file. Soundness backing: the
fundamental-derivative-theorem property test (20k cases), a 2000-case brute-force
differential (sat=1218/unsat=782, wrong-unsat direction gated), and a regex-membership
differential fuzz vs **both** Z3 (627 jointly decided) and cvc5 (175) — all DISAGREE=0.

### QF_S + QF_SLIA rows re-measured 2026-07-03 (P2.7 A.2 — the len/code↔LIA bridge)

The `str.to_code` bridge in the unbounded length abstraction was upgraded from a
*wholly-free* integer to a **code-domain + length-coupled** twin: `str.to_code s`
maps to a fresh `Int c` with the universally-true fact
`(len(s)=1 ∧ 0≤c≤0x2FFFF) ∨ (len(s)≠1 ∧ c=-1)`, plus a single-character
**code↔equality link** `(len(p)=1 ∧ len(q)=1 ∧ c_p=c_q) ⇒ (p=q)`. Both are sound
relaxations of the *real* (Unicode) theory — the code cap is the SMT-LIB maximum
`0x2FFFF`, not the byte model's 255, so the abstraction can never refute a formula
satisfiable only above the byte range. The string gate now also runs the
abstraction on an `unknown` bounded verdict (not just to confirm/downgrade an
`unsat`): the abstraction being itself `unsat` proves the original `unsat`
bound-independent regardless of why the bounded integer bit-blast was undecided.
This decides the `str-code-unsat{,-2,-3}` code-range / code-arithmetic / distinct
conflicts the bounded 32-bit int blast left `unknown`. Net (same-command HEAD
re-run): **QF_S 58 → 61 decided (unsat 11 → 14; oracle-compared 55 → 58; PAR-2
5.141 → 4.372), QF_SLIA 12 → 13 decided (unsat 2 → 3; oracle-compared 11 → 12;
PAR-2 8.584 → 7.632), QF_SEQ 26 unchanged** — the `str.<=`-over-variables
lex-order and `seq.update` files honestly stay `unknown` (out of the code-bridge
scope). DISAGREE=0, model-replay-failures=0 across all three; the z3-binary oracle
agrees `unsat` on every upgraded file. Soundness: `unsat` only through the sound
length/code abstraction (documented per-fact relaxation argument); a 1500-case
never-refutes-a-model property test, a 400-case adversarial brute-force
cross-check, and the `str.to_code`-dense QF_S differential fuzz vs Z3 (474 jointly
decided) are all DISAGREE=0.

### QF_S row re-measured 2026-07-03 (T-B.7 slice 3 — certified concat-congruence refutation)

The census `str002`-class disjunctive shape now decides. The word refuter gained
a **concat-congruence / affix-cancellation disequality** conflict, re-checked
independently in `check_derivation.rs::check_congruence_equality`: a disequality
`a ≠ b` is refuted when the cited equalities force `a ≈ b` by equal-for-equal
congruence substitution (its own oriented rule set + a memoized, cycle-safe
expansion) + T-B.1 normalization + free-monoid common-affix cancellation. This
moves **`r1_QF_S_str002` unsupported → unsat: QF_S 57 → 58 decided (43% → 43%),
PAR-2 5.208 → 5.141, DISAGREE=0** (z3-binary oracle agrees `unsat`, oracle
compared 54 → 55). Attribution is a same-command HEAD re-run: exactly one
instance changed. **QF_SLIA (12 decided) and QF_SEQ (26 decided) are unchanged** —
the `quad-*-unsat` Kepler-22 quadratic word equations are single-equation
Nielsen/length refutations, NOT word-level cancellation, and the refuter honestly
declines them (verified per-file). A bench wiring fix was required so the
disjunctive word-first-fallback shape (`word_skeleton`, `word_problem` empty) is
routed through the online string route instead of the under-parse `unsupported`
guard — mirroring the existing `run_one` dispatch condition. Soundness: `unsat`
only through the independent re-check (mutation-tested, zero dangerous accept-path
survivors); word/qf_s_online/cvc5 differential fuzzes DISAGREE=0.

### BV quantified row re-measured 2026-07-03 (P2.6 slice 6 — closed-universal falsification)

A census of the 17 undecided `bv-cvc5-regress-clean-quantified` instances
retired the hypothesised lever (raise the e-matching round/instance budget) as
**unjustified — it would decide zero**: none of the 17 was
instantiation-depth/round-budget starved. The blockers are quantifier *shape*,
not depth — 16 are existential/`¬∃`/nested-`∀∃`/let-nested or free-parameter
`∀` shapes that never reach the top-level universal e-matching loop, and exactly
one (`qbv-simp`, `∀A B C D. (A=B∧C=D)∨(A=C∧B=D)`, declared `unsat`) reaches the
loop but has **no function-application trigger**, so no round budget helps. The
census-supported lever is therefore *closed-universal falsification*: a closed
`∀x⃗. body` (quantifier-free body over exactly its bound vars, no free
function/constant symbols) is a sentence decided exactly by one bounded
quantifier-free check of `¬body[x⃗:=c⃗]` — `Sat` ⇒ the universal is false ⇒
`unsat`. This moves **`qbv-simp` unknown → unsat: 37 → 38 decided (69% → 70%),
PAR-2 7.929 → 7.470, DISAGREE=0**. The valid direction is already owned upstream
by `quant_valid_universal`; only the refuting direction is taken here, so the
lever can never wrong-`unsat` a valid universal (soundness-guarded by the
900-seed `qinst_bounded_instance_soundness` brute-force oracle + a 600-seed
`quantified_bv_differential_fuzz` vs Z3, DISAGREE=0). The remaining 16 need
existential/prenex normalization or free-parameter e-matching, out of this
slice's scope.

### QF_NRA row re-measured 2026-07-02 (free-division `/0` witnesses + prior landings)

The first-class free-division witness landing (forced-div-by-zero promotes
`unknown` → `sat`; see
[P2.5 § 08](../docs/plan/track-2-theories/P2.5-nra/08-evaluation-and-soundness.md))
re-measured `qf-nra-cvc5-regress-clean` on the committed 10 s bench route:
**9 → 21 decided (24% → 55%), PAR-2 15.166 → 8.660, DISAGREE=0.** Attribution is
honest: the witness change itself moves **+1** (`cli__regress1__arith__div.06`,
`n=0 ∧ x/n=0 ∧ y/n=1`, declared/Z3 `sat`) against a same-command HEAD re-run
(20 decided) — the other +11 vs the stale committed row are the prior
sign-refutation + coprime-split CAD landings that had not yet been re-measured
on this route. `issue9164-2` (nested `1/(a/b)`) still declines: it needs the
FM → simplex lever in addition to the `/0` witness.

### QF_NRA row re-measured 2026-07-07 (equality-anchored bignum CAD entry + parser slices)

The P2.5 slice-4 + slice-7 landing (equality-anchored bignum CAD-entry path +
nullary `define-fun` Real-const coercion; task #43) re-measured
`qf-nra-cvc5-regress-clean` on the 10 s route (`--backend solver --compare-z3
--jobs 1` for contention-free timing): **27 → 32 decided (71% → 84%),
PAR-2 5.421 → 3.169, DISAGREE=0, model_replay_failures=0.** Attribution is honest:
**+3 are this landing** — `parser__real-numerals` (`(define-fun x () Real 0)` +
chained `(<= -1 x 3)`, `unsupported` → `sat`), `nl__approx-sqrt` (`x²=2` algebraic
√2 witness through three tight strict inequalities, `unknown` → `sat`), and
`nl__approx-sqrt-unsat` (the same √2 anchor under a top-level `or` of a
28-digit-rational disjunction, decided through the existing DPLL cube → exact CAD
edge once the pinning pair `x²≤2 ∧ x²≥2` anchors and the wide bignum-intermediate
coefficient clearing keeps the 10²⁸ denominator exact, `unknown` → `unsat`). The
other **+2** (`nl__very-easy-sat`, `nl__metitarski-3-4`) are **prior landings**
surfacing on this stale-baseline re-measure — both are multi-variable /
transcendental shapes the single-variable anchored path does not touch. `jobs 1`
was used because the `jobs 4` run flakes 1–2 boundary rows at the 10 s cap
(`nl__ones` is deterministically `unsat`, 5/5 at ~140 ms single-threaded). The
genuine-engine residue (`factor_agg_s`, the remaining MetiTarski rows,
`sin-cos`/`nt-lemmas-bad`) stays on the funded CAD/nlsat arc (ADR-0058).

### String rows re-measured 2026-07-02 (ADR-0052 gate — soundness over decide-rate)

The P2.7 A.2 landing re-measured QF_S/QF_SEQ/QF_SLIA under the bounded-string
`unsat` gate: a bounded `unsat` is reported only when confirmed
bound-independent; otherwise an honest `unknown`. Net: **QF_S 59→48 decided,
QF_SLIA 15→11, QF_SEQ 26 (unchanged)** — 23 prior `unsat` verdicts downgraded.
Of those, **two were on instances whose declared `:status` is `sat`**
(`r1_QF_SLIA_re-inter-stack-ovf.smt2`, `sat__regress0__seq__seq-nemp.smt2`):
the old rows were silently carrying real wrong verdicts the oracle path never
compared (it skips `unknown`s and the old runs' library oracle rejected the
logic on part of the slice). The other 21 are declared-`unsat` instances the
gate cannot yet confirm — recoverable via richer length facts / width widening
/ the Phase B word-level solver, tracked in
[P2.7 Phase A](../docs/plan/track-2-theories/P2.7-strings/03-phaseA-ir-sort-and-combination.md).
DISAGREE=0 holds on all compared instances; PAR-2 rose accordingly (honest
unknowns count as double-timeout). The 9-hour scoreboard hang met en route was
an exponential (per-path) DAG walk in the new blast's skeleton scan — fixed
(`f403991b`) with a regression test; the three divisions now measure in ~10
minutes total.

**2026-07-03 — the Phase B word route + word-first parse fallback moved QF_S
52→57 decided** (ADR-0053, T-B.4a/b/d + the harness-parity wiring): five
declared-`sat` instances the bounded encoder rejected at parse (long literals /
wide concats, incl. the quadratic word equation `r0_QF_SLIA_issue6520`) now
decide via the sat-only, ground-evaluator-replayed word-equation search; each
new `sat` is verdict-compared against the Z3 binary (all five agree,
DISAGREE=0). QF_SEQ (26/33) and QF_SLIA (12/50) are unchanged — their
`unsupported` remainder is `str.len`-linked / extended-function / unsat-shaped:
the next levers are the len↔search link, Phase C/D reductions, and T-B.7 unsat
derivations.

### String residual recoveries re-measured 2026-07-02 (ADR-0052 follow-up)

Three sound, bound-independent strengthenings of the abstraction/gate recover
**5 of the 21** gate-downgraded `unsat` files (**QF_S 48 → 52, QF_SLIA 11 → 12,
QF_SEQ 26 unchanged**; DISAGREE = 0; PAR-2 QF_S 6.676 → 5.564, QF_SLIA
9.537 → 8.584): a **step-1a LIA projection** (drop the pure-BV well-formedness
assertions — a sound weakening — so the mixed BV+Int abstraction refutes
`xx = xx ++ yy ∧ len yy > len xx`: `str004`); an **empty-string exact equality**
(`s = "" ⟺ len s = 0`, so `len s = 0 ∧ s ≠ ""` refutes: `str005`); and an
**empty-language regex fold** (`str.in_re s R` with `L(R) = ∅` → constant
`false`, a non-coarse ground atom: `re-comp/comp-all-is-empty`, `re-in-rewrite`
×2). Recoveries + soundness pairs are pinned by 8 new tests in
`bv2nat_blast_bounds.rs`. The remaining 16 are regex-*content*
(inclusion/intersection emptiness across separate `in_re` atoms) and
lexicographic (`str.<=`) refutations — **Phase B / A.3**, not length facts (see
[ADR-0052](../docs/research/09-decisions/adr-0052-string-len-lia-link-and-bounded-unsat-gate.md)).

### QF_UFLIA re-measured 2026-07-02 — both residual divisions now fully decided

`qf-uflia-cvc5-regress-clean` 6→8/8 and `-overbound-uninterp-sorts` 0→2/2
(DISAGREE=0, all 10 z3-compared). Per-instance timing attributes the movers to
the **UFLIA combination deadline threading** (`3cd6c810` — the former
timeout/budget declines now solve in ~2.3 s) on top of the accumulated
arithmetic landings; the model-assembly parity fix (`bff67679`) is verdict-
relevant only for skeleton-Bool SAT witnesses (none among the movers) but
repaired a wrong-default `false` witness value in the same builders.

### Public QF_BV (p4dfa 113): first committed lazy-vs-eager PAR-2 head-to-head (2026-07-03)

The north-star "measured performance" axis for public QF_BV now has a committed
PAR-2 head-to-head between the eager `sat-bv` backend and the lazy CEGAR
bit-blaster (`--backend lazy-bv`, ADR-0019), all five runs re-executed fresh at
one HEAD on the SMT-LIB `20221214-p4dfa-XiaoqiChen` slice (113 files, Z3
oracle, `--jobs 2`). These runs are not in the division table above (the
generator ingests only `*solver-vs-z3*` check_auto baselines); the committed
baselines are `qf-bv-20221214-p4dfa-sat-bv-z3-compare-1s-n1000.json` and
`qf-bv-p4dfa-fair-{sat-bv,lazy-bv}-vs-z3-{3s-n200k-cnf5M,20s-n300k-cnf8M}.json`.

| tier (budgets) | backend | decided | unknown breakdown | DISAGREE | replay fail | PAR-2 (s) |
|---|---|---|---|---|---|---|
| 1 s, node 1k (compare config) | eager sat-bv | 1 sat | NodeBudget 112 | 0 | 0 | 1.982 |
| 3 s, node 200k, cnf 2M/5M | eager sat-bv | 3 sat | T 87 / EB 13 / NB 10 | 0 | 0 | 5.855 |
| 3 s, node 200k, cnf 2M/5M | **lazy-bv** | **3 sat** | T 106 / EB 2 / NB 2 | 0 | 0 | **5.841** |
| 20 s, node 300k, cnf 3M/8M | eager sat-bv | 4 sat | T 98 / EB 10 / NB 1 | 0 | 0 | 38.643 |
| 20 s, node 300k, cnf 3M/8M | **lazy-bv** | **7 sat** | T 99 / EB 6 / NB 1 | 0 | 0 | **37.522** |

**Verdict: lazy-bv weakly dominates eager on this slice (3 = 3 decided at 3 s,
7 > 4 at 20 s; PAR-2 lower at both tiers; DISAGREE = 0, 0 replay failures) —
but the win is NOT the CEGAR abstraction.** Per-instance telemetry shows
`lazy_ops_total = 0` on all 113 files at both tiers: every instance falls
through `ops.is_empty()` to the full `solve()` front door, whose default
word-level preprocessing shrinks the encodings (EncodingBudget 13→2 at 3 s,
10→6 at 20 s; the 20 s decided set matches the committed `--preprocess` row's 7
exactly), while the bench `sat-bv` backend runs the raw eager blast with no
reduction. Attribution and next steps are recorded in
[the P2.1 findings note](../docs/research/05-algorithms/lazy-bitblasting-p21-findings.md);
the opt-in `SolverConfig::lazy_bv` dispatch (`10a412e`,
`tests/lazy_bv_dispatch.rs`) already exists, and default-on needs its own ADR.
Z3 decides all 113 in ≤ 1 s each — parity on this slice remains open, owned by
reduction depth.
<!-- NOTES:END -->

## Progress frontiers (lever depth)

Each frontier tracks how deep a single capability lever reaches: a family is scaled by a knob `N` and the **frontier** is the largest `N` axeyum still decides within budget. **Baseline** is the previously recorded frontier — the gap (frontier − baseline) is the gradual improvement this front exists to show.

| Lever family | Frontier | Baseline | Δ | Max knob | Budget (s) | Tracks |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| bv_reduction | 30 | 30 | 0 | 34 | 4 | QF_BV word-level reduction depth (unsat at knob N) |
| lia_cuts | 26 | 26 | 0 | 37 | 4 | QF_LIA branch-and-cut depth (sat at knob N) |
| nia_unsat | 40 | 40 | 0 | 40 | 4 | QF_NIA unsat-proving depth (knob N) |
| nra_degree | 40 | 40 | 0 | 40 | 4 | QF_NRA polynomial-degree decision depth (knob N) |
| string_bound | 8 | 8 | 0 | 12 | 4 | QF_S string-length bound (sat at knob N) |

## One-line summary

**35 division baselines measured vs z3 4.13.3, DISAGREE = 0 across all — zero wrong verdicts; decide-rate ranges 0%–100%.** DISAGREE = 0 everywhere is the soundness guarantee; decide% is the capability frontier we push, division by division.

## Provenance

Generated by [`scripts/gen-scoreboard.py`](../scripts/gen-scoreboard.py) from the following committed baselines (deterministic — no timestamps, fully sorted; re-running on unchanged inputs yields a byte-identical file):

- `bench-results/baselines/bv-bitwuzla-regress-clean-quantified-solver-vs-z3-10s.json`
- `bench-results/baselines/bv-cvc5-regress-clean-quantified-solver-vs-z3-10s.json`
- `bench-results/baselines/lia-cvc5-regress-clean-quantified-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-alia-cvc5-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-aufbv-cvc5-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-auflia-cvc5-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-ax-cvc5-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-bv-curated-bvred-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-bvfp-bitwuzla-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-dt-cvc5-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-ff-cvc5-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-fp-bitwuzla-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-lia-cvc5-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-lra-cvc5-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-nia-curated-iand-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-nia-cvc5-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-nia-synthetic-graduated-vs-z3.json`
- `bench-results/baselines/qf-nra-cvc5-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-nra-synthetic-graduated-vs-z3.json`
- `bench-results/baselines/qf-s-cvc5-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-seq-cvc5-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-slia-cvc5-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-uf-cvc5-regress-clean-bounded-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-uf-cvc5-regress-clean-bounded-uninterp-sorts-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-uf-cvc5-regress-clean-overbound-uninterp-sorts-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-ufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-ufbv-cvc5-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-ufff-cvc5-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-uflia-curated-named-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-uflia-cvc5-regress-clean-bounded-uninterp-sorts-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-uflia-cvc5-regress-clean-overbound-uninterp-sorts-solver-vs-z3-10s.json`
- `bench-results/baselines/qf-uflia-cvc5-regress-clean-solver-vs-z3-10s.json`
- `bench-results/baselines/uf-cvc5-regress-clean-quantified-solver-vs-z3-10s.json`
- `bench-results/frontier/bv_reduction.json`
- `bench-results/frontier/lia_cuts.json`
- `bench-results/frontier/nia_unsat.json`
- `bench-results/frontier/nra_degree.json`
- `bench-results/frontier/string_bound.json`

Regenerate with `python3 scripts/gen-scoreboard.py`.

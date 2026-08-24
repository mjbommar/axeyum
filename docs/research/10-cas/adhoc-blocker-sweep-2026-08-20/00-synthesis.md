# Ten-lens blocker sweep: synthesis

Date: 2026-08-20
Status: ad hoc research synthesis, outside the normal roadmap/gates.
Inputs: diaries 01-10 in this directory (each with its own FINDINGS section,
references fetched and verified by web, and independent reproductions).
Every claim below is sourced to a diary; finite computation remains
evidence, never a theorem.

## Headline

Ten field-specialist agents attacked the endpoint blocker in parallel.
Net effect: **nine broad route-classes are now closed with proofs or exact
witnesses** (several upgrading the lane's "measured shortfall" entries to
"impossible at any strength"), **two ledger/review claims are corrected**
(one each direction), and the surviving frontier is **narrower, weaker, and
better instrumented** than the one the lane was pursuing this morning.

The single most consequential pair of findings (07 + 09, independent
instruments): **the lane's live target `K_4 <= M_2^2` / `R_0 <= 4` is
~`2^ell` stronger than the endpoint needs.** The weakest sufficient form is
`M_4 < mean^4 = 2^(4(n-ell))`; measured truth is `M_4 ~ 0.6 ell^3 2^(3ell)`,
i.e. **exponential slack `2^ell/ell^3`**. At `ell = 200` the sufficient
threshold is `R_0 <= 2^171.5` against the pursued `R_0 <= 4`. A proof may
lose `2^(ell/4)` and still close the endpoint (consistent with 01's Linnik
profile: primes arrive at `ell + O(log ell)`, so the conjecture holds with
exponential room).

## Closed route-classes (proof or exact witness; diary in parentheses)

1. **Any individual-character estimate, including the optimal one** (02):
   exact L-polynomials of ALL `2^ell - 1` characters for `ell <= 14` show
   `sum |S_chi|` already exceeds the endpoint allowance from `ell = 6`, and
   `sum |Re S_chi|` from `ell = 10`. Every surviving route must keep
   characters signed.
2. **Moment/Hölder ladder at every order** (01, 03): the `sqrt(ell)` loss is
   independent of the moment order (proved two ways). Explains every
   recorded Cauchy/Hast--Matei shortfall at once.
3. **Black-box correlation bounds** (08): refuted by a constant-phase
   adversary; the phase is a depth-2 nonclassical polynomial, the exact
   Bhowmick--Lovett barrier class. All content is in the signs.
4. **Fixed-modulus 2-adic congruences** (05, 07): `v_2(I_n(1))` over
   `n = 3..61` matches a random 2-adic integer; the lane's own `ell = 27`
   row refutes `(C8)`-type statements. (Review note Move 1: downgraded.)
5. **Newton-slope route to the needed congruence** (04): `2 | Delta` needs
   `v_2(trace) >= ell+1`; the unique slope hypothesis delivering it is
   supersingularity, REFUTED at `ell = 4` (exact slope multiset
   `{1/4, 1/2, 3/4}`). p-adic floors lose to trivial counting from
   `ell = 4` on. Sharp reformulation retained: odd endpoint holds iff
   `Delta !== 1 (mod 2^(ell+1))` — one forbidden residue class;
   `v_2(I) = v_2(Delta - 1)`.
6. **Iwasawa / Ferrero--Washington route** (05): the exact analogue exists
   on this very tower (Angles--Bandini--Bars--Longhi, Math. Ann. 2020) and
   is triply vacuous at `q = 2` ("We need q > 2" verbatim; empty index
   range; `gamma = 0` kills the class module). mu-statements are
   existential/precision-zero where a prescribed coefficient with `ell+2`
   digits is needed.
7. **Cyclic/Foulkes Betti target `B(n,r) <= n^4`** (06): REFUTED at
   `n = 401`: required Betti mass `>= 2^214.3` vs allowance `2^49 - 1`
   (165 bits). All twelve induction base rows fail. Architectural death:
   `2^omega(n)` summands of size `2^365` must cancel to relative precision
   `2^-164` — no bound on individual summands can recover this. (Review
   note Move 3.1: withdrawn before external handoff.)
8. **PFR / inverse-theorem squeeze** (09): circular — the failure mode is a
   degree-one obstruction where the `U^2` inverse statement is the identity
   being bounded; an uncertainty-principle lemma shows low-conductor
   equidistribution is structurally unable to contribute a minorant.
9. **Hitting-set/PRG derandomization** (10): at the Lemire dimension there
   exist affine subspaces (multiples of a fixed prime) with ZERO
   irreducibles, so no generic subspace theorem can have content.
   Also closed: all rational/composition transforms outside the new
   classification (10), Kedlaya-based range extension (04), Green--Tao
   restriction/enveloping sieve with explicit deficit (09), exact
   Kerdock/DG enumerators beyond the discharged low-conductor corner (07).

## Ledger corrections (both directions)

- **The odd-degree construction claim is WRONG in the ledger** (10):
  "the 95 Capell rays omit every odd degree" holds only for `k = 3`.
  The criterion generalizes to every odd `k | 2^d - 1`, iterates by the
  same LTE argument, and against the repo's own 400 committed witnesses
  yields **367 eligible seeds and 172 of 200 odd degrees covered**
  (spot-verified by independent Rabin certificates). Action: generalize
  `axeyum-gf2-capell-audit` with a falsification control.
- **Odd-endpoint rows are ~700x cheaper than the lane's method** (07):
  `N = 1 + n I` needs only `I` — `2^ell` irreducibility tests; `ell = 24`
  in 2.3 s / ~1 MB vs 25m41s / 10.3 GB. New rows `ell = 25, 26, 28, 29, 30`
  computed: `Delta = -42333, -102128, 32552, -221070, -238629`.
- Katz's Thm 5.1 (`SL(ell-1) ⊂ G_geom` at `p = 2`, `ell >= 4`) is a proved
  asset the ledger under-records (03). The Hast--Matei deficits
  `(ell-1)/2, (ell-1)/4` are the mean L-degree, i.e. the genus — the
  blocker's log factor IS the genus (07). `M_2` IS Keating--Rudnick
  variance; `K_4 <= M_2^2` is the fixed-q case of Montgomery--Soundararajan
  (open over Z) — one more reason to target the weak form (09).
- Small unconditional theorem, analysis-free: **Ax--Katz proves the odd
  endpoint for `n <= 7`**, and provably cannot extend (`N_9(1) = 37` odd)
  (07).

## The surviving frontier, ranked

A. **Weakened fourth moment** `M_4 < 2^(4(n-ell))` (07, 09). Exponential
   slack, measured. Immediate actions: (i) add the weak threshold beside
   `R_0 <= 4` in the implication ledger; (ii) **resurrection audit** — every
   shortcut refuted against the strong allowance whose loss grows only
   poly(ell) is NOT refuted against the weak one; re-measure their
   ell-scaling; (iii) push 08's `(E2') + (S)` split (one `sum c_F^2`
   accumulator in the existing Rust fibre report, rows `ell = 10..12`).
B. **Global hypercontractivity on the Efron--Stein/Witt grading** (09):
   hypothesis is globalness, not degree; required constant `<= 3.11` vs
   sharp two-point `3`. One measurement (E1) decides.
C. **Equivariant localized trace formula** (06): surviving purity target
   `|Tr(Frob . c | H*_c) - 2^h| <= C n 2^(h/2)`, matched by exact data;
   missing lemma = a local wildly-ramified twisted Milnor number at `p = 2`
   at the `phi(oddpart n)` eigenlines the lane already classified
   (Saito CC; Yang--Zhao Invent. 2025; relative Lefschetz--Verdier).
   Expert one-pager (re-aimed at THIS statement) is in diary 06.
D. **Laumon local Fourier transform + Abbes--Saito explicitness in
   Schmid--Witt coordinates** (02): signed, family-wide, wild-native.
   The Schmid--Witt residue formula (`chi_a(g) = (-1)^{res(a dlog g)}`,
   verified `ell <= 8`) is new machinery for the repo regardless.
E. **Constructive coverage** (10): generalized odd-`k` Capell rays
   (172/200 odd degrees) + the new power-of-two composition family
   (241 witnesses; iterates 8 -> 64 -> 512; one reduced open lemma would
   make every power of two inductive). Every covered degree is a degree
   the analytic route no longer owes.
F. **Fallback deliverables**: density-one-in-degrees via averaging over `n`
   (03, Cha--Fiorilli--Jouve); the `h_c^(2ell-1)` first-moment measurement
   over `GF(2^r)` that can kill or fund the geometric route by data (03);
   Newton-over-Hodge at `p = 2` verified for 32766 characters, zero
   violations — a publishable conjecture in its own right (04); Paper A is
   STRONGER than previously stated: the lane's `n/2 + O(log n)` theorem
   beats every published prescribed-coefficient result at `q = 2` (10).

## Process notes

- Three independent reimplementations (Python/sympy, single-file C, and a
  throwaway Rust crate) reproduced the CAS's pinned integers exactly —
  external replication the ledger lacked (08, 05, 04, 09).
- The reviewer's original Moves 1 and 3.1 were refuted by this sweep; the
  re-aim review has been annotated accordingly. That is the sweep working
  as intended.
- The shared checkout advanced during the sweep (another lane is active in
  `gf2_hayes.rs`); all sweep writes were confined to this directory.

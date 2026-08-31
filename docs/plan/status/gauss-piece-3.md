# Lane: gauss-piece-3 -- Gauss's-lemma connecting theorem, piece 3

<!-- plan-section: lane-status -->

**Your lane's block (`PARTIAL`, gauss-piece-3, 2026-08-31).** Verified
ADR-0990's five-item piece-3 sizing against the tree before starting (all
citations confirmed present or absent as ADR-0990 said, plus two items
found already de-risked by unrelated same-day work -- see ADR-1050).
Landed two of the five items in full, both axiom-free, both admitted by
the kernel on the FIRST attempt:

- **Item A, `∏(a·k) = a^m·m!`**: `Int.prodRange_const_pow` (`prodRange
  (fun _ => a) n = pow a n`, no case split) plus
  `Int.prodRange_scaledIndexEqPowMulFactorial` (`prodRange (fun k => mul a
  (ofNat (succ k))) m = mul (pow a m) (factorial m)`, chaining
  `prodRange_mul` + `prodRange_const_pow` + `factorial`'s own defeq unfold,
  no induction of its own).
- **The sign-product item** (ADR-0990: "no existing analogue found"):
  `Int.prodRangeIf_constEqPowCount` (`prodRangeIf pred (fun _ => a) n =
  pow a (Nat.countRange pred n)`, built GENERICALLY in `euler_theorem.rs`
  because Euler's theorem's own module doc names the identical shape as
  its remaining gap -- one lemma serves both targets) plus its one-line
  Gauss corollary `Int.gaussSignProdEqPowNegOneOfCount`.

Full route, citations, and the precise sizing of what remains: **ADR-1050**
(`docs/research/09-decisions/adr-1050-gauss-lemma-piece-3-two-of-five-items-land-generically-reusable-with-euler.md`).
Read it before starting the next session on this -- it verifies against
the tree two things ADR-0990 could not have known: `Int.modEq_prodRange`/
`Int.modEq_prodRange_lt` and `Int.mod_eq_of_nat_mod_eq` (the `Nat`/`Int`
`ModEq` bridge) both landed elsewhere the same day, changing the sizing of
item 1 and item 3 below.

**What remains -- three items, NOT attempted this session**, each sized in
ADR-1050 with the exact lemma names checked or flagged unchecked:

1. The per-term congruence `a·k ≡ ε_k · gaussFold(pp,a,k) [pp]` for `k =
   1..m` -- a `Bool`-case-split proof comparable in size to
   `gauss_fold_injective_of_coprime` (ADR-1015), PLUS a `Nat.mul`-to-
   `Int.mul` distribution lemma this session found is also needed and did
   not check for an existing name.
2. `gcd(m!, pp) = 1` -- an induction using `Nat.coprime_mul_of_coprime`
   (confirmed present) and `Nat.coprime_of_lt_prime` (confirmed present by
   ADR-0990); unresolved whether it needs a `Nat`-side `factorial` mirror
   since `Int.factorial` cannot feed a `Nat.gcd` argument directly, or
   whether an `Int`-typed coprimality primitive already avoids that detour
   -- check `wilson.rs` first.
3. The final assembly, chaining everything above plus a `ModEq`
   cancellation step (name not yet matched against `modeq_cancel_div_gcd.rs`/
   `int_prelude/modeq.rs`) -- estimated mostly bookkeeping once items 1-2
   land, since every structural piece (induction, permutation, sign
   product, scaled-product identity) now exists.

**Verify each of ADR-1050's citations in-tree before treating them as
real** (the standing rule: a handoff's "what remains" is a lower bound on
one route's cost, not a fact about the cheapest route) -- this session
found two of ADR-0990's own citations already stale in the OTHER
direction (present when ADR-0990 said "not confirmed"), so the next lane
should expect the same in either direction.

Verification this session: `cargo test -p axeyum-lean-kernel --lib
int_prelude::` (56 passed, 0 failed, up from 53); `cargo test -p
axeyum-lean-kernel --lib nat_prelude::` (263 passed, 0 failed, sanity
check, unaffected); `cargo clippy -p axeyum-lean-kernel --lib -- -D
warnings` (same 8 pre-existing errors before and after, none in touched
files, confirmed via `git log -1 -- <file>` on each); `derived_laws`
pinned array recounted 223 -> 227 across four commits via
`scripts/recount-pinned-inventory.py` (never hand-incremented);
`theorem_axiom_footprint` confirmed footprint `0` for all four new
declarations by their KERNEL (camelCase) names -- the Rust snake_case
field name silently matches nothing in that tool's substring filter, worth
noting since it cost one wasted invocation this session.

No fact-ledger entries added this session (kernel declarations only). New
names checked against the full source tree and `artifacts/facts/` before
landing -- no collisions.

<!-- plan-section: landed-changes -->

| 2026-08-31 | gauss-piece-3 | `Int.prodRange_const_pow`, `Int.prodRange_scaledIndexEqPowMulFactorial` (Gauss's-lemma item A, `∏(a·k)=a^m·m!`, complete) and `Int.prodRangeIf_constEqPowCount` (built generically for both Euler's theorem and Gauss's lemma) + `Int.gaussSignProdEqPowNegOneOfCount` (Gauss's-lemma sign-product identity, complete) land axiom-free toward Gauss's lemma's connecting theorem (ADR-1050). Two of ADR-0990's five piece-3 items now closed; three remain, precisely sized in ADR-1050 with two of ADR-0990's own "not confirmed present" citations verified present. |

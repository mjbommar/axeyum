# Lane: nat-stragglers — the two `Nat` stragglers left by `283-nat-div-mod-family`

<!-- plan-section: lane-status -->

**DONE for this dispatch (`nat-stragglers`, 2026-08-29).** Both targets closed.

```
F:ml430-nat-add-div-of-dvd-add-add-one-f17dffc0   -- proved
F:ml430-nat-base-induction-83561d4c               -- proved
```

**`add_div_of_dvd_add_add_one`.** `∀ {c a b}, c ∣ (a+b+1) → (a+b)/c = a/c+b/c`.
The prior lane's route sketch (compare divisibility's forced remainder
against a case split on `ra+rb` vs `c`) was directionally right but the
actual derivation needed was cleaner than either sketch or my own first plan:
decompose `a=c*qa+ra`, `b=c*qb+rb` via `div_mod_exec`, so `a+b+1 =
c*(qa+qb)+(ra+rb+1)`. Case-split `ra+rb+1` against `c` (`lt_or_ge`) — below
`c` this is ALREADY a valid `divMod` decomposition of `a+b+1`, and comparing
it against the one the `dvd` witness gives (remainder `0`) via
`div_mod_unique` forces `ra+rb+1=0`, refuted by `succ_ne_zero` since it's a
successor. At or above `c`, subtracting `c` once (`sub_add_cancel`) gives a
remainder `r'` also `<c` (bounded via `ra<c`,`rb<c` and
`le_of_succ_le_succ`/`add_le_add_left`/`add_le_add_right`/`le_trans`), and
comparing THAT decomposition against the same `dvd`-witness relation forces
`r'=0`, i.e. `ra+rb+1=c` exactly — pinning `ra+rb=c-1<c`, which closes the
goal against `div_mod_exec`'s own decomposition of `a+b`. No case-split on
the `dvd` witness `q`'s shape was needed at all (an earlier plan detour I
abandoned once the derivation above worked without it). New file
`nat_prelude/div_mod_lemmas.rs` extension (the ninth/last mirror in that
family); module doc there has the full step list.

**`base_induction`.** `∀ {P:ℕ→Prop}{n:ℕ}(b:ℕ), 1<b → (∀m<b,P m) → (∀m k,
k<b→0<m→P m→P(b*m+k)) → P n`. I had not analysed this one at all going in.
**Read the pinned source before sizing it** — `command -v lean`/mathlib4
checkout is a separate question from what the fact actually needs, and here
it mattered doubly: the nursery manifest's `module`/`source_group` already
say `Init.Data.Nat.Div.Lemmas`, and reading
`~/.elan/toolchains/leanprover--lean4---v4.30.0/src/lean/Init/Data/Nat/Div/Lemmas.lean:256`
confirms this is **Lean core, not Mathlib proper**, and — the part that
decided whether it was even attemptable — `P : Nat -> Prop` is fixed at
`Prop` (never an arbitrary `Sort*`), and the declaration is a `theorem`
proved via `Nat.strongRecOn`, not a `def`. That means it is **not** the
fuel-cannot-be-a-dependent-recursor case that permanently blocks a mirror
(`Nat.binaryRec` et al.): proving `∀n,P n` for a fixed proposition-valued `P`
needs no computational recursor, only ordinary well-founded strong
induction — and this prelude already has that primitive
(`NatPrelude::lt_well_founded` + `WellFounded.fix`, used the same way by
`declare_gcd_semantics`/`declare_gcd_bezout`/
`declare_exists_prime_factorization`/`declare_irrational`). New file
`nat_prelude/base_induction.rs`: `P:Nat->Prop` is a genuine motive parameter,
so `NatOps::theorem`'s `Nat`-only arity mechanism can't express the
statement, so the declaration is hand-assembled (`pi_fv`/`lam_fv` chains,
the same way `Nat.dvd`/`Nat.modEq` are in `divisibility.rs`/`modular.rs`).
Route (module doc has the full derivation): `WellFounded.fix` with `step`
case-splitting `lt_or_ge v b` — `Lt v b` closes by `single v`; `Le b v`
decomposes `v=b*qv+rv`, case-splits `qv` (`qv=0` contradicts `Le b v`;
`qv=succ qvpred` bounds `qv<v` via `mul_le_mul_left`+`le_add_right`+
`le_succ_succ` (`mul qv 2` is defeq `add qv qv`) + `mul_comm` + `le_add_right`
again — three `lt_of_lt_of_le`-style chains), then closes by `digit qv rv
(rv<b) (0<qv) (ih qv (qv<v))` transported along `v=b*qv+rv`.

**Two real bugs found and fixed while landing this, both via the same
technique** (a throwaway `#[test]` dumping `Kernel::render_lean` of both
`TypeMismatch` sides at the FIRST build failure — CLAUDE.md's standard
bisection move for an opaque top-level mismatch, and the fastest path both
times: each bug was isolated and fixed within one debug-probe round-trip):

1. `add_div_of_dvd_add_add_one`: a swapped `d.symm` argument order.
   `congr(r_prime, zero, r_prime_eq_zero, |v| add(v,c))`'s ACTUAL type is
   `Eq r_prime_c zero_c` (that operand order, matching `congr`'s `f a`/`f b`
   convention), and the first draft called `d.symm(zero_c, r_prime_c, …)` —
   backwards. Same defect class the div/mod shift family hit in the prior
   lane's own commit history; still easy to get wrong because `congr`'s
   output order is easy to misremember under `symm`'s own argument order.
2. `base_induction`: a transport source/target mixup in the `qv=0`
   contradiction branch. `bound`'s actual type is `motive(rv)` (`Lt rv b`),
   so the transport SOURCE must be `rv` and the TARGET `v`, via `Eq rv v` —
   the first draft used `v` as source and `rv` as target with the hypothesis
   in the un-reversed direction, which type-checks as a well-formed `Eq.rec`
   application but produces a value of the WRONG type (`Lt v b` demanded,
   nothing of that type available at that call site) rather than failing to
   parse — exactly the shape CLAUDE.md's `le_congr`/`symm` direction-bug
   family warns is indistinguishable from other `TypeMismatch` causes without
   rendering both sides.

**Verification (both facts together, final state):**
`env -u RUST_MIN_STACK scripts/cargo-serialized.sh test -p axeyum-lean-kernel
--lib nat_prelude::` — **164 passed, 0 failed** (162 baseline + 2 new:
`add_div_of_dvd_add_add_one_applies_at_concrete_discriminating_instances`
at two instances chosen to discriminate — `(5,7,7)` equal `a`,`b` with
nonzero quotients/remainders summing to `c-1`, and `(5,3,11)` asymmetric
`a<c<=b` to catch an `a`/`b` swap — and
`base_induction_applies_at_a_concrete_recursive_instance`, which actually
exercises the recursion: `P:=Le zero`, `n=5`, `b=2` forces several `qv=v/2`
levels before landing in the `Lt v b` base case). `cargo fmt --all --check`
and `cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` both
clean. `python3 scripts/check-test-attribute-integrity.py` clean (9106
`#[test]` attributes, 0 findings). `nat_axiom_inventory --require-axiom-free
nat`: `axiom=0 opaque=0 quotient=0`, exit 0 (both new declarations are
axiom-free). `python3 scripts/validate-facts.py`: 0 errors. The
`the_build_is_deterministic` pin moved `93+531 -> 93+532 -> 93+533` (one
recount per landed declaration, each taken from that run's own panic
message, never hand-incremented).

Both facts flipped to `epistemic_status: proved`, each with a kernel-term
evidence row (`nat_theorem_inventory -- <name>`, rendered type compared
verbatim against `formal.statement`, and each `checker_command` verified to
return count 0 on a `_bogus` variant of the name) and an
exhaustive-enumeration axiom-freedom row (`nat_axiom_inventory
--require-axiom-free nat`). `proof_route: kernel-lean`,
`axiom_footprint: []` on both. `base_induction`'s fact also records the Lean
core (not Mathlib) provenance correction in its notes/evidence, since the
mirror-flip criterion depends on reading the actual pinned source rather
than inferring from the `ml430` family name.

**Commits** (not pushed, in order): `5ff4b316b` (add_div_of_dvd_add_add_one,
compiles), `abc3b7210` (add_div_of_dvd_add_add_one, fixed + verified +
fact), `1069ff40c` (base_induction, compiles), `fad6b8fb3` (base_induction,
fixed + verified + fact).

**Nothing left open in this lane's dispatch.** If picking up `nat_prelude/`
work next: `docs/research/11-design-review/2026-08-27-retrieval-is-the-bottleneck.md`
and this file's own `CLAUDE.md` gotchas list are both worth a pass before
sizing the next family — several "needs new machinery" calls in that
inventory turned out to already exist, or (as here) to be smaller than they
looked once the actual pinned source was read rather than inferred from the
fact's `formal.statement` alone.

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-stragglers | `Nat.add_div_of_dvd_add_add_one` — the ninth/last `ml430` add/div/mod shift-family mirror, axiom-free (new file `nat_prelude/div_mod_lemmas.rs` extension). |
| 2026-08-29 | nat-stragglers | `Nat.base_induction` — strong induction over `Nat.lt`'s well-foundedness, axiom-free (new file `nat_prelude/base_induction.rs`); confirmed the pinned source is Lean core (`Init.Data.Nat.Div.Lemmas`), not Mathlib proper. |

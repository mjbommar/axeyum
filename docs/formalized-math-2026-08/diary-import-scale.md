# Diary — lane `import-scale`, 2026-08-15

Continuing [`diary-whnf-cache-key.md`](diary-whnf-cache-key.md), which closed the
last root blocker on the committed 40-declaration corpus and ended with the
right instruction: *40/40 means this corpus has stopped measuring; replace it
with whatever exercises the rules we know we lack.*

Outcome in one line: **the corpus is now the environment itself — all 96,591
`Init`+`Std` declarations and all 680,925 Mathlib ones are exported and
sampled — the binding constraint turned out to be kernel `Nat` literal
arithmetic and is fixed, and the next one is `String` literals, which block
52% of a random `Init`+`Std` declaration and 85% of a random Mathlib one.**

## 1. Export the environment, not a corpus

`lean4export` takes a module list and an optional constant list, and **with no
constant list it dumps every non-internal constant in the environment**. That is
the whole answer to "a corpus nobody chose":

| | records | declarations | wall | peak RSS | size |
|---|---|---|---|---|---|
| `lean4export Init Std` | 10,516,909 | **96,591** | 25 s | 1.4 GB | 552 MB |
| `lean4export Mathlib` (v4.30.0, s5) | — | **680,925** | ~4 min | ~7 GB | 5.5 GB |

Mathlib is `leanprover-community/mathlib4` tag `v4.30.0` (`c5ea0035`), built on
s5 from `lake exe cache get` — 8,459 cached archives, 8,101 oleans, 77 seconds
end to end. The previous lane was right that no published bulk dump exists; it
turns out not to matter, because producing one costs four minutes once the
oleans are on disk. Both streams live under `/nas3/data/axeyum/lean-import-scale/`.

Declaration counts by kind, `Init`+`Std` / Mathlib: theorems 69,074 / 488,593,
definitions 26,074 / 182,298, inductives 972 / 6,900, opaques 464 / 3,127,
axioms 7 / 7.

## 2. The whole-environment stream cannot be censused in one pass — and *why* is the first result

The obvious next move is to run the 10.5M-record `Init`+`Std` stream through
`census_ndjson` and read off the distribution. It does not work, and the way it
fails is worth the paragraph.

Three minutes in, RSS was 22 GB and climbing at ~4 GB/min. Rather than guess, I
read the process's own file offset:

```
/proc/<pid>/fdinfo/<fd of the ndjson>   ->   pos=2342912   (0.4% of 578 MB)
```

and read it again a minute later: **identical, while RSS grew another 3 GB.**
Not slow — stuck, on one declaration. The last declaration record at or before
that offset is line 44957, `Nat.Linear.Expr.denote_toPoly_go`. Exported alone it
reproduced immediately: 8,450 records, every dependency admitted, and then no
answer at all — 25 GB and counting.

So a single stream through the trusted gate has a third outcome besides admit
and decline: it can **diverge**. A census that only counts the first two reports
such a declaration as neither, and — this is the trap — a whole-environment run
that dies partway through looks exactly like a resource problem rather than a
located one.

## 3. The binding constraint: literal `Nat` arithmetic

`Nat.Linear.Expr.denote_toPoly_go` is `omega`'s reflection infrastructure, which
told me nothing. What did was looking at the literals in the streams that failed:

```
$ grep -o '"natVal":"[0-9]*"' Option.repr.ndjson | sort -n -u | tail
2047  4096  55296  57343  65535  262144  1114112  4294967296
```

`55296`/`57343` are the UTF-16 surrogate range, `1114112` is `Char`'s bound,
`4294967296` is `2^32`. **`Char`, `UInt8/16/32/64`, `USize` and `Fin` are `Nat`
under bounds like these**, and this kernel had no rule for `Nat.add` on
literals — only `Nat.succ` folding and offset equality. Reaching `2^32` by
successor steps is not slow, it is unbounded.

Lean's kernel has had the rule since forever
(`references/lean4/src/kernel/type_checker.cpp:609`, `type_checker::reduce_nat`):
fourteen binary operations evaluated directly on literal arguments —
`add sub mul div mod gcd pow land lor xor shiftLeft shiftRight beq ble` — tried
after `whnf_core` and before δ. `Kernel::reduce_nat_binop` is that rule,
arbitrary-precision on `NatLit`'s `BigUint`, with Lean's totality conventions
(`x / 0 = 0`, `x % 0 = x`, truncated `sub`) and Lean's `ReducePowMaxExp` bound of
`1 << 24` on the exponent.

**What it bought, on the three declarations that provoked it:**

| declaration | before | after |
|---|---|---|
| `Nat.Linear.Expr.denote_toPoly_go` | 25 GB, no answer in 4 min | clean, 190 records, **0.04 s** |
| `Option.repr` | 8 GB address space exhausted in 95.7 s | reaches the next wall in **0.05 s** |
| `Lean.Parser.Attr.extIff` | 8 GB exhausted in 78.9 s | reaches the next wall in **0.05 s** |

### The guards, because this widens definitional equality

`build_nat_binop_table` admits an operation only if the environment declares it
as a **`Definition`** (never an axiom or an opaque), with **no universe
parameters**, and with **exactly** `Nat → Nat → Nat` or `Nat → Nat → Bool`; and
only in an environment whose `Bool` is Lean's — a parameter-free, index-free,
non-recursive inductive in `Type` whose constructors are `[false, true]` **in
that order**, both nullary, at indices 0 and 1. Any of those failing leaves the
table empty and no arithmetic fires at all.

Two details that are not decoration:

- **The type is checked by walking the two `Pi` layers, not by comparing
  interned ids.** Binder *names* are part of an interned `Pi` node and the
  official export spells `Nat.add`'s type with named binders `n`/`m`, so an id
  comparison against a locally built arrow never matches. My first version did
  exactly that and the rule silently never fired; the three-minute census was
  unchanged, which is how I found it.
- **The table looks names up, it does not intern them.** `Kernel::name_str`
  mints on miss, name ids are dense and assigned in insertion order, and the
  lean4export writer emits them in that order — so a reduction that minted
  `Bool.true` while checking a declaration renumbered the entire subsequent
  export. `axeyum_lean_import::export_round_trip::axeyum_built_prelude_round_trips`
  caught it, on the first `in` record that differed (`Or` vs `Bool`). The new
  `Kernel::lookup_name_str` is a non-interning query, and the expression-level
  equivalents (`sort`, `const_`) are now built only *after* the declaration shape
  has established that they already exist.

### The residual trust, stated as a test

The rule is keyed on the *name* `Nat.add`. So is Lean's. It cannot check the
body — and for `div`, `mod` and `gcd` **no checker could**, because those are
well-founded recursions in Lean whose unaccelerated kernel reduction is stuck by
construction, which is the reason the acceleration exists. I considered
validating each operation against its own definition on a small grid at bootstrap
and rejected it: it would disable exactly the operations that need the rule.

So the trust is Lean's, and `acceleration_trusts_the_declared_type_not_the_body`
says so with a passing test — an environment declaring `Nat.beq := fun _ _ =>
false` still gets `beq 3 3 ≡ true` — rather than with a comment nobody reads.
`axeyum-lean-import` consumes official exports only, and that is now a load-bearing
statement rather than a habit.

### Our own preludes are untouched, and by mechanism

`build_logic_prelude` declares `Bool` with constructors in the order
`[true, false]`. Lean's is `[false, true]`. So the table is refused for every
environment our reconstruction preludes build, every operation keeps computing by
its own declared body, and nothing about the 119-theorem `nat` inventory or its
empty axiom footprint can move because of this change.
`tc_tests::the_reconstruction_prelude_is_not_accelerated` asserts the constructor
order, asserts `nat_binop_table()` is `None`, and then checks the prelude's
`Nat.add 2 3` still computes.

### Controls: each guard removed in turn

A negative test that passes with the rule disabled proves nothing, so every
clause came out one at a time and the suite was re-run.

| control | effect |
|---|---|
| rule not installed at all | **4 positives fail**; every negative still passes |
| declared type not checked | `a_wrongly_typed_declaration_is_not_accelerated` fails |
| axiom/opaque accepted as an operation | `an_axiom_or_opaque_named_like_an_operation_is_not_accelerated` fails |
| arity not required to be exactly 2 | `only_an_exactly_binary_application_is_evaluated` fails |
| Lean's `pow` exponent bound removed | `a_huge_exponent_leaves_pow_stuck_instead_of_exploding` fails |
| `Bool` **constructor-name order** clause dropped | **nothing fails** |
| `Bool` **constructor-index** clause dropped | **nothing fails** |
| **both** `Bool` order clauses dropped | `a_bool_whose_constructors_are_in_the_wrong_order_disables_the_table` fails |

The last three rows are the previous lane's lesson in a new costume. The two
`Bool`-order clauses are individually redundant and jointly load-bearing: each
alone rejects a swapped `Bool`. That is a fine place to be — but a table with one
row saying "the `Bool` order clause is load-bearing" would have been wrong, and I
only know which is which because the controls were run separately.

### And the answers are checked by Lean itself

`tests/real_lean_nat_arithmetic_crosscheck.rs` (new, registered in
`scripts/check-lean-gate.sh`) generates its obligations from **this kernel's**
output: for 24 argument pairs — both totality conventions, truncated `sub`,
`gcd` with a zero, `pow 0 0`, and values past `2^32` and `2^64` — `Kernel::whnf`
produces a value and that value is rendered as `example … := rfl` for official
Lean 4.30.0 to check. Lean accepts all 24. Mutating one convention in our
arithmetic (`x % 0` from `x` to `0`) makes Lean reject, so the crosscheck
discriminates. Real-Lean floor raised 105 → 107; measured total is now 115.

## 4. The distribution at scale, with cascades separated

`scripts/lean-import-scale-census.sh` (new) samples the environment's own name
list with a recorded seed, exports each sampled declaration's dependency closure
as its own stream, and censuses each under an OS-enforced wall-clock and
address-space bound. Per-stream, so a diverging declaration costs one bucket
rather than the whole run.

**500 random `Init`+`Std` declarations, seed 20260815, 34,112 declaration
records**, with the `Nat` rule in place, on the shipped binary (512 MB stack,
120 s and 8 GB per stream):

| outcome | streams |
|---|---|
| CLEAN | 219 (43.8%) |
| **UNSUPPORTED — `literal-string-typing`** | **262 (52.4%)** |
| DECLINED (kernel refused something) | 16 (3.2%) |
| RESOURCE (neither admitted nor declined) | 3 (0.6%) |

(An earlier pass at 60 s and 4 GB on the 8 MB default stack reported 218 clean
and 4 RESOURCE; §5 is about the one that moved and the three that did not.)

**400 random Mathlib declarations, seed 20260815, 13,710 declaration records:**

| outcome | streams |
|---|---|
| CLEAN | 78 (19.5%) |
| **UNSUPPORTED — `literal-string-typing`** | **315 (78.8%)** |
| DECLINED | 7 (1.8%) |
| RESOURCE | 0 |

And the methodology's whole point. `Init`+`Std`: 265 declines, **243 cascades**,
**6 distinct roots**. Mathlib: 154 declines, **144 cascades**, **5 distinct
roots** — and *four of the five are the same declarations*:

| root | `Init`+`Std` streams | Mathlib streams |
|---|---|---|
| `Nat.bitwise._unary` | 13 | 6 |
| `Nat.Linear.Poly.denote_reverse` | 3 | 1 |
| `Nat.Linear.ExprCnstr.denote_toNormPoly` | 3 | 1 |
| `Fin.shiftRight_val` | 1 | — |
| `List.attach_cons` | 1 | — |
| `_private.…DTreeMap.Internal.Zipper.prependMap.eq_def` | 1 | — |
| `Fin.addCommSemigroup._proof_1` / `_proof_2` | — | 1 / 1 |

**Not one Mathlib-specific root blocker.** Every declaration this kernel refuses
in a 400-strong Mathlib sample lives in Lean's `Init`/`Std` core — `Nat.bitwise`,
`Nat.Linear`, `Fin`. Whatever Mathlib does on top of that core, this kernel
already checks; category theory, measure theory, affine geometry and functional
analysis are in the clean 78 (`geometric_hahn_banach_point_point`,
`MeasureTheory.martingalePart`, `AffineSubspace.vsub_left_mem_direction_iff_mem`,
`HasOuterApproxClosed.measure_le_lintegral`,
`CategoryTheory.Functor.flipping_unitIso_hom_app_app_app`, `Submonoid.card_bot`).
That is a stronger statement than the clean rate, and it is the one worth
carrying forward.

Each declined stream admits **everything except the declaration that was asked
for** — `Nat.bitwise._unary`: 302 records, 301 admitted, one `TypeMismatch`. So
these are a handful of specific definitional-equality failures, not missing
subsystems. I located them and did not diagnose them; that is the honest state.

## 5. A fourth outcome class: runaway reduction, and one real fix

The four RESOURCE streams of the first pass looked like memory exhaustion at the
4 GB cap. Some were actually `thread 'main' has overflowed its stack` on the
default 8 MB — a *different* failure wearing the same shell exit code, which is
the sort of thing that gets filed as "needs a bigger machine".

The census example now runs its work on a 512 MB stack, which is what Lean does
for its own kernel (`lean -s`). **That fixed exactly one of the four**:
`UInt16.toFin_ofNatTruncate_of_lt` now imports cleanly in 3.8 s. The other three
— `Char.toUpper`, `Char.utf8Size.fun_cases_unfolding`, `UInt32.ofFin_lt_iff_lt` —
run *longer* with the bigger stack, reach ~6.3 GB of heap, and overflow 512 MB
anyway; raising the address-space cap to 16 GB only buys them more time before
the same abort. They are runaway reductions, not deep-but-finite ones, and no
stack size retires them.

I wrote "all four import in under two seconds" in that doc comment before
measuring the other three; the measurement is in the comment now instead. That
is this repository's own standing rule — prefer a measurement to a message,
including the message you have just written — and it caught me inside an hour of
writing it down.

## 6. The next binding constraint: `String` literals

Every UNSUPPORTED stream stops at the same place —
`axeyum-lean-import/src/lib.rs:582`, `"strVal" => Err(unsupported(line,
"literal-string-typing"))` — and the kernel behind it refuses
`Lit::Str` in `infer` (`KernelError::UnsupportedLit`). This is not a reduction
rule that is missing; it is an IR construct that was deferred, and it is now the
single largest blocker by a wide margin.

**Size, from Lean's own sources, with the call sites:**

| piece | where Lean does it | shape |
|---|---|---|
| accept `strVal` on the wire | `lean4export` format 3.1.0 | one arm in `import_expression`; the payload is a JSON string, so escape handling is `serde`'s |
| type a string literal | `type_checker::infer_lit` | `Lit::Str : String`, gated by a `String` bootstrap the way `nat_literal_bootstrap` gates `Nat` |
| literal → constructor | `kernel/inductive.cpp:1200`, `string_lit_to_constructor` | UTF-8 decode to code points, then `String.ofList (List.cons (Char.ofNat c₀) … List.nil)` |
| use it in reduction | `type_checker.cpp:360` | a projection or recursor whose major is a string literal expands first |
| use it in `def_eq` | `type_checker.cpp:1030`, `try_string_lit_expansion` | a literal against a `String.ofList …` application, symmetric in both argument orders |
| emit it again | `lean_export.rs:97` currently refuses | the writer's round-trip is a committed gate, so this is not optional |

The bootstrap has to validate five declarations rather than three (`String`,
`String.ofList`, `Char.ofNat`, `List.nil`/`List.cons` at `Char`), and note that
in Lean 4.30 `String` is `structure String where ofByteArray :: (toByteArray :
ByteArray) (isValidUTF8 : …)` — so `String.ofList` is a **definition**, not a
constructor, and the conversion produces a δ-reducible term rather than a
constructor application. That is a real difference from the `Nat` case and the
place a port gets it wrong.

Estimate: **comparable to this lane's `Nat` work, perhaps 1.5×** — call it one
focused session, of which the kernel change is maybe 200 lines and the rest is
the bootstrap, the negative suite (a literal must not be definitionally equal to
a *different* literal's expansion; a non-Lean `String` must disable it; the
writer must round-trip) and a real-Lean crosscheck of the same shape as the
arithmetic one.

What it would buy is **not** 52% clean. It buys 52% of streams *reaching the next
wall*; `Option.repr` went from diverging to failing on strings in 0.05 s, and
what lies past strings for those 262 is unmeasured. Anyone quoting a projected
clean rate from this number is quoting me wrongly.

## 7. Gates

- `cargo test -p axeyum-lean-kernel -p axeyum-lean-import` — green; **14 tests
  new here** (13 in `tests/nat_literal_arithmetic.rs`, 1 in `tc_tests`).
- `cargo clippy -p axeyum-lean-kernel -p axeyum-lean-import --all-targets
  --all-features -- -D warnings` — clean.
- `./scripts/check-lean-gate.sh` — **13 suites, 50 tests, 115 real-Lean checks
  (floor raised 105 → 107)**, Lean 4.30.0.
- `python3 scripts/validate-facts.py` — 98 facts, **0 errors**.
- `scripts/check-imported-fact-lean-axioms.sh` — 5 declarations cross-checked,
  0 failed.
- `nat_theorem_inventory` — **119 theorems**; `nat: axiom=0`, `integer:
  axiom=1` — unchanged, and unchanged *by mechanism* (§3).

## 8. What I did not do

- **`String` literals.** Sized in §6 and deliberately left; a half-implemented
  literal-expansion rule in the trusted kernel is worse than none, and this is
  the second definitional-equality widening of the session.
- **Diagnosing the six root blockers.** Located, reproduced, not explained.
- **The three runaway `Char`/`UInt32` reductions.** They will most likely be
  understood as a by-product of whatever explains the six above.
- **A fact.** Nothing here establishes a proposition; it is capability plus
  measurement, pinned by tests and by one re-runnable script.
- **The toolchain re-pin (4.30.0 → current).** Fourth diary to say so.

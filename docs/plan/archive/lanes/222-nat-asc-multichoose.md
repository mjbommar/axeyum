# Lane: nat-asc-multichoose — `Nat.ascFactorial` and `Nat.multichoose`

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, nat-asc-multichoose, 2026-08-28).** Both
definitions landed with boundary lemmas, evaluation tests, and six new
`F:nat-*` facts.

`Nat.ascFactorial` mirrors `Nat.descFactorial` exactly (`NatOps::define_binary`,
structural recursion on the second argument), climbing with `Nat.add` instead
of descending with truncated `Nat.sub`. `ascFactorial_zero`/`_succ` hold by
`Eq.refl` (no fuel device); `ascFactorial_one` reduces to `Nat.mul_one`'s own
proof term, exactly like `descFactorial_one` reduces to it.

`Nat.multichoose n k := choose (pred (add n k)) k` is a plain non-recursive
abbreviation over already-declared `Nat.add`/`Nat.pred`/`Nat.choose` — not a
fresh recursion. `multichoose_zero_right` needs no reduction at all
(`choose_zero_right` holds for any first argument); `multichoose_one_right`
reduces fully by ι alone (`add n 1 ≡ succ n`, `pred (succ n) ≡ n`, then
`choose_one_right` closes it — no lemma beyond that one); `multichoose_one`
is the one genuinely needing a `congr`/`trans` chain, because `Nat.add`
recurses on its RIGHT argument and the literal `1` sits on the LEFT
(`add 1 k` stuck for symbolic `k` — bridged via `succ_add`/`zero_add`).

Every definition carries a concrete-instantiation evaluation test with a
negative control catching the copy-paste class of bug the kernel's trusted
gate cannot see (a `Definition` type-checks whatever it computes):
`asc_factorial_evaluates_correctly` checks `3.ascFactorial 2 = 12` against a
DESCENDING-product control (`3*2=6`, and `3.descFactorial 2`) that an
`add`/`sub` swap would still type-check but compute; `multichoose_evaluates_correctly`
checks `3.multichoose 2 = 6` against the `pred`-dropped value `10` a copy-paste
omitting `- 1` would compute.

Measured: `nat: axiom=0 opaque=0 quotient=0 total_trusted=0`
(`nat_axiom_inventory --require-axiom-free nat`) — the eight new declarations
(2 definitions — `ascFactorial`, `multichoose` — plus 6 theorems —
`ascFactorial_zero/_succ/_one`, `multichoose_zero_right/_one/_one_right`)
add zero axioms. `nat_prelude::` suite: 109 passed, 0 failed (was 107 before
this lane). `cargo fmt --check` and
`clippy --all-targets --all-features -D warnings` both clean.

Did NOT attempt `F:ml430-nat-factorial-dvd-ascfactorial-44a4e641`
(`k! ∣ n.ascFactorial k`) — a genuinely nontrivial divisibility induction,
out of scope for this slice per the brief ("landing ONE definition with its
boundary lemmas is a complete success"). No target in this lane's families
(`natural-binomial`, `natural-factorial`) carried a HELD-OUT or MUTATION
marker.

New facts (do NOT flip any `F:ml430-nat-*` mirror fact — these are our own
independent constructions): `F:nat-asc-factorial-zero`,
`F:nat-asc-factorial-succ`, `F:nat-asc-factorial-one`,
`F:nat-multichoose-zero-right`, `F:nat-multichoose-one`,
`F:nat-multichoose-one-right`. `python3 scripts/validate-facts.py`: 0 errors.

Next lane: `factorial_dvd_ascFactorial` (needs a real induction over
`Nat.dvd`/`Nat.choose` algebra), or `Nat.zero_ascFactorial` in our own
prelude (currently only closed via the separate autogenesis statement-
reflexivity route, not this kernel's `Nat.ascFactorial`).

<!-- plan-section: landed-changes -->

| 2026-08-28 | nat-asc-multichoose | `Nat.ascFactorial`/`Nat.multichoose` definitions + 6 boundary theorems + 6 new `F:nat-*` facts |

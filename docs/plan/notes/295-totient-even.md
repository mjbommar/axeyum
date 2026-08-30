# Notes: 295-totient-even

Detail moved out of [`../status/295-totient-even.md`](../status/295-totient-even.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Verification.** `cargo test -p axeyum-lean-kernel --lib nat_prelude::` —
167 passed, 0 failed (165 baseline + 2 new, each with a concrete instance
at `a`/`n` in `{1,2}`, a negative reduction control at `totient 6 = 2 !=
1`, and a genuinely-free-variable instance via `LocalContext`/`infer_in`).
`cargo fmt` (per-file `rustfmt --edition 2024`, workspace `cargo fmt` is
banned in a shared checkout) and
`cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` both
clean (one `#[allow(clippy::too_many_arguments)]` needed on
`trichotomy_elim`, matching the precedent at `restrict_pair.rs`'s
`compact_pair_off`). `python3 scripts/check-test-attribute-integrity.py`:
0 findings. `the_build_is_deterministic`'s pin moved from `93 + 534` to
`93 + 536` (2 new theorems), taken from the panic message's own mismatch
(627 vs 629), not hand-incremented.

Both facts' `evidence` carries a `kernel-term` row (`nat_theorem_inventory`,
verified both to pass on the real name — count 1 — and fail on a fabricated
one — count 0, exit 1) and an exhaustive-enumeration axiom-freedom row
(`nat_axiom_inventory --require-axiom-free nat`, exit 0). `depends_on` was
populated by hand against the counting machinery, then completed by
`scripts/check-fact-depends-derived.py --fix` against the actual proof
term's direct dependencies (13-14 nat-prelude basics each, none carrying
their own fact entry — unregistered nat-prelude theorems, not axioms, per
the empty-footprint evidence). `python3 scripts/validate-facts.py`: 2034
facts, 0 errors.

**Commits** (not pushed): `c12bd6271` (wip, unverified), `f502afe95` (the
two theorems + tests + pin, verified), `644be1664` (the fact-ledger flips).

## Part 2 — `Nat.totient_even`, hand-traced and numerically checked, NOT built

**Did not build this.** The construction below is genuinely more concrete
than the prior triage's characterization ("needs the classical
fixed-point-free-involution pairing argument... not machinery this prelude
has"), and most of its pieces turn out to already exist — but it still
needs one new induction principle, and landing it wrong under time pressure
would be worse than handing off a checked plan. Every claim below was
verified in Python before being written down (scripts kept at
`/tmp/claude-1000/.../scratchpad/totient-even-check.py` and
`totient-even-verify2.py` in this session's scratchpad — not committed,
reproduce inline below since the scratchpad is ephemeral).

### The statement

`Nat.totient_even : ∀ n, Lt 2 n -> Even (totient n)`, where `Even n :=
Exists (fun k => Eq n (add k k))` (`nat_prelude.rs`'s `even` field).

### Step 0 — peel index 0 for free

`countRange f 1 = 0` since `f 0 = beq (gcd 0 n) 1 = beq n 1 = false` for
`n > 1` (`gcd_zero_left`). So `totient n = countRange f n =
countRange_split(f, 1, n-1)'s second summand = countRange (shift f 1)
(n-1)` — counting is unaffected by dropping index `0`. This is a
`countRange_split(f, 1, n-1)` application, already available, composed with
the `countRange f 1 = 0` reduction (cheap, `n > 2` so `n != 1`).

Define `h(j) := f(1+j) = beq (gcd (1+j) n) 1`, `L := n - 1`. Goal becomes
`Even (countRange h L)`.

### Step 1 — the reflection `h`-invariance, from EXISTING lemmas only

**Verified: no new gcd lemma is needed.** For `0 <= j < L`, writing `k1 :=
1+j` and `k2 := 1+(L-1-j)`, `k1 + k2 = n` exactly (checked for all `n` in
`[3,40)`, all `j < L`). The claim `h(j) = h(L-1-j)`, i.e. `beq (gcd k1 n) 1
= beq (gcd k2 n) 1`, reduces to `gcd k1 n = 1 <-> gcd k2 n = 1`, which
chains through THREE already-declared `Iff`s (no new arithmetic fact,
verified in Python for all `n` in `[2,40)`, all `k` in `[1,n)`):

```
gcd (n-k) n  =  gcd (n-k) k     -- coprime_add_self_right-shaped, at (n-k, k):
                                   n = (n-k)+k, so this is "coprime (n-k)
                                   ((n-k)+k) <-> coprime (n-k) k"
             =  gcd k (n-k)     -- coprime_symmetric
             =  gcd k n         -- coprime_add_self_right-shaped, at (k, n-k),
                                   reversed: n = k+(n-k)
```

Composing the three `Iff`s is ordinary `Iff`-transitivity (build it by hand
via nested `iff_intro`/`or_elim`-free function composition of each hop's
`mp`/`mpr` — no `iff_trans` field exists in this prelude today, but nothing
stops writing it inline, or adding a tiny local `iff_trans` helper). The
exact hypotheses needed from `coprime_add_self_right`/`coprime_add_self_left`
(both already declared, `nat_prelude.rs` fields of the same name) are
`Iff (gcd m (add n m) = 1) (gcd m n = 1)`-shaped; matching `k1`/`k2` to the
`add` form needs `n - k = (n-k)` restated as an actual `add`-term via
`Nat.sub_add_cancel`-shaped rewriting (`k <= n`, in fact `k < n` here) —
check whether this exists under `sub_add_cancel`/`add_sub_cancel'`-style
names before rebuilding it; several `sub`/`add` round-trip lemmas already
exist elsewhere in `nat_prelude/` for exactly this purpose (used
pervasively in `finite.rs`'s own index bookkeeping).

### Step 2 — no true fixed point

Fixed point of the reflection at position `j` is `j = L-1-j`, i.e. `2j =
L-1 = n-2`, i.e. original index `k1 = 1+j` satisfies `2*k1 = n`. If `h(j) =
true` there, `gcd k1 n = 1` with `n = 2*k1` forces `gcd k1 (2*k1) = k1 =
1`, so `n = 2`, contradicting `2 < n`. Verified in Python for all `n` in
`[3,60)`: whenever `j = L-1-j`, `h(j)` is `false`.

### Step 3 — the general combinatorial lemma (THE NEW PIECE)

```
Nat.count_range_reversal_even :
  ∀ (h : Nat -> Bool) (L : Nat),
    (∀ j, Lt j L -> Eq Bool (h (sub (pred L) j)) (h j)) ->
    (∀ j, Lt j L -> Eq Bool (h j) true -> Not (Eq Nat j (sub (pred L) j))) ->
    Even (countRange h L)
```

Proof sketch, by strong/well-founded induction on `L` (this prelude already
has strong recursion over `Nat` -- see `nat_strict_well_foundedness_
drives_generic_strong_recursion` in `nat_prelude_tests.rs` and whatever
`lt_well_founded`-based constructor it exercises):

- `L = 0`: `countRange h 0 = 0`, `Even 0` via witness `0`.
- `L = 1`: the single index `j=0` is its own mirror (`pred 1 - 0 = 0`), so
  hypothesis 2 forces `h 0 = false`, giving `countRange h 1 = 0`.
- `L >= 2`: peel BOTH ends in one step.
  - Front: `countRange h L = countRange h 1 + countRange (shift h 1)
    (L-1)` via `countRange_split(h, 1, L-1)`, and `countRange h 1 =
    [h(0)?1:0]`.
  - Back: `countRange (shift h 1) (L-1)`, with `L-1 = succ (L-2)` (since
    `L>=2`), peels its OWN top index via `countRange`'s ordinary defining
    equation (the same equation `countRange_succ_of_true` already
    extracted): `countRange (shift h 1) (succ (L-2)) = countRange (shift h
    1) (L-2) + [(shift h 1)(L-2) ? 1 : 0]`, and `(shift h 1)(L-2) = h(L-1)`.
  - So `countRange h L = [h(0)?1:0] + [h(L-1)?1:0] + countRange (shift h 1)
    (L-2)`. By hypothesis 1 at `j=0`: `h(L-1) = h(pred L - 0) = h(0)`, so
    the two boundary terms are EQUAL, contributing `0` or `2` (even) either
    way -- no case split on which needed.
  - Recurse on `h' := shift h 1`, `L' := L-2` (verified in Python: `h'`
    inherits BOTH hypotheses at length `L'`, by direct index substitution --
    `h'(j) = h(1+j)`, and hypothesis 1 for `h'` at `j` unfolds to exactly
    hypothesis 1 for `h` at `1+j`, landing on `pred L' - j = L-3-j`
    corresponding to original index `L-2-j = pred L - (1+j)`, matching).
    `L' < L` (since `L >= 2`), so the strong induction hypothesis applies.
  - `Even a -> Even (a + 2)`-shaped closure for the final sum (trivial:
    witness `k+1` from `a = 2k`).

**This is the one genuinely new piece.** Everything else in Part 2 composes
existing lemmas. The risk is entirely in this induction's bookkeeping
(matching `pred`/`sub` forms exactly, and picking the right induction
principle -- a literal "peel 2 elements" recursion needs either genuine
well-founded recursion on `L` or an explicit two-case-per-step structural
device; `Nat.rec` alone does not give you `P(L) -> P(succ (succ L))`
without also carrying `P(succ L)` as a side hypothesis you then discard, so
reach for the well-founded route rather than fighting `Nat.rec` directly).

### Step 4 — closing the mirror

Apply `count_range_reversal_even` at `h := shift(totient_predicate(n), 1)`,
`L := n-1`, using Steps 1-2 for its two hypotheses, then rewrite `Even
(countRange h (n-1))` back to `Even (totient n)` via Step 0's `countRange_
split` identity (reversed).

### Numerically verified (all in this session's scratchpad, not committed)

- `gcd(n-k,n) = gcd(k,n)` via the three-`Iff` chain: checked for `n` in
  `[2,40)`, every `k` in `[1,n)`.
- The index correspondence `k1=1+j`, `k2=1+(L-1-j)`, `k1+k2=n`: checked for
  `n` in `[3,40)`, every `j < L`.
- No true fixed point: checked for `n` in `[3,60)`.
- The double-peel recursion (Step 3's literal recursive definition,
  executed in Python) reproduces `totient(n)` exactly for `n` in `[3,30)`.
- `totient(n)` is even and has no fixed point in the raw `k <-> n-k`
  pairing over `[0,n)`, for `n` in `[3,60)`.

### What is NOT yet checked

- Whether `Nat.sub_add_cancel`/`add_sub_cancel'`-shaped rewriting (needed
  to restate `n-k` as an `add`-term for `coprime_add_self_right`/`_left`)
  exists under a name this file didn't grep for. Check before rebuilding.
- The exact shape of this prelude's well-founded/strong-recursion
  constructor (only confirmed a TEST exercises it, not read its API).
- Whether `Even`'s existential witness composition (`a = 2k -> a+2 =
  2(k+1)`) is already a named lemma or needs inline `Exists.intro` at
  `succ k`.

**For the next lane:** Part 2's weakest step is Step 3 (the new induction
principle) -- everything else is either already-declared machinery or a
short chain of already-declared `Iff`s. Build Step 3 as a standalone,
`totient`-independent lemma first (it has no `totient`/`gcd` content at
all), test it in isolation against a synthetic `h`/`L`, and only then wire
it to Steps 0-2 and 4.

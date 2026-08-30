# Lane: nat-coprime-family — all nine `Nat.Coprime` mirrors closed

<!-- plan-section: lane-status -->

**DONE for this dispatch (`nat-coprime-family`, 2026-08-29).** All nine
target facts closed: `epistemic_status: proved`, `proof_route: kernel-lean`,
`axiom_footprint: []`.

## The task

```
F:ml430-nat-coprime-coprime-div-right-7a8ce438
F:ml430-nat-coprime-coprime-dvd-left-2ce391d2
F:ml430-nat-coprime-coprime-dvd-right-4a2670ae
F:ml430-nat-coprime-coprime-mul-left-fb5bd11a
F:ml430-nat-coprime-coprime-mul-left-right-910d7d8f
F:ml430-nat-coprime-coprime-mul-right-70e4e946
F:ml430-nat-coprime-coprime-mul-right-right-9599ecd3
F:ml430-nat-coprime-dvd-of-dvd-mul-left-b0608cb9
F:ml430-nat-coprime-dvd-of-dvd-mul-right-efc3a4ec
```

All nine mirror `Init.Data.Nat.Coprime` — Lean **core** (not mathlib4
itself). Confirmed by reading the pinned toolchain source directly:
`~/.elan/toolchains/leanprover--lean4---v4.30.0/src/lean/Init/Data/Nat/Coprime.lean`.
`Nat.Coprime m n := gcd m n = 1` there, matching this prelude's own
convention (`rel_prime.rs`'s module doc: `Coprime` is never given a separate
name here, always spelled `gcd _ _ = one` inline) — so every mirror-flip
here is the honest kind (same definition, not a theorem about a different
one).

## Step 0 — two were already proved

`primes.rs`'s `Nat.coprime_of_dvd_left`/`Nat.coprime_of_dvd_right` (built
for an earlier, differently-named fact) state the IDENTICAL propositions as
`coprime-coprime-dvd-left`/`coprime-coprime-dvd-right` once `Coprime` is
unfolded — checked by comparing argument roles against the doc comment, not
by name. Closed as thin one-line wrappers under the Mathlib name rather than
aliases, to keep the one-fact-one-declaration correspondence the ledger's
checkers lean on.

## The other seven

New file `crates/axeyum-lean-kernel/src/nat_prelude/coprime_lemmas.rs`
(all nine declarations, one dispatcher `declare_coprime_lemmas`, called from
`build_nat_prelude` right after `declare_coprime_of_dvd_both`):

Detail moved to [`../notes/296-nat-coprime-family.md`](../notes/296-nat-coprime-family.md).


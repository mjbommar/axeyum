# Lane diary — ledger-integrity / int-euclid (2026-08-16)

The working record behind this lane's PLAN.md block, kept here so the block
stays a queue entry. This is the policy the lane itself established on the same
day: PLAN.md sources are capped at 52 KB, and detail belongs beside the other
diaries rather than in the tracker. Writing this file was prompted by watching
the sources reach 51,643 bytes — this lane was about to re-break the gate it had
just repaired.

**Landed the claim dashboard's gate, and the type check whose absence hid the
bug** (`WIP`, ledger-integrity, 2026-08-16). Strand item
[`04-gates-and-truth.md`](04-gates-and-truth.md) T1
("every gate reports its own scope"), and finding 8's shape one level down: the
defect was not a wrong number, it was three layers each trusting the one below.

**What was actually wrong — three defects, not one.**

1. `artifacts/claims/rado/rado-r4-a6-b5-frontier/claim.json` wrote `would_settle`
   as a one-element **list**; `claim.schema.json` declares `"type": "string"`.
2. `validate-claims.py` checked which frontier keys were *present* and never what
   they *held*, so the ledger reported **104 claims, 0 errors** over a claim that
   violated its own schema. The file already carries a `schema_drift()` check
   whose comment says "a schema no code reads is decoration" — that argument
   applied to field names but had never been extended to their types.
3. `gen-claims-dashboard.py` therefore crashed on `fr['would_settle'].strip()`,
   and **was wired into no gate at all** — not `check.sh`, not the `justfile`.

So the committed `DASHBOARD.md`, headed *"Auto-generated. Do not edit by hand"*,
reported **38 claims across 1 family** against an actual **104 across 3**, and
listed the campaign's flagship result `R_4(5(x-y)=4z)` as `open` at `> 740` when
the ledger had it `computed` at exactly **741**. Nobody edited it wrongly. Nobody
ran it.

**Both negative controls exercised, not asserted.**

- The new type check was run *before* the data was fixed and rejected the real
  claim with exit 1 — `frontier.would_settle must be a string, got list`.
- `--check` was run against a deliberately dirtied `DASHBOARD.md` and exited 1,
  then against the restored file and exited 0.

**Gated in both aggregates, deliberately.** `--check` joins `generated-trackers`
in the `justfile` (beside `gen-plan.py` and `gen-adr-index.py`, the other two
generated views) and `check.sh` gains `claims-validate` and `claims-dashboard`.
The claim ledger's structural gates previously ran only from `just claims`, which
is not part of `just check`; both are seconds long and need nothing external, so
the no-`just` fallback had no reason to be blind to them. The certificate pass
stays out of both — it needs the gitignored `drat-trim` clone.

**Next for this lane.** The larger half of finding 8: **40 of 162 checker runs
across 36 settled facts exit 0 on completion alone**, including
`nat_axiom_inventory`, which prints its number and exits 0 whatever it is — so
`axiom_footprint: []` on 31 kernel-lean facts, this project's headline
axiom-freedom metric, is asserted by nothing. Re-measure the count first
(`b94b56425` already fixed one example), then make each checker's exit status
depend on its finding, one exercised negative control per fix.

**Returned `main` to green: PLAN.md 225,019 -> 47,409 bytes** (`WIP`,
ledger-integrity, 2026-08-16). `just check` could not pass — `plan-authority`
failed at 233,888 bytes against a 52,000 ceiling, and had failed since
`69d32216b`, the commit that split PLAN.md into per-lane sources. The ceiling and
that design could not both stand: `docs/plan/global/` alone is 43,348 bytes of
the budget, so even a 500-byte cap across 43 lanes would not have fit. Resolved
by taking CLAUDE.md's framing literally — PLAN.md is an **active work queue** —
and archiving finished and cut-off lanes to
[`docs/plan/archive/`](../plan/archive/README.md), which is not a PLAN source. Nothing
is lost: every file moves verbatim by `git mv`, 26 of the 43 duplicate a fuller
committed diary, and the archive README indexes all 43 with the next action each
lane left behind, so the queue keeps its work items. Restoring a lane is a `git
mv` back plus `gen-plan.py`.

**Scoped the keystone's last axiom, by measurement** (`WIP`, ledger-integrity,
2026-08-16). Strand [`01`](01-int-real-keystone.md) K1.
`nat_axiom_inventory` confirms `integer` carries exactly **one** trusted
declaration, `Int.euclidean_decomposition`, whose type decodes to
`∀ a b, 0 < b → ∃ q r, a = b·q + r ∧ 0 ≤ r ∧ r < b`. Four measured facts make the
remaining work concrete:

- **It need not define `Int.div`/`Int.mod`.** The axiom is purely existential, so
  it is discharged by supplying witnesses; the predecessor lane's diary assumed
  definitions were required.
- **`Int` is a real inductive** (`ofNat n` / `negSucc n`), so `Int.rec` gives the
  sign case split. No named case-analysis theorem exists among the 52 `Int`
  theorems, which is why this looked blocked.
- **`Int.lt_dest`** turns the hypothesis `0 < b` into `∃ k, b = 0 + ofNat (succ k)`
  — a positive `ofNat`, which is what the ℕ side needs.
- **The ℕ side is already proved**: `Nat.div_mod_exists` (`1 ≤ k → ∃ q r,
  divMod k t q r`), with `div_mod_unique`, `div_mod_bounds` and `div_mod_exec`
  beside it, among 119 `Nat` theorems.

The real work is the negative branch, exactly as the predecessor flagged:
Euclidean rounding is not truncation. For `a = negSucc n` with `n+1 = k·q + r`,
the witnesses are `(-q, 0)` when `r = 0` and `(-q-1, k-r)` otherwise, and the
second needs `0 < k - r < k`.

**Read the construction, and the plan got smaller twice.** A first pass through
the 52 `Int` theorems found no `ofNat` homomorphisms — no `ofNat_add`,
`ofNat_mul`, `ofNat_lt` — and concluded a helper development was needed first.
Reading `defs.rs` instead of the inventory shows that is wrong: `Int.add` and
`Int.mul` are structural definitions that **compute on two `ofNat`
constructors**, which is why `Int.add_zero` is proved by `d.irefl(value)` and
nothing else. `Int.le`/`Int.lt` are likewise four-case definitions over
`Nat.le`/`Nat.lt`, and the module's own table states
`Int.le (ofNat m) (ofNat n) ≡ Nat.le m n`.

So the transfer lemmas are **definitional**, and the non-negative branch needs no
new lemmas at all:

- `Nat.divMod d n q r` is a *definition* unfolding to `(n = d·q + r) ∧ (r < d)`,
  so `And.left`/`And.right` apply to a `divMod` term directly.
- `t = ofNat n`: `Nat.div_mod_exists (succ m) n` gives `q, r`; the goal
  `ofNat n = ofNat (succ m) · ofNat q + ofNat r` reduces to
  `ofNat n = ofNat ((succ m)·q + r)`, closed by `nat_eq_to_int` on `And.left`.
  `0 ≤ ofNat r` reduces to `Nat.le zero r`, and `ofNat r < ofNat (succ m)` to
  `And.right`.

The remaining work is therefore **one branch**, `t = negSucc n`, plus the
`Int.lt_dest` preamble that turns `0 < k` into `k = ofNat (succ m)`. The
primitives are all present: `case_split` (already does `Int.rec` over
`Shape::OfNat`/`Shape::NegSucc`), `exists_elim`, `shift_intro`, `nat_eq_to_int`.

**Next for this lane.** Write that proof term — `Exists` here ranges over `Int`
rather than `Nat`, so the existing `shift_exists`/`exists_elim` helpers need
`Int`-typed siblings. Then discharge the axiom, taking `int_prelude` to **0
axioms**, and land it as a fact whose checker is bound to the theorem itself
rather than to a gate-wide run (see the caution in finding 8).

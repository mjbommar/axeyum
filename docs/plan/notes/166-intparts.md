# Notes: 166-intparts

Detail moved out of [`../status/166-intparts.md`](../status/166-intparts.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Was the witness bookkeeping (`BoundedOn`/`UniformlyContinuousOn` for
products) the predicted friction? Yes, exactly, and it was mechanical, not
conceptual.** `has_derivative_mul`'s call signature is `[F, F', G, G', a, b,
hf, hg, huc, k1, k2, k3, hbf, hbg, hbgp]` — confirmed by reading its actual
`Rust` construction (`declare_has_derivative_mul` in `derivative.rs`), not
assumed from the doc comment. `uniformly_continuous_mul`'s is `[F, G, a, b,
hucF, hucG, k1, k2, hbF, hbG]`. `bounded_of_uniformly_continuous`'s is `[F,
a, b, huc, hab]`. All three orders were extracted from existing call sites
elsewhere in the file (`declare_has_derivative_cube`,
`cos_fn_wide_uniformly_continuous`) before writing any new code, per
CLAUDE.md's "mirror an existing helper's construction" habit.

**What the kernel REJECTED, and why — the one real bug.** First attempt
failed at `add_declaration` with `UnboundFVar { id: 11464 }`, not at proof
construction. Cause: the TYPE was built using `d.arrow(hab_ty, t)`,
`d.arrow(huc_u_ty, t)`, `d.arrow(huc_up_ty, t)`, `d.arrow(huc_v_ty, t)`,
`d.arrow(huc_vp_ty, t)` for all seven hypotheses — but `hab`, `huc_u`,
`huc_up`, `huc_v`, `huc_vp` (five of the seven) are referenced **by value**
later in the conclusion itself (embedded in `i1`/`i2`/`uc_upv`/`uc_uvp`,
which are literally `integral`/`uniformly_continuous_mul` applications
carrying `hab`/`huc_*` as positional arguments). `d.arrow` builds a
non-dependent Pi and does **not** abstract the hypothesis's own fvar from
the body; `d.pi_fv` does. Using `arrow` for all seven left those five fvars
genuinely free in the declared type. `hu`/`hv` are correctly `arrow`ed —
their VALUES never appear in the conclusion, only inside the proof term —
matching `integral_eq_antideriv_diff`'s own `hg`/`hbnd` at the tail of its
own hypothesis list.

Diagnosis method: a temporary tree-walk (built and removed within this
session, in the same function) collected every `FVar` id reachable in the
fully-assembled `ty`/`value` before calling `add_declaration`, and diffed
against the 13 tracked binder ids. It found exactly the five `arrow`ed
value-carrying hypotheses and nothing else — pinpointing the fix in one
run rather than by guessing. General lesson for this file: **before
`d.arrow`ing a hypothesis, check whether its own fvar is referenced by
value anywhere later in the term being built — if so it needs `pi_fv`.**

**`hasDerivative_chain`'s actual hypotheses, and why substitution is
BLOCKED, not merely awkward.** Read directly from
`declare_has_derivative_chain` in `derivative.rs` (not from the doc
comment, which only states the surface form):

```
∀ F F' G G' a b,
  HasDerivativeOn F F' a b → HasDerivativeOn G G' a b →
  UniformlyContinuousOn F a b →
  (∀ z, le a z → le z b → le a (F z)) →   -- F self-maps INTO [a,b] (low)
  (∀ z, le a z → le z b → le (F z) b) →   -- F self-maps INTO [a,b] (high)
  ∀ k1 k2, BoundedOn F' a b k1 → BoundedOn G' a b k2 →
  HasDerivativeOn (fun r => G (F r)) (fun x => mul (G' (F x)) (F' x)) a b
```

Confirmed at the term level: `hg_ty = hd_ty(d, p, g, gp, a, b)` — the
**same** `a`, `b` as `f`'s own `HasDerivativeOn`, not a second pair of
endpoints for `G`. And `self_map_tys(d, p, f, a, b)` builds exactly the two
self-map hypotheses above. There is no alternate/generalized chain rule in
the tree — grepped `creal.rs` for every `chain`-named field: only
`has_derivative_chain` and its one concrete instantiation
`has_derivative_chain_id_sq` exist.

Substitution wants `∫_{g(a)}^{g(b)} F = ∫ₐᵇ (F∘g)·g'`. Building this via
FTC-II + this chain rule needs an antiderivative `H` of `F` with `H' = F`
proved on the **same** `[a,b]` that `g` is differentiated on (not on
`[g(a), g(b)]`, `g`'s actual range) — because `hasDerivative_chain`'s `G`
parameter shares `f`'s own `a`, `b` verbatim, with no independent pair for
`G`'s own domain. That forces `g` to be a **self-map** `[a,b] → [a,b]`
(the two extra hypotheses), and forces `F` to be uniformly continuous /
bounded / have a computable antiderivative over the whole `[a,b]`, not just
over `g`'s actual range `[g(a), g(b)] ⊆ [a,b]`. For a genuinely
range-changing substitution (e.g. `g(x) = 2x` on `[0,1]`, range `[0,2]` —
a proper superset of the domain), this chain rule cannot be invoked at all:
the self-map hypothesis `le (F z) b` fails outright at any `z` with
`F z > b`.

**This is a real obstruction, not a bookkeeping one**, and it is not fixed
by a restriction lemma either: even restricting `H`'s already-proved
derivative from a big interval down to `[g(a), g(b)]` would need a
`HasDerivativeOn`-restriction lemma (narrowing `[a,b]` to a sub-interval),
and no such lemma exists in this development (`HasDerivativeOn` is a
one-constructor inductive in `Type`, so it is not the free `BoundedOn`-style
restriction `creal/inventory/integral.rs`'s FTC-II reused for its own
degenerate-interval argument — that shortcut only worked there because
`BoundedOn` is a transparent `Definition`). The general substitution
theorem needs a chain rule shaped `HasDerivativeOn F F' a b →
HasDerivativeOn G G' c d → (∀ z, le a z → le z b → le c (F z)) → (∀ z, le a
z → le z b → le (F z) d) → HasDerivativeOn (G∘F) (...) a b`, with an
INDEPENDENT `[c,d]` for `G`, which does not exist and is a new
`has_derivative_chain`-shaped declaration in its own right, not a
composition of what is landed.

**Sizing for the next lane:** the general substitution theorem is a new
chain-rule variant (independent domain for the outer function), roughly the
same shape and size as `has_derivative_chain` itself (a two-level modulus
composition), plus the FTC-II composition this lane already worked out. Not
attempted here — this lane's budget went to integration by parts (landed)
and to confirming precisely why substitution needs new analysis rather than
composition (characterised above, verified against source, not doc
comments).

**Timings** (foreground, `env` with `RUST_MIN_STACK` unset, load not
isolated): `creal_prelude_builds` **100.82 s** — within the 89–117 s range
recorded by the two FTC lanes earlier the same day, no multiple, so none of
this file's documented concrete-witness/lazy-delta traps apply.
`every_creal_declaration_is_checked_and_axiom_free` (`--release`) **18.39
s**, green: the new declaration is in `kernel.environment()`, kind
`Theorem`, empty axiom footprint. `creal_tests::steps_table_matches_
recorded_extraction` and `existing_step_order_is_topologically_valid` both
green (the latter **92.13 s**). `cargo clippy -p axeyum-lean-kernel
--all-targets --all-features -D warnings` clean, both before and after the
fix.

**Wiring, all three places plus the inventory shard.** New
`CRealPrelude::integral_by_parts` field + name registration in `creal.rs`;
new `BuildStep` `"integral::declare_integral_by_parts"` placed immediately
after `"integral::declare_integral_eq_antideriv_diff"` in `STEPS` (its
latest dependency in file order — also needs `has_derivative_mul`,
`uniformly_continuous_mul`/`_add`, `bounded_of_uniformly_continuous`,
`integral_add`, all provided earlier); matching `EXPECTED_STEP_ORDER` entry
in `creal_tests.rs`; inventory entry in `creal/inventory/integral.rs`.

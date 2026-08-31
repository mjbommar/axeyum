//! The unit-permutation step Euler's totient theorem needs — and a precise
//! record of why the theorem itself does **not** land in this file.
//!
//! ## Step 0: not already present
//!
//! `prelude_theorem_inventory --include-constructed --release` lists 481
//! `integer`-prelude names as of this slice; nothing named `euler` or
//! `totient` beyond the already-landed `Int.euler_criterion_pm_one`
//! (`euler.rs`, quadratic residues — unrelated) and `Nat.totient_prime`
//! (`nat_prelude/totient.rs`). `Nat.totient`, `Int.prodRange`, and
//! `Nat.countRange` are *definitions* (invisible to a theorem inventory) and
//! were confirmed present from source. Euler's totient theorem itself,
//! `gcd a n = 1 → a^φ(n) ≡ 1 [n]`, is absent under any name, in either `ℕ`
//! or `ℤ`.
//!
//! ## What `wilson.rs` actually supplies, and what does not transfer
//!
//! `wilson.rs`'s own permutation step is **not** a subset-product
//! permutation — it is a fixed-point-free INVOLUTION COLLAPSE over the
//! FULL contiguous range `[0,n)` (`Int.prod_range_pairing_collapse`,
//! `σ := Nat.inverseIndex p`), which is sound for Wilson's theorem only
//! because every residue `1..p-1` is a unit when `p` is prime — there is no
//! subset to carve out. The more general tool named in that file's own
//! doc, `Int.prodRange_permute : ∀ f σ n, InjectiveOn σ n → MapsInto σ n →
//! prodRange f n = prodRange (f∘σ) n`, still requires `σ` to be a self-map
//! of the WHOLE `[0,n)` (`MapsInto σ n` is stated with the SAME bound `n` as
//! the domain — `prod.rs`'s own comment on `declare_prod_range_permute`).
//! Euler's argument needs a bijection of the *subset* `{k<n : gcd k n=1}`,
//! which is smaller than `[0,n)` for every composite `n`. Neither
//! `prodRange_permute` nor the pairing collapse accepts a predicate-scoped
//! domain, and this matches this session's diary
//! (`docs/mathematics-2026-08/diary-predicate-subset-product.md`): the
//! missing primitive is `prodRangeIf` (a product folded over a
//! Boolean-predicate subset of `[0,n)`, the multiplicative analogue of
//! `Nat.countRange`) plus a proof that a predicate-preserving bijection of
//! `[0,n)` leaves such a restricted product unchanged. That proof needs a
//! remove-one-element re-indexing induction this kernel does not yet have,
//! and building it is explicitly out of scope for this file (see "What does
//! NOT land here", below).
//!
//! What DOES transfer unchanged from `wilson.rs`/`gcd.rs`/`modinv.rs`, and is
//! reused here rather than rebuilt: [`super::wilson::emod_eq_self_of_in_range`]
//! and [`super::wilson::emod_modeq_self`] (both `pub(super)`), and the
//! already-proved `Int.modEq_cancel`, `Int.modEq_inverse_exists`,
//! `Int.ModEq.mul`/`.mul_right`/`.symm`/`.trans`, `Int.coprime_of_bezout_one`.
//!
//! ## What lands here: the unit-permutation lemma (Step 2 of the task brief)
//!
//! For `a` coprime to `n`, multiplication by `a` mod `n` permutes the
//! residues coprime to `n` — proved here as its two halves, over `ℤ`
//! (matching `wilson.rs`'s own carrier, not `ℕ`'s `Nat.mod_eq_cancel`,
//! because the `MapsInto` half needs `Int.modEq_inverse_exists`'s
//! Bézout-through-subtraction route; the balanced, subtraction-free `ℕ`
//! Bézout shape `nat_prelude/euler.rs` uses makes the analogous
//! coprimality-composition argument considerably more awkward):
//!
//! - [`declare_euler_unit_coprime`] — `Int.euler_unit_coprime : ∀ n a k,
//!   0 < n → Coprime a n → Coprime k n → Coprime (emod (a*k) n) n` — `MapsInto`.
//!   Proof: `Coprime a n`/`Coprime k n` each give a modular inverse
//!   (`Int.modEq_inverse_exists`); their product is `a*k`'s inverse after a
//!   pure ring regroup (`mul_swap_inner`, copied unchanged from
//!   `prod.rs`'s private helper of the same name — not `pub(super)` there),
//!   which [`coprime_of_modeq_inverse`] (a local copy of the inline
//!   Bézout-extraction `modinv.rs`'s `declare_modeq_inverse_unique` already
//!   does, generalized off that theorem's own `a`,`b` names) turns into
//!   `Coprime (a*k) n`. A second application of the same two lemmas —
//!   `emod_modeq_self` supplies `ModEq n (a*k) (emod (a*k) n)`, multiplied
//!   through the `a*k`-inverse and re-closed by
//!   [`coprime_of_modeq_inverse`] — reduces that to the canonical
//!   representative `emod (a*k) n`. No case split anywhere; the reduction to
//!   `Coprime (emod (a*k) n) n` is unconditional given `0 < n`.
//! - [`declare_euler_unit_injective`] — `Int.euler_unit_injective : ∀ n a i
//!   j, 0 < n → Coprime a n → 0 ≤ i → i < n → 0 ≤ j → j < n →
//!   emod (a*i) n = emod (a*j) n → i = j` — injectivity on `[0,n)` (not yet
//!   restricted to the coprime subset; the hypothesis is the SAME-residue
//!   premise, not coprimality of `i`/`j`, so this is actually injectivity on
//!   ALL of `[0,n)`, of which restriction to the coprime subset is a free
//!   corollary). Proof: the hypothesis IS `ModEq n (a*i) (a*j)` by
//!   `Int.ModEq`'s own definition (`ModEq n x y := emod x n = emod y n`, a
//!   `Regular`-reducibility `Definition`, so the raw `Eq Int` term
//!   type-checks directly against a `ModEq` parameter — the same reliance on
//!   kernel-level unfolding `emod_modeq_self`'s own doc spells out);
//!   `Int.modEq_cancel` cancels `a` to `ModEq n i j`, and
//!   `emod_eq_self_of_in_range` applied to `i` and to `j` (using the bound
//!   hypotheses) closes `i = emod i n = emod j n = j` by a three-step
//!   `ichain`.
//!
//! Combined, these two give: multiplication-by-`a` (`a` coprime to `n`) maps
//! the coprime-residue subset of `[0,n)` into itself and is injective on all
//! of `[0,n)`, hence injective on the subset — which is exactly "permutes
//! the subset" MODULO the subset actually being finite and the map landing
//! back inside it with equal cardinality forcing surjectivity. That last
//! step (injective self-map of a *subset* ⟹ surjective onto that same
//! subset) is `Nat.injective_on_imp_surjective_on`'s pigeonhole
//! (`nat_prelude/finite.rs`) generalized off a full-range self-map to an
//! arbitrary predicate-scoped one — the same missing primitive as the
//! product side, not a new gap. See "What does NOT land here" below.
//!
//! ## What does NOT land here
//!
//! `Int.euler_totient_theorem` itself. Two independent things are missing,
//! both flagged by this session's diary before this file was written and
//! confirmed, not merely assumed, while building the above:
//!
//! 1. **The subset pigeonhole.** `Nat.injective_on_imp_surjective_on`
//!    (`finite.rs`) only accepts `InjectiveOn`/`MapsInto` self-maps of the
//!    FULL `[0,n)` — `restrict_pair.rs` restricts to a fixed two-element
//!    complement, `permutation.rs` inverts bijections already known on all
//!    of `[0,n)`, and neither covers an arbitrary predicate-carved subset.
//!    Bijectivity of multiplication-by-`a` on `{k<n : gcd k n=1}` therefore
//!    is NOT yet a corollary of the two lemmas this file adds; it needs that
//!    generalized pigeonhole (a genuinely new, separate induction: remove
//!    one predicate-satisfying element, recurse) as its own slice.
//! 2. **The subset product.** Even granting bijectivity, forming
//!    `∏_{gcd k n=1} k ≡ ∏_{gcd k n=1} (a·k mod n) [n] = a^{φ(n)} ·
//!    ∏_{gcd k n=1} k [n]` needs `Int.prodRangeIf` (a product folded over a
//!    Boolean-predicate subset, mirroring `Nat.countRange`) plus invariance
//!    of that restricted product under a predicate-preserving bijection of
//!    `[0,n)`. Neither exists; `Int.prodRange`/`Int.prodRange_permute` are
//!    unconditionally over the FULL range (see above). This is the same
//!    primitive the diary names as blocking uniqueness of prime
//!    factorization, general-`n` CRT, and permutations-as-group-elements —
//!    not a gap specific to this theorem.
//!
//! Building either is a separate, larger slice (the diary's own estimate,
//! matching this file's experience actually trying): each needs a genuinely
//! new induction (remove-one-element re-indexing) this kernel has not built
//! anywhere yet, not a repackaging of `wilson.rs`'s full-range machinery.
//! This file lands the one piece Wilson's own route DOES supply unchanged —
//! cancellation via `Int.modEq_cancel`/`Int.modEq_inverse_exists` — and
//! stops precisely where that route runs out.

use super::dvd::{dvd_predicate, idvd};
use super::modeq::imodeq;
use super::ops::IntDev;
use super::wilson::{emod_eq_self_of_in_range, emod_modeq_self};
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

// ============================================================================
// Local plumbing, copied per this development's own convention (per-file
// local copies rather than a shared private module — see `nat_prelude/euler.rs`
// and `int_prelude/modinv.rs`'s own doc comments on the same choice).
// ============================================================================

/// Eliminate `witness : Int.dvd a b` into `target`, given
/// `minor : ∀ (c : Int), Eq Int b (a*c) → target`. Copied from
/// `modinv.rs`'s private `idvd_elim` (not `pub(super)` there).
fn idvd_elim(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    target: ExprId,
    witness: ExprId,
    minor: ExprId,
) -> ExprId {
    let pred = dvd_predicate(d, a, b);
    let int_ty = d.int_ty();
    let one = d.level_one();
    let anon = d.anon_name();
    let exists_ty = {
        let name = d.int().logic.exists_;
        let e = d.kernel().const_(name, vec![one]);
        d.apply(e, &[int_ty, pred])
    };
    let motive = d.kernel().lam(anon, exists_ty, target, BinderInfo::Default);
    let rec_name = d.int().logic.exists_rec;
    let rec = d.kernel().const_(rec_name, vec![one]);
    d.apply(rec, &[int_ty, pred, motive, minor, witness])
}

/// Eliminate `witness : Exists.{1} Int predicate` into `target`, given
/// `minor : ∀ (x : Int), predicate x → target`. Copied from `euler.rs`'s
/// private `int_exists_elim` (not `pub(super)` there — that file is about
/// quadratic residues, unrelated to this one).
fn int_exists_elim(
    d: &mut IntDev<'_>,
    predicate: ExprId,
    target: ExprId,
    witness: ExprId,
    minor: ExprId,
) -> ExprId {
    let int_ty = d.int_ty();
    let one = d.level_one();
    let anon = d.anon_name();
    let exists_ty = {
        let name = d.int().logic.exists_;
        let e = d.kernel().const_(name, vec![one]);
        d.apply(e, &[int_ty, predicate])
    };
    let motive = d.kernel().lam(anon, exists_ty, target, BinderInfo::Default);
    let rec_name = d.int().logic.exists_rec;
    let rec = d.kernel().const_(rec_name, vec![one]);
    d.apply(rec, &[int_ty, predicate, motive, minor, witness])
}

/// Proves `Eq Int (mul (mul a b) (mul x y)) (mul (mul a x) (mul b y))`.
/// Copied verbatim from `prod.rs`'s private `mul_swap_inner` (not
/// `pub(super)` there): five steps, all `mul_assoc`/`mul_comm`,
/// `(a*b)*(x*y) = a*(b*(x*y)) = a*((b*x)*y) = a*((x*b)*y) = a*(x*(b*y)) =
/// (a*x)*(b*y)`.
fn mul_swap_inner(d: &mut IntDev<'_>, a: ExprId, b: ExprId, x: ExprId, y: ExprId) -> ExprId {
    let p = d.int();
    let ab = d.imul(a, b);
    let xy = d.imul(x, y);
    let start = d.imul(ab, xy);

    let bxy = d.imul(b, xy);
    let t1 = d.imul(a, bxy);
    let p1 = d.const_app(p.mul_assoc, &[a, b, xy]);

    let bx = d.imul(b, x);
    let bx_y = d.imul(bx, y);
    let t2 = d.imul(a, bx_y);
    let assoc_bxy = d.const_app(p.mul_assoc, &[b, x, y]);
    let assoc_bxy_rev = d.isymm(bx_y, bxy, assoc_bxy);
    let p2 = d.icongr(bxy, bx_y, assoc_bxy_rev, &|d, t| d.imul(a, t));

    let xb = d.imul(x, b);
    let xb_y = d.imul(xb, y);
    let t3 = d.imul(a, xb_y);
    let comm_bx = d.const_app(p.mul_comm, &[b, x]);
    let p3 = d.icongr(bx, xb, comm_bx, &|d, t| {
        let ty_ = d.imul(t, y);
        d.imul(a, ty_)
    });

    let by = d.imul(b, y);
    let x_by = d.imul(x, by);
    let t4 = d.imul(a, x_by);
    let assoc_xby = d.const_app(p.mul_assoc, &[x, b, y]);
    let p4 = d.icongr(xb_y, x_by, assoc_xby, &|d, t| d.imul(a, t));

    let ax = d.imul(a, x);
    let end_ = d.imul(ax, by);
    let assoc_axby = d.const_app(p.mul_assoc, &[a, x, by]);
    let assoc_axby_rev = d.isymm(end_, t4, assoc_axby);

    let (_e, proof) = d.ichain(
        start,
        &[
            (t1, p1),
            (t2, p2),
            (t3, p3),
            (t4, p4),
            (end_, assoc_axby_rev),
        ],
    );
    proof
}

/// From `h1 : ModEq n (x*y) one`, derive `Coprime x n`. Copied and
/// generalized from the inline Bézout-extraction block inside
/// `modinv.rs::declare_modeq_inverse_unique` (that block is not itself a
/// named, reusable function there — it derives `Coprime a n` from `h1`
/// as one step of a larger proof; this is the same derivation, extracted,
/// with `a`,`b` renamed `x`,`y` to avoid confusion with this file's own
/// `a` (the multiplier)).
///
/// `pub(super)`, not private: [`super::euler_unit_preserve`] reuses it
/// unchanged for the converse half of `Int.euler_unit_coprime_iff` (item 2
/// of `euler_theorem.rs`'s "what does NOT land here" list) — a second
/// application of the same Bézout-extraction, at `a`'s own modular inverse
/// rather than at `a` itself.
pub(super) fn coprime_of_modeq_inverse(
    d: &mut IntDev<'_>,
    n: ExprId,
    x: ExprId,
    y: ExprId,
    h_pos: ExprId,
    h1: ExprId,
) -> ExprId {
    let p = d.int();
    let one_i = d.ione();
    let xy = d.imul(x, y);
    let neg_xy = d.ineg(xy);
    let diff = d.iadd(one_i, neg_xy); // one + (-(x*y)) ~ one - x*y

    let modeq_xy1 = imodeq(d, n, xy, one_i);
    let dvd_ty = idvd(d, n, diff);
    let iff_ty = d.const_app(p.mod_eq_iff_dvd, &[n, xy, one_i, h_pos]);
    let mp = d.const_app(p.logic.iff_mp, &[modeq_xy1, dvd_ty, iff_ty]);
    let dvd_diff = d.apply(mp, &[h1]);

    let int_ty = d.int_ty();
    let minor = {
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let nw = d.imul(n, w);
        let eq_fv = d.fresh_fvar();
        let eq_h = d.kernel().fvar(eq_fv);
        let eq_ty = d.ieq(diff, nw);

        let step_congr = d.icongr(diff, nw, eq_h, &|d, t| d.iadd(t, xy));
        let diff_xy = d.iadd(diff, xy);
        let nw_xy = d.iadd(nw, xy);

        let neg_xy_xy = d.iadd(neg_xy, xy);
        let xy_neg_xy = d.iadd(xy, neg_xy);
        let zero2 = d.izero();
        let comm1 = d.const_app(p.add_comm, &[neg_xy, xy]);
        let negcancel = d.const_app(p.add_neg, &[xy]);
        let (_, negxy_xy_eq_zero) = d.ichain(neg_xy_xy, &[(xy_neg_xy, comm1), (zero2, negcancel)]);

        let assoc = d.const_app(p.add_assoc, &[one_i, neg_xy, xy]);
        let one_plus_negxy_xy = d.iadd(one_i, neg_xy_xy);
        let congr_zero = d.icongr(neg_xy_xy, zero2, negxy_xy_eq_zero, &|d, t| d.iadd(one_i, t));
        let one_plus_zero = d.iadd(one_i, zero2);
        let addzero = d.const_app(p.add_zero, &[one_i]);
        let (_, diff_xy_eq_one) = d.ichain(
            diff_xy,
            &[
                (one_plus_negxy_xy, assoc),
                (one_plus_zero, congr_zero),
                (one_i, addzero),
            ],
        );

        let step_congr_rev = d.isymm(diff_xy, nw_xy, step_congr);
        let nw_xy_eq_one = d.itrans(nw_xy, diff_xy, one_i, step_congr_rev, diff_xy_eq_one);

        let xy_nw = d.iadd(xy, nw);
        let comm_final = d.const_app(p.add_comm, &[xy, nw]);
        let xy_nw_eq_one = d.itrans(xy_nw, nw_xy, one_i, comm_final, nw_xy_eq_one);

        let coprime_xn = d.const_app(p.coprime_of_bezout_one, &[x, n, y, w, xy_nw_eq_one]);

        let with_eq = d.lam_fv(eq_fv, eq_ty, coprime_xn);
        d.lam_fv(w_fv, int_ty, with_eq)
    };

    let coprime_ty = d.const_app(p.coprime, &[x, n]);
    idvd_elim(d, n, diff, coprime_ty, dvd_diff, minor)
}

// ============================================================================
// `Int.euler_unit_coprime` — MapsInto.
// ============================================================================

/// Declare `Int.euler_unit_coprime : ∀ n a k, 0 < n → Coprime a n →
/// Coprime k n → Coprime (emod (a*k) n) n`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_euler_unit_coprime(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.euler_unit_coprime, 3, &|d, v| {
        let (n, a, k) = (v[0], v[1], v[2]);
        let p = d.int();
        let zero = d.izero();
        let pos_ty = d.ilt(zero, n);
        let cop_a_ty = d.const_app(p.coprime, &[a, n]);
        let cop_k_ty = d.const_app(p.coprime, &[k, n]);
        let ak = d.imul(a, k);
        let r = d.iemod(ak, n);
        let goal = d.const_app(p.coprime, &[r, n]);

        let stmt = {
            let inner = d.arrow(cop_k_ty, goal);
            let with_cop_a = d.arrow(cop_a_ty, inner);
            d.arrow(pos_ty, with_cop_a)
        };

        let h_pos_fv = d.fresh_fvar();
        let h_pos = d.kernel().fvar(h_pos_fv);
        let h_cop_a_fv = d.fresh_fvar();
        let h_cop_a = d.kernel().fvar(h_cop_a_fv);
        let h_cop_k_fv = d.fresh_fvar();
        let h_cop_k = d.kernel().fvar(h_cop_k_fv);

        let int_ty = d.int_ty();
        let one_i = d.ione();

        let ex_b = d.lemma(p.mod_eq_inverse_exists, &[n, a, h_pos, h_cop_a]);
        let ex_c = d.lemma(p.mod_eq_inverse_exists, &[n, k, h_pos, h_cop_k]);

        // Outer elim: b, hb : ModEq n (a*b) one.
        let outer_pred = {
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let ab = d.imul(a, b);
            let body = imodeq(d, n, ab, one_i);
            d.lam_fv(b_fv, int_ty, body)
        };
        let outer_minor = {
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let ab = d.imul(a, b);
            let hb_ty = imodeq(d, n, ab, one_i);
            let hb_fv = d.fresh_fvar();
            let hb = d.kernel().fvar(hb_fv);

            // Inner elim: c, hc : ModEq n (k*c) one.
            let inner_pred = {
                let c_fv = d.fresh_fvar();
                let c = d.kernel().fvar(c_fv);
                let kc = d.imul(k, c);
                let body = imodeq(d, n, kc, one_i);
                d.lam_fv(c_fv, int_ty, body)
            };
            let inner_minor = {
                let c_fv = d.fresh_fvar();
                let c = d.kernel().fvar(c_fv);
                let kc = d.imul(k, c);
                let hc_ty = imodeq(d, n, kc, one_i);
                let hc_fv = d.fresh_fvar();
                let hc = d.kernel().fvar(hc_fv);

                // ModEq n ((a*b)*(k*c)) (one*one).
                let ab = d.imul(a, b);
                let hbc = d.lemma(p.mod_eq_mul, &[n, ab, one_i, kc, one_i, h_pos, hb, hc]);

                // Rewrite the LHS: (a*b)*(k*c) = (a*k)*(b*c).
                let ab_kc = d.imul(ab, kc);
                let bc = d.imul(b, c);
                let ak = d.imul(a, k);
                let ak_bc = d.imul(ak, bc);
                let ring_eq = mul_swap_inner(d, a, b, k, c);
                let oo = d.imul(one_i, one_i);
                let hbc_lhs =
                    d.int_eq_rewrite(ab_kc, ak_bc, ring_eq, hbc, &|d, t| imodeq(d, n, t, oo));

                // Rewrite the RHS: one*one = one.
                let mul_one_pf = d.const_app(p.mul_one, &[one_i]);
                let h_final = d.int_eq_rewrite(oo, one_i, mul_one_pf, hbc_lhs, &|d, t| {
                    imodeq(d, n, ak_bc, t)
                });

                // Coprime (a*k) n.
                let cop_ak = coprime_of_modeq_inverse(d, n, ak, bc, h_pos, h_final);

                // Reduce to the canonical representative: Coprime (emod (a*k) n) n.
                let ex_d = d.lemma(p.mod_eq_inverse_exists, &[n, ak, h_pos, cop_ak]);
                let r_local = d.iemod(ak, n);
                let goal_local = d.const_app(p.coprime, &[r_local, n]);

                let d_pred = {
                    let dp_fv = d.fresh_fvar();
                    let dp = d.kernel().fvar(dp_fv);
                    let ak_dp = d.imul(ak, dp);
                    let body = imodeq(d, n, ak_dp, one_i);
                    d.lam_fv(dp_fv, int_ty, body)
                };
                let d_minor = {
                    let dp_fv = d.fresh_fvar();
                    let dp = d.kernel().fvar(dp_fv);
                    let ak_dp = d.imul(ak, dp);
                    let hd_ty = imodeq(d, n, ak_dp, one_i);
                    let hd_fv = d.fresh_fvar();
                    let hd = d.kernel().fvar(hd_fv);

                    let em = emod_modeq_self(d, ak, n, h_pos); // ModEq n ak r_local
                    let em_symm = d.lemma(p.mod_eq_symm, &[n, ak, r_local, em]); // ModEq n r_local ak
                    let r_dp = d.imul(r_local, dp);
                    let step_mul =
                        d.lemma(p.mod_eq_mul_right, &[n, r_local, ak, dp, h_pos, em_symm]); // ModEq n (r_local*dp) (ak*dp)
                    let h_r = d.lemma(p.mod_eq_trans, &[n, r_dp, ak_dp, one_i, step_mul, hd]);

                    let cop_r = coprime_of_modeq_inverse(d, n, r_local, dp, h_pos, h_r);
                    let with_hd = d.lam_fv(hd_fv, hd_ty, cop_r);
                    d.lam_fv(dp_fv, int_ty, with_hd)
                };
                let body = int_exists_elim(d, d_pred, goal_local, ex_d, d_minor);
                let with_hc = d.lam_fv(hc_fv, hc_ty, body);
                d.lam_fv(c_fv, int_ty, with_hc)
            };
            let inner_elim = int_exists_elim(d, inner_pred, goal, ex_c, inner_minor);
            let with_hb = d.lam_fv(hb_fv, hb_ty, inner_elim);
            d.lam_fv(b_fv, int_ty, with_hb)
        };
        let outer_elim = int_exists_elim(d, outer_pred, goal, ex_b, outer_minor);

        let with_hck = d.lam_fv(h_cop_k_fv, cop_k_ty, outer_elim);
        let with_hca = d.lam_fv(h_cop_a_fv, cop_a_ty, with_hck);
        let proof = d.lam_fv(h_pos_fv, pos_ty, with_hca);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Int.euler_unit_injective`.
// ============================================================================

/// Declare `Int.euler_unit_injective : ∀ n a i j, 0 < n → Coprime a n →
/// 0 ≤ i → i < n → 0 ≤ j → j < n → Eq Int (emod (a*i) n) (emod (a*j) n) →
/// Eq Int i j`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_euler_unit_injective(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.euler_unit_injective, 4, &|d, v| {
        let (n, a, i, j) = (v[0], v[1], v[2], v[3]);
        let p = d.int();
        let zero = d.izero();
        let pos_ty = d.ilt(zero, n);
        let cop_a_ty = d.const_app(p.coprime, &[a, n]);
        let i0_ty = d.ile(zero, i);
        let ilt_ty = d.ilt(i, n);
        let j0_ty = d.ile(zero, j);
        let jlt_ty = d.ilt(j, n);
        let ai = d.imul(a, i);
        let aj = d.imul(a, j);
        let emod_ai = d.iemod(ai, n);
        let emod_aj = d.iemod(aj, n);
        let heq_ty = d.ieq(emod_ai, emod_aj);
        let goal = d.ieq(i, j);

        let stmt = {
            let inner = d.arrow(heq_ty, goal);
            let with_jlt = d.arrow(jlt_ty, inner);
            let with_j0 = d.arrow(j0_ty, with_jlt);
            let with_ilt = d.arrow(ilt_ty, with_j0);
            let with_i0 = d.arrow(i0_ty, with_ilt);
            let with_cop = d.arrow(cop_a_ty, with_i0);
            d.arrow(pos_ty, with_cop)
        };

        let h_pos_fv = d.fresh_fvar();
        let h_pos = d.kernel().fvar(h_pos_fv);
        let h_cop_fv = d.fresh_fvar();
        let h_cop = d.kernel().fvar(h_cop_fv);
        let h_i0_fv = d.fresh_fvar();
        let h_i0 = d.kernel().fvar(h_i0_fv);
        let h_ilt_fv = d.fresh_fvar();
        let h_ilt = d.kernel().fvar(h_ilt_fv);
        let h_j0_fv = d.fresh_fvar();
        let h_j0 = d.kernel().fvar(h_j0_fv);
        let h_jlt_fv = d.fresh_fvar();
        let h_jlt = d.kernel().fvar(h_jlt_fv);
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);

        // `heq : Eq Int (emod (a*i) n) (emod (a*j) n)` IS `ModEq n (a*i) (a*j)`
        // by `Int.ModEq`'s own (Regular-reducibility) definition — passed
        // directly, the same reliance on kernel-level unfolding
        // `emod_modeq_self`'s own doc comment spells out.
        let modeq_ij = d.lemma(p.mod_eq_cancel, &[n, a, i, j, h_pos, h_cop, heq]);
        // modeq_ij : Eq Int (emod i n) (emod j n) (again by unfolding).

        let emod_i = d.iemod(i, n);
        let emod_j = d.iemod(j, n);
        let ei_eq_i = emod_eq_self_of_in_range(d, i, n, h_pos, h_i0, h_ilt); // Eq (emod i n) i
        let ej_eq_j = emod_eq_self_of_in_range(d, j, n, h_pos, h_j0, h_jlt); // Eq (emod j n) j
        let step1 = d.isymm(emod_i, i, ei_eq_i); // Eq i (emod i n)

        let (_, final_eq) = d.ichain(i, &[(emod_i, step1), (emod_j, modeq_ij), (j, ej_eq_j)]);

        let with_heq = d.lam_fv(heq_fv, heq_ty, final_eq);
        let with_jlt = d.lam_fv(h_jlt_fv, jlt_ty, with_heq);
        let with_j0 = d.lam_fv(h_j0_fv, j0_ty, with_jlt);
        let with_ilt = d.lam_fv(h_ilt_fv, ilt_ty, with_j0);
        let with_i0 = d.lam_fv(h_i0_fv, i0_ty, with_ilt);
        let with_cop = d.lam_fv(h_cop_fv, cop_a_ty, with_i0);
        let proof = d.lam_fv(h_pos_fv, pos_ty, with_cop);
        (stmt, proof)
    })?;
    Ok(())
}

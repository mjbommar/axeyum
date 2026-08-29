//! `Nat.Pair` — the first product type this prelude has — and `Nat.binaryRec`,
//! bit-halving recursion over `Nat`.
//!
//! # Why this file exists
//!
//! `docs/plan/status/250-nat-fastfib-minfac.md` sized `Nat.fastFib` (Mathlib's
//! log-time Fibonacci) and found it blocked on two pieces of infrastructure
//! that did not exist here, either of which alone stops the construction:
//!
//! 1. **No product type.** `fibonacci.rs`'s module doc records the same gap
//!    ("this kernel has no tuple type"), and a sibling lane could not reify a
//!    2x2 adjugate for the same reason. The prelude's standing workaround is a
//!    `Bool`-SELECTED function (`Nat.xgcdAux … (sel : Bool)`,
//!    `int_prelude/bezout_witnesses.rs`; `Nat.divModState`, `division.rs`;
//!    `creal/ivt.rs`'s `Bool -> CReal` bracket carrier), which keeps ONE
//!    recursion at the cost of evaluating the step twice per component.
//! 2. **No bit-halving recursion.** Every fuel-recursive definition here
//!    (`landAux`, `lorAux`, `ldiffAux`, `bitwiseAux`, `logAux`, `sqrtAux`,
//!    `clogAux`, `powSqAux`, `minFacAux`, `testBitAux`) recurses structurally
//!    on a UNARY counter; none exposes the recursion principle itself.
//!
//! Both are built here.
//!
//! # `Nat.Pair`
//!
//! A monomorphic, one-constructor, zero-parameter inductive
//! `Nat.Pair.mk : Nat -> Nat -> Nat.Pair`, with `fst`/`snd` projected through
//! the kernel-generated `Nat.Pair.rec` exactly as `Nat.Fin`'s `val`/`isLt` are
//! (`finite.rs`) and as `CReal`'s `seq`/`regular` are (`creal.rs`). Not a
//! parametric `Prod alpha beta`: the kernel's `add_inductive` handles that
//! shape (`inductive/inductive_tests.rs::prod_two_params_one_ctor` admits one
//! and checks its recursor's iota rule), but a general `Prod` belongs in the
//! LOGIC prelude, shared by every carrier, and that is a wider change than the
//! `Nat`-local need this file serves. `Nat.Pair` is the `Nat x Nat` this
//! prelude actually wants; promoting it is a separate decision.
//!
//! `eta` (`mk (fst p) (snd p) = p`) and `ext` (equal components give equal
//! pairs) are what make it usable in a proof rather than only in a
//! computation, and both come straight off the recursor.
//!
//! # `Nat.binaryRec`
//!
//! ```text
//! binaryRecAux alpha z f 0        n          == z
//! binaryRecAux alpha z f (succ k) 0          == z
//! binaryRecAux alpha z f (succ k) (succ m)   ==
//!     f (beq ((succ m) % 2) 1) ((succ m) / 2)
//!       (binaryRecAux alpha z f k ((succ m) / 2))
//! binaryRec alpha z f n := binaryRecAux alpha z f n n
//! ```
//!
//! All three `Aux` equations hold **definitionally** (beta/delta/iota); they
//! are declared as `refl` theorems so consumers can rewrite with them.
//!
//! The device is the one `binary.rs`'s `testBitAux` established and its module
//! doc explains: the recursion that is WANTED is on `n / 2`, which is not
//! structurally smaller by one constructor, so instead recurse structurally on
//! a FUEL counter carrying `n` through as an ordinary parameter that is
//! replaced by `n / 2` in the function VALUE at each step. The motive of the
//! outer `Nat.rec` is `fun _ => Nat -> alpha`, so this is large elimination
//! into `Type 0`, not a `Prop` induction.
//!
//! Two design points are load-bearing.
//!
//! *The `n = 0` guard is not optional.* Without it, fuel `succ k` at `n = 0`
//! would apply `f` at `bit false 0 = 0` and the value would depend on how much
//! fuel was left — [`declare_binary_rec_aux_agree_of_fuel`] would be FALSE, and
//! with it every equation that reaches for a non-canonical fuel.
//!
//! *`alpha` is an explicit `Type 0` argument, not a universe parameter, and the
//! motive is CONSTANT in `n`.* Mathlib's `binaryRec` is dependent
//! (`{motive : Nat -> Sort u}`); a fuel encoding cannot be, because the
//! fuel-exhaustion row has to return a value for an ARBITRARY `n` and only
//! `motive 0` is in hand. That is one of the two reasons this is a different
//! construction from Mathlib's — see "Is this Mathlib's `binaryRec`?" below.
//!
//! # Is this Mathlib's `binaryRec`? No.
//!
//! Read at the pinned commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`,
//! `Mathlib/Data/Nat/BinaryRec.lean:88`:
//!
//! ```text
//! def binaryRec {motive : Nat -> Sort u} (zero : motive 0)
//!     (bit : forall b n, motive n -> motive (bit b n)) (n : Nat) : motive n :=
//!   if n0 : n = 0 then congrArg motive n0 |> zero
//!   else
//!     let x := bit (1 &&& n != 0) (n >>> 1) (binaryRec zero bit (n >>> 1))
//!     congrArg motive n.bit_testBit_zero_shiftRight_one |> x
//! termination_by if n = 0 then 0 else n.log2.succ
//! decreasing_by ...
//! ```
//!
//! That is **well-founded recursion** on a `log2`-based measure, compiled to
//! `WellFounded.fix`, with a dependent motive in an arbitrary `Sort u`. This
//! one is **structural recursion on a fuel counter**, non-dependent, with an
//! extra fuel argument whose canonical instantiation needs a separately-proved
//! fuel-irrelevance theorem before the recursive equation even holds. Same
//! values at every argument; different `def`.
//!
//! By CLAUDE.md's mirror-flip criterion that is the `Nat.multichoose` /
//! `Nat.minFac` case, not the `Nat.descFactorial_of_lt` case: a theorem stated
//! ABOUT this definition is a different proposition from the `ml430` mirror of
//! the theorem stated about Mathlib's. Anything built on top of it — a
//! `fastFib`, in particular — therefore lands as a NEW local fact and leaves
//! `F:ml430-nat-fastfib-eq-cde11774` open. See
//! `docs/plan/status/255-nat-binaryrec.md`.
//!
//! # The arithmetic, and where it was already hiding
//!
//! [`NatPrelude::half_le_of_succ_le_succ`] (`succ m <= succ k` gives
//! `(succ m) / 2 <= k`) is the fuel-sufficiency step every halving family in
//! this prelude needs. It existed as an unnamed private copy in `log.rs`,
//! `binary.rs`, `powsq.rs`, and `rec_agreement.rs` — whose own
//! `half_le_predecessor_of_succ` doc calls itself "the fourth site with this
//! exact arithmetic … always duplicated because each fuel family's `…Aux` type
//! differs and there is nothing generic to promote it to". The arithmetic never
//! depended on any `…Aux` type; only the wrapper did. It is a named declaration
//! here, together with its own ingredient
//! [`NatPrelude::lt_two_mul_of_pos`] (`0 < n` gives `n < 2 * n`), which was
//! duplicated at the same sites.

use super::NatPrelude;
use super::helpers::iff_forward;
use super::ops::{NatDev, NatOps, agree_by_fuel_induction, cases_zero_succ};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

// --- generic-carrier `Eq` combinators ---------------------------------------
//
// `NatOps`' `eq`/`refl`/`symm`/`trans`/`congr`/`transport` are all hard-wired
// to `Nat`. Everything below is stated at an arbitrary `alpha : Type 0`, which
// lives at the same universe level as `Nat` (`Sort 1`), so these are the same
// constructions with the carrier passed in.

/// `Eq.{1} ty x y`.
fn eq_at(d: &mut NatDev<'_>, ty: ExprId, x: ExprId, y: ExprId) -> ExprId {
    let one = d.level_one();
    let name = d.prelude().logic.eq;
    let eq = d.kernel().const_(name, vec![one]);
    d.apply(eq, &[ty, x, y])
}

/// `Eq.refl.{1} ty a`.
fn refl_at(d: &mut NatDev<'_>, ty: ExprId, a: ExprId) -> ExprId {
    let one = d.level_one();
    let name = d.prelude().logic.eq_refl;
    let refl = d.kernel().const_(name, vec![one]);
    d.apply(refl, &[ty, a])
}

/// `Eq.rec.{0,1}` at carrier `ty`: transport `refl_case : motive p rfl` along
/// `h : Eq ty p q`.
fn transport_at(
    d: &mut NatDev<'_>,
    ty: ExprId,
    p: ExprId,
    motive: ExprId,
    refl_case: ExprId,
    q: ExprId,
    h: ExprId,
) -> ExprId {
    let z = d.kernel().level_zero();
    let one = d.level_one();
    let name = d.prelude().logic.eq_rec;
    let rec = d.kernel().const_(name, vec![z, one]);
    d.apply(rec, &[ty, p, motive, refl_case, q, h])
}

/// `fun (x : ty) (_ : Eq ty a x) => body(x)`.
fn eq_motive_at(
    d: &mut NatDev<'_>,
    ty: ExprId,
    a: ExprId,
    body: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let concl = body(d, x);
    let hyp = eq_at(d, ty, a, x);
    let anon = d.anon_name();
    let inner = d.kernel().lam(anon, hyp, concl, BinderInfo::Default);
    d.lam_fv(x_fv, ty, inner)
}

/// `h : Eq ty a b` gives `Eq ty b a`.
fn symm_at(d: &mut NatDev<'_>, ty: ExprId, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let motive = eq_motive_at(d, ty, a, &|d, x| eq_at(d, ty, x, a));
    let refl_case = refl_at(d, ty, a);
    transport_at(d, ty, a, motive, refl_case, b, h)
}

/// `h1 : Eq ty a b`, `h2 : Eq ty b c` give `Eq ty a c`.
fn trans_at(
    d: &mut NatDev<'_>,
    ty: ExprId,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> ExprId {
    let motive = eq_motive_at(d, ty, b, &|d, x| eq_at(d, ty, a, x));
    transport_at(d, ty, b, motive, h1, c, h2)
}

/// Congruence at carrier `ty` in a one-hole context landing in `ty`:
/// `h : Eq ty a b` gives `Eq ty (g a) (g b)`.
fn congr_at(
    d: &mut NatDev<'_>,
    ty: ExprId,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    g: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let ga = g(d, a);
    let motive = eq_motive_at(d, ty, a, &|d, x| {
        let gx = g(d, x);
        eq_at(d, ty, ga, gx)
    });
    let refl_case = refl_at(d, ty, ga);
    transport_at(d, ty, a, motive, refl_case, b, h)
}

// --- Nat.Pair ---------------------------------------------------------------

/// `Nat.Pair`, the carrier constant.
fn pair_ty(d: &mut NatDev<'_>) -> ExprId {
    let pair = d.prelude().pair;
    d.kernel().const_(pair, vec![])
}

/// `Nat.Pair.mk a b`.
pub(super) fn mk_pair(d: &mut NatDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let mk = d.prelude().pair_mk;
    d.const_app(mk, &[a, b])
}

/// `Nat.Pair.fst p`.
pub(super) fn pair_fst(d: &mut NatDev<'_>, p: ExprId) -> ExprId {
    let f = d.prelude().pair_fst;
    d.const_app(f, &[p])
}

/// `Nat.Pair.snd p`.
pub(super) fn pair_snd(d: &mut NatDev<'_>, p: ExprId) -> ExprId {
    let f = d.prelude().pair_snd;
    d.const_app(f, &[p])
}

/// Declare `Nat.Pair`, its constructor, both projections, their defining
/// equations, eta and extensionality.
///
/// # Errors
///
/// Returns the kernel's rejection if any generated declaration does not
/// type-check or a name is already taken.
pub(super) fn declare_pair_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one = d.level_one();
    let type0 = d.kernel().sort(one);

    // Pair : Type 0, with mk : Nat -> Nat -> Pair (no parameters).
    {
        let mk_ty = {
            let concl = d.kernel().const_(p.pair, vec![]);
            let inner = d.arrow(nat, concl);
            d.arrow(nat, inner)
        };
        d.kernel()
            .add_inductive(p.pair, &[], 0, type0, &[(p.pair_mk, mk_ty)])?;
    }

    let pair = pair_ty(d);

    // fst : Pair -> Nat := fun q => Pair.rec.{1} (fun _ => Nat) (fun a _ => a) q
    // snd : Pair -> Nat := fun q => Pair.rec.{1} (fun _ => Nat) (fun _ b => b) q
    for (name, take_first) in [(p.pair_fst, true), (p.pair_snd, false)] {
        let motive = d.kernel().lam(anon, pair, nat, BinderInfo::Default);
        let minor = {
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let chosen = if take_first { a } else { b };
            let inner = d.lam_fv(b_fv, nat, chosen);
            d.lam_fv(a_fv, nat, inner)
        };
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let rec = d.kernel().const_(p.pair_rec, vec![one]);
        let body = d.apply(rec, &[motive, minor, q]);
        let value = d.lam_fv(q_fv, pair, body);
        let ty = d.arrow(pair, nat);
        d.kernel().add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // fst_mk : ∀ a b, Eq Nat (fst (mk a b)) a   -- refl (iota on the literal
    // constructor, exactly as `Nat.Fin.val_mk`).
    d.theorem(p.pair_fst_mk, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let q = mk_pair(d, a, b);
        let lhs = pair_fst(d, q);
        (d.eq(lhs, a), d.refl(a))
    })?;

    // snd_mk : ∀ a b, Eq Nat (snd (mk a b)) b   -- refl.
    d.theorem(p.pair_snd_mk, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let q = mk_pair(d, a, b);
        let lhs = pair_snd(d, q);
        (d.eq(lhs, b), d.refl(b))
    })?;

    // eta : ∀ q, Eq Pair (mk (fst q) (snd q)) q
    //     := fun q => Pair.rec.{0} (fun y => Eq Pair (mk (fst y) (snd y)) y)
    //                              (fun a b => Eq.refl (mk a b)) q
    // The minor is `refl` because at the literal constructor `mk a b` both
    // projections iota-reduce, so the goal is `Eq Pair (mk a b) (mk a b)`.
    {
        let claim = |d: &mut NatDev<'_>, y: ExprId| {
            let f = pair_fst(d, y);
            let s = pair_snd(d, y);
            let rebuilt = mk_pair(d, f, s);
            eq_at(d, pair, rebuilt, y)
        };
        let motive = {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let body = claim(d, y);
            d.lam_fv(y_fv, pair, body)
        };
        let minor = {
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let q = mk_pair(d, a, b);
            let proof = refl_at(d, pair, q);
            let inner = d.lam_fv(b_fv, nat, proof);
            d.lam_fv(a_fv, nat, inner)
        };
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let zero_level = d.kernel().level_zero();
        let rec = d.kernel().const_(p.pair_rec, vec![zero_level]);
        let body = d.apply(rec, &[motive, minor, q]);
        let value = d.lam_fv(q_fv, pair, body);
        let ty = {
            let inner = claim(d, q);
            d.pi_fv(q_fv, pair, inner)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.pair_eta,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // ext : ∀ q r, Eq Nat (fst q) (fst r) -> Eq Nat (snd q) (snd r)
    //             -> Eq Pair q r
    // Rebuild both sides through `eta`, then rewrite the two components.
    {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let fq = pair_fst(d, q);
        let fr = pair_fst(d, r);
        let sq = pair_snd(d, q);
        let sr = pair_snd(d, r);
        let hf_ty = d.eq(fq, fr);
        let hf_fv = d.fresh_fvar();
        let hf = d.kernel().fvar(hf_fv);
        let hs_ty = d.eq(sq, sr);
        let hs_fv = d.fresh_fvar();
        let hs = d.kernel().fvar(hs_fv);

        // mk (fst q) (snd q) = mk (fst r) (snd q) = mk (fst r) (snd r)
        let start = mk_pair(d, fq, sq);
        let middle = mk_pair(d, fr, sq);
        let finish = mk_pair(d, fr, sr);
        let step1 = d.congr(fq, fr, hf, &|d, x| mk_pair(d, x, sq));
        let step2 = d.congr(sq, sr, hs, &|d, x| mk_pair(d, fr, x));
        let rebuilt_eq = trans_at(d, pair, start, middle, finish, step1, step2);

        // Replace each rebuilt side by the pair itself, via `eta`.
        let eta_q = d.const_app(p.pair_eta, &[q]);
        let eta_r = d.const_app(p.pair_eta, &[r]);
        let start_eq_r = trans_at(d, pair, start, finish, r, rebuilt_eq, eta_r);
        let q_eq_start = symm_at(d, pair, start, q, eta_q);
        let proof = trans_at(d, pair, q, start, r, q_eq_start, start_eq_r);

        let stmt = eq_at(d, pair, q, r);
        let ty = {
            let with_hs = d.pi_fv(hs_fv, hs_ty, stmt);
            let with_hf = d.pi_fv(hf_fv, hf_ty, with_hs);
            let with_r = d.pi_fv(r_fv, pair, with_hf);
            d.pi_fv(q_fv, pair, with_r)
        };
        let value = {
            let with_hs = d.lam_fv(hs_fv, hs_ty, proof);
            let with_hf = d.lam_fv(hf_fv, hf_ty, with_hs);
            let with_r = d.lam_fv(r_fv, pair, with_hf);
            d.lam_fv(q_fv, pair, with_r)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.pair_ext,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    Ok(())
}

// --- the halving arithmetic -------------------------------------------------

/// Declare `Nat.lt_two_mul_of_pos` and `Nat.half_le_of_succ_le_succ`.
///
/// # Errors
///
/// Returns the kernel's rejection if either proof is refused.
pub(super) fn declare_halving_arithmetic(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    // lt_two_mul_of_pos : ∀ n, Lt zero n -> Lt n (mul 2 n).
    //
    // `add_lt_add_left` at `(n, 0, n)` gives `n + 0 < n + n`, and `add_zero`
    // rewrites the left side to `n`; then `succ_mul 1 n` plus `one_mul n`
    // turns `mul 2 n` into `n + n`.
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let zero = d.zero();
        let pos_ty = d.lt(zero, n);
        let pos_fv = d.fresh_fvar();
        let pos = d.kernel().fvar(pos_fv);

        let add_n_zero = d.add(n, zero);
        let add_n_n = d.add(n, n);
        let step1 = d.lemma(p.add_lt_add_left, &[n, zero, n, pos]);
        let eq1 = d.lemma(p.add_zero, &[n]);
        let motive1 = d.eq_motive(add_n_zero, &|d, x| {
            let rhs = d.add(n, n);
            d.lt(x, rhs)
        });
        let n_lt_add_n_n = d.transport(add_n_zero, motive1, step1, n, eq1);

        let one = d.num(1);
        let two = d.num(2);
        let mul_two_n = d.mul(two, n);
        let mul_one_n = d.mul(one, n);
        let add_mul_one_n_n = d.add(mul_one_n, n);
        let succ_mul_eq = d.lemma(p.succ_mul, &[one, n]);
        let one_mul_eq = d.lemma(p.one_mul, &[n]);
        let congr_step = d.congr(mul_one_n, n, one_mul_eq, &|d, x| d.add(x, n));
        let (_, mul_two_n_eq_add_n_n) = d.chain(
            mul_two_n,
            &[(add_mul_one_n_n, succ_mul_eq), (add_n_n, congr_step)],
        );
        let rev_eq = d.symm(mul_two_n, add_n_n, mul_two_n_eq_add_n_n);
        let motive2 = d.eq_motive(add_n_n, &|d, x| d.lt(n, x));
        let proof = d.transport(add_n_n, motive2, n_lt_add_n_n, mul_two_n, rev_eq);

        let stmt = d.lt(n, mul_two_n);
        let ty = {
            let with_pos = d.pi_fv(pos_fv, pos_ty, stmt);
            d.pi_fv(n_fv, nat, with_pos)
        };
        let value = {
            let with_pos = d.lam_fv(pos_fv, pos_ty, proof);
            d.lam_fv(n_fv, nat, with_pos)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.lt_two_mul_of_pos,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // half_le_of_succ_le_succ : ∀ m k, Le (succ m) (succ k)
    //                                -> Le (div (succ m) 2) k.
    //
    // `e := succ m` is positive, so `e < 2*e`; `div_mod_lt_mul_iff` (fed the
    // executable witness `div_mod_exec 1 e`) turns that into `e/2 < e`;
    // `lt_of_lt_of_le` with the hypothesis gives `e/2 < succ k`.
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let e = d.succ(m);
        let sk = d.succ(k);
        let bound_ty = d.le(e, sk);
        let bound_fv = d.fresh_fvar();
        let bound = d.kernel().fvar(bound_fv);

        let two = d.num(2);
        let one = d.num(1);
        let the_half = d.div(e, two);
        let r = d.modulo(e, two);
        let pos = d.zero_lt_succ(m);
        let e_lt_2e = d.lemma(p.lt_two_mul_of_pos, &[e, pos]);

        let h_exec = d.lemma(p.div_mod_exec, &[one, e]);
        let iff_fn = d.lemma(p.div_mod_lt_mul_iff, &[two, e, the_half, r, e]);
        let the_iff = d.apply(iff_fn, &[h_exec]);
        let mul_two_e = d.mul(two, e);
        let lt_e_2e_ty = d.lt(e, mul_two_e);
        let lt_half_e_ty = d.lt(the_half, e);
        let forward = iff_forward(d, lt_e_2e_ty, lt_half_e_ty, the_iff);
        let half_lt_e = d.apply(forward, &[e_lt_2e]);
        let half_lt_sk = d.lemma(p.lt_of_lt_of_le, &[the_half, e, sk, half_lt_e, bound]);
        let proof = d.lemma(p.le_of_succ_le_succ, &[the_half, k, half_lt_sk]);

        let stmt = d.le(the_half, k);
        let ty = {
            let with_bound = d.pi_fv(bound_fv, bound_ty, stmt);
            let with_k = d.pi_fv(k_fv, nat, with_bound);
            d.pi_fv(m_fv, nat, with_k)
        };
        let value = {
            let with_bound = d.lam_fv(bound_fv, bound_ty, proof);
            let with_k = d.lam_fv(k_fv, nat, with_bound);
            d.lam_fv(m_fv, nat, with_k)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.half_le_of_succ_le_succ,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    Ok(())
}

// --- Nat.binaryRec ----------------------------------------------------------

/// The step function's type, `Bool -> Nat -> alpha -> alpha`.
fn step_fn_ty(d: &mut NatDev<'_>, alpha: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let inner = d.arrow(alpha, alpha);
    let with_nat = d.arrow(nat, inner);
    d.arrow(bool_ty, with_nat)
}

/// `beq (mod n 2) 1` — this prelude's ad-hoc `Nat.bodd` (`bitwise.rs` uses the
/// same spelling; Mathlib's `Nat.bodd` is not declared here).
fn low_bit(d: &mut NatDev<'_>, n: ExprId) -> ExprId {
    let two = d.num(2);
    let one = d.num(1);
    let r = d.modulo(n, two);
    d.beq(r, one)
}

/// `div n 2`.
fn halve(d: &mut NatDev<'_>, n: ExprId) -> ExprId {
    let two = d.num(2);
    d.div(n, two)
}

/// `Nat.binaryRecAux alpha z f fuel n`.
fn aux(d: &mut NatDev<'_>, alpha: ExprId, z: ExprId, f: ExprId, fuel: ExprId, n: ExprId) -> ExprId {
    let name = d.prelude().binary_rec_aux;
    d.const_app(name, &[alpha, z, f, fuel, n])
}

/// `Nat.binaryRec alpha z f n`.
fn canonical(d: &mut NatDev<'_>, alpha: ExprId, z: ExprId, f: ExprId, n: ExprId) -> ExprId {
    let name = d.prelude().binary_rec;
    d.const_app(name, &[alpha, z, f, n])
}

/// Introduce the shared `(alpha : Type 0) (z : alpha) (f : Bool -> Nat -> alpha
/// -> alpha)` prefix, run `build` on them, and wrap the resulting
/// `(statement, proof)` in the three binders.
fn with_carrier(
    d: &mut NatDev<'_>,
    build: &dyn Fn(&mut NatDev<'_>, ExprId, ExprId, ExprId) -> (ExprId, ExprId),
) -> (ExprId, ExprId) {
    let one = d.level_one();
    let type0 = d.kernel().sort(one);
    let alpha_fv = d.fresh_fvar();
    let alpha = d.kernel().fvar(alpha_fv);
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let f_ty = step_fn_ty(d, alpha);
    let (stmt, proof) = build(d, alpha, z, f);
    let ty = {
        let with_f = d.pi_fv(f_fv, f_ty, stmt);
        let with_z = d.pi_fv(z_fv, alpha, with_f);
        d.pi_fv(alpha_fv, type0, with_z)
    };
    let value = {
        let with_f = d.lam_fv(f_fv, f_ty, proof);
        let with_z = d.lam_fv(z_fv, alpha, with_f);
        d.lam_fv(alpha_fv, type0, with_z)
    };
    (ty, value)
}

/// Declare `Nat.binaryRecAux`, `Nat.binaryRec` and their four defining
/// equations (all `refl`).
///
/// # Errors
///
/// Returns the kernel's rejection if any generated declaration is refused.
pub(super) fn declare_binary_rec_defs(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one = d.level_one();
    let type0 = d.kernel().sort(one);

    // binaryRecAux : Π (alpha : Type 0), alpha -> (Bool -> Nat -> alpha ->
    //                alpha) -> Nat -> Nat -> alpha
    {
        let alpha_fv = d.fresh_fvar();
        let alpha = d.kernel().fvar(alpha_fv);
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let f_ty = step_fn_ty(d, alpha);
        let row_ty = d.arrow(nat, alpha);

        // motive of the fuel recursion: `fun _ : Nat => Nat -> alpha`.
        let motive = d.kernel().lam(anon, nat, row_ty, BinderInfo::Default);
        // fuel = 0: `fun _ : Nat => z`.
        let base_term = d.kernel().lam(anon, nat, z, BinderInfo::Default);
        // fuel = succ k: `fun n => Nat.rec (fun _ => alpha) z
        //                        (fun _ _ => f (bodd n) (n/2) (ih (n/2))) n`.
        let step_term = {
            let k_fv = d.fresh_fvar();
            let ih_fv = d.fresh_fvar();
            let ih = d.kernel().fvar(ih_fv);
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let inner_motive = d.kernel().lam(anon, nat, alpha, BinderInfo::Default);
            let inner_step = {
                let m_fv = d.fresh_fvar();
                let unused_fv = d.fresh_fvar();
                let b = low_bit(d, n);
                let h = halve(d, n);
                let recursive = d.apply(ih, &[h]);
                let combined = d.apply(f, &[b, h, recursive]);
                let with_unused = d.lam_fv(unused_fv, alpha, combined);
                d.lam_fv(m_fv, nat, with_unused)
            };
            let inner_rec = d.kernel().const_(p.rec, vec![one]);
            let guarded = d.apply(inner_rec, &[inner_motive, z, inner_step, n]);
            let over_n = d.lam_fv(n_fv, nat, guarded);
            let with_ih = d.lam_fv(ih_fv, row_ty, over_n);
            d.lam_fv(k_fv, nat, with_ih)
        };
        let fuel_fv = d.fresh_fvar();
        let fuel = d.kernel().fvar(fuel_fv);
        let outer_rec = d.kernel().const_(p.rec, vec![one]);
        let body = d.apply(outer_rec, &[motive, base_term, step_term, fuel]);
        let value = {
            let with_fuel = d.lam_fv(fuel_fv, nat, body);
            let with_f = d.lam_fv(f_fv, f_ty, with_fuel);
            let with_z = d.lam_fv(z_fv, alpha, with_f);
            d.lam_fv(alpha_fv, type0, with_z)
        };
        let ty = {
            let tail = d.arrow(nat, row_ty);
            let with_f = d.arrow(f_ty, tail);
            let with_z = d.arrow(alpha, with_f);
            d.pi_fv(alpha_fv, type0, with_z)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.binary_rec_aux,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(30),
        })?;
    }

    // binaryRec alpha z f n := binaryRecAux alpha z f n n.
    {
        let alpha_fv = d.fresh_fvar();
        let alpha = d.kernel().fvar(alpha_fv);
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let f_ty = step_fn_ty(d, alpha);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = aux(d, alpha, z, f, n, n);
        let value = {
            let with_n = d.lam_fv(n_fv, nat, body);
            let with_f = d.lam_fv(f_fv, f_ty, with_n);
            let with_z = d.lam_fv(z_fv, alpha, with_f);
            d.lam_fv(alpha_fv, type0, with_z)
        };
        let ty = {
            let tail = d.arrow(nat, alpha);
            let with_f = d.arrow(f_ty, tail);
            let with_z = d.arrow(alpha, with_f);
            d.pi_fv(alpha_fv, type0, with_z)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.binary_rec,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(31),
        })?;
    }

    // binaryRecAux_zero_fuel : ∀ alpha z f n, binaryRecAux alpha z f 0 n = z.
    {
        let (ty, value) = with_carrier(d, &|d, alpha, z, f| {
            let nat = d.nat_ty();
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let zero = d.zero();
            let lhs = aux(d, alpha, z, f, zero, n);
            let stmt = eq_at(d, alpha, lhs, z);
            let proof = refl_at(d, alpha, z);
            let ty = d.pi_fv(n_fv, nat, stmt);
            let value = d.lam_fv(n_fv, nat, proof);
            (ty, value)
        });
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.binary_rec_aux_zero_fuel,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // binaryRecAux_zero : ∀ alpha z f fuel, binaryRecAux alpha z f fuel 0 = z.
    // Case-split on `fuel` alone (no induction hypothesis): at `0` the base row
    // is the constant `z`; at `succ k` the `n = 0` guard is a LITERAL zero, so
    // it fires by iota and short-circuits the recursive call. Both refl.
    {
        let (ty, value) = with_carrier(d, &|d, alpha, z, f| {
            let nat = d.nat_ty();
            let fuel_fv = d.fresh_fvar();
            let fuel = d.kernel().fvar(fuel_fv);
            let claim = |d: &mut NatDev<'_>, x: ExprId| {
                let zero = d.zero();
                let lhs = aux(d, alpha, z, f, x, zero);
                eq_at(d, alpha, lhs, z)
            };
            let proof = cases_zero_succ(
                d,
                fuel,
                &claim,
                &|d| refl_at(d, alpha, z),
                &|d, _k| refl_at(d, alpha, z),
            );
            let stmt = claim(d, fuel);
            let ty = d.pi_fv(fuel_fv, nat, stmt);
            let value = d.lam_fv(fuel_fv, nat, proof);
            (ty, value)
        });
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.binary_rec_aux_zero,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // binaryRecAux_succ : ∀ alpha z f k m,
    //   binaryRecAux alpha z f (succ k) (succ m)
    //     = f (beq ((succ m) % 2) 1) ((succ m) / 2)
    //         (binaryRecAux alpha z f k ((succ m) / 2))
    // refl: the fuel recursor iota-reduces at `succ k` and the `n = 0` guard
    // iota-reduces at `succ m`.
    {
        let (ty, value) = with_carrier(d, &|d, alpha, z, f| {
            let nat = d.nat_ty();
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let m_fv = d.fresh_fvar();
            let m = d.kernel().fvar(m_fv);
            let sk = d.succ(k);
            let sm = d.succ(m);
            let lhs = aux(d, alpha, z, f, sk, sm);
            let b = low_bit(d, sm);
            let h = halve(d, sm);
            let inner = aux(d, alpha, z, f, k, h);
            let rhs = d.apply(f, &[b, h, inner]);
            let stmt = eq_at(d, alpha, lhs, rhs);
            let proof = refl_at(d, alpha, rhs);
            let ty = {
                let with_m = d.pi_fv(m_fv, nat, stmt);
                d.pi_fv(k_fv, nat, with_m)
            };
            let value = {
                let with_m = d.lam_fv(m_fv, nat, proof);
                d.lam_fv(k_fv, nat, with_m)
            };
            (ty, value)
        });
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.binary_rec_aux_succ,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // binaryRec_zero : ∀ alpha z f, binaryRec alpha z f 0 = z   -- refl.
    {
        let (ty, value) = with_carrier(d, &|d, alpha, z, f| {
            let zero = d.zero();
            let lhs = canonical(d, alpha, z, f, zero);
            let stmt = eq_at(d, alpha, lhs, z);
            let proof = refl_at(d, alpha, z);
            (stmt, proof)
        });
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.binary_rec_zero,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    Ok(())
}

/// `binaryRecAux_agree_of_fuel : ∀ alpha z f fuel1 n fuel2, Le n fuel1 ->
/// Le n fuel2 -> Eq alpha (binaryRecAux … fuel1 n) (binaryRecAux … fuel2 n)`.
///
/// The DOUBLE-fuel form, for the reason `rec_agreement.rs`'s module doc gives:
/// `binaryRec alpha z f n` puts `n` itself in the fuel slot, so a
/// "fuel versus the canonical instance" statement refers to itself and its
/// induction cannot unfold. Two independently-chosen sufficient fuels have no
/// such self-reference, and the canonical instance is then the corollary at
/// `fuel2 := n` with `le_refl`.
///
/// # Errors
///
/// Returns the kernel's rejection if the proof is refused.
pub(super) fn declare_binary_rec_aux_agree_of_fuel(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let (ty, value) = with_carrier(d, &|d, alpha, z, f| {
        let nat = d.nat_ty();

        // statement(fuel1, n, fuel2)
        let statement = |d: &mut NatDev<'_>, fuel1: ExprId, n: ExprId, fuel2: ExprId| -> ExprId {
            let lhs = aux(d, alpha, z, f, fuel1, n);
            let rhs = aux(d, alpha, z, f, fuel2, n);
            let concl = eq_at(d, alpha, lhs, rhs);
            let h2 = d.le(n, fuel2);
            let inner = d.arrow(h2, concl);
            let h1 = d.le(n, fuel1);
            d.arrow(h1, inner)
        };

        // At `fuel1 = 0`: `Le n 0` forces `n = 0`, and both sides are `z`.
        let base = |d: &mut NatDev<'_>, n: ExprId, fuel2: ExprId| -> ExprId {
            let zero = d.zero();
            let h1_ty = d.le(n, zero);
            let h1_fv = d.fresh_fvar();
            let h1 = d.kernel().fvar(h1_fv);
            let h2_ty = d.le(n, fuel2);
            let h2_fv = d.fresh_fvar();

            let zero_le_n = d.lemma(p.zero_le, &[n]);
            let n_eq_zero = d.lemma(p.le_antisymm, &[n, zero, h1, zero_le_n]);
            // `aux fuel2 0 = z`, transported back along `n = 0`.
            let at_zero = d.const_app(p.binary_rec_aux_zero, &[alpha, z, f, fuel2]);
            let zero_eq_n = d.symm(n, zero, n_eq_zero);
            let motive = d.eq_motive(zero, &|d, x| {
                let side = aux(d, alpha, z, f, fuel2, x);
                eq_at(d, alpha, side, z)
            });
            let rhs_eq_z = d.transport(zero, motive, at_zero, n, zero_eq_n);
            let rhs = aux(d, alpha, z, f, fuel2, n);
            let body = symm_at(d, alpha, rhs, z, rhs_eq_z);

            let with_h2 = d.lam_fv(h2_fv, h2_ty, body);
            d.lam_fv(h1_fv, h1_ty, with_h2)
        };

        // At `fuel1 = succ k`.
        let step = |d: &mut NatDev<'_>,
                    k: ExprId,
                    ih: ExprId,
                    n: ExprId,
                    fuel2: ExprId|
         -> ExprId {
            let sk = d.succ(k);
            // Fold both hypotheses into the motive so each branch of the
            // `n = 0` / `n = succ m` split re-introduces them at its OWN shape
            // (`cases_zero_succ`'s doc: an outer hypothesis does not
            // specialize).
            let claim = |d: &mut NatDev<'_>, x: ExprId| statement(d, sk, x, fuel2);
            cases_zero_succ(
                d,
                n,
                &claim,
                &|d| {
                    // n = 0: both sides are `z` by `binaryRecAux_zero`.
                    let zero = d.zero();
                    let h1_ty = d.le(zero, sk);
                    let h1_fv = d.fresh_fvar();
                    let h2_ty = d.le(zero, fuel2);
                    let h2_fv = d.fresh_fvar();
                    let lhs = aux(d, alpha, z, f, sk, zero);
                    let rhs = aux(d, alpha, z, f, fuel2, zero);
                    let lhs_z = d.const_app(p.binary_rec_aux_zero, &[alpha, z, f, sk]);
                    let rhs_z = d.const_app(p.binary_rec_aux_zero, &[alpha, z, f, fuel2]);
                    let z_rhs = symm_at(d, alpha, rhs, z, rhs_z);
                    let body = trans_at(d, alpha, lhs, z, rhs, lhs_z, z_rhs);
                    let with_h2 = d.lam_fv(h2_fv, h2_ty, body);
                    d.lam_fv(h1_fv, h1_ty, with_h2)
                },
                &|d, m| {
                    let sm = d.succ(m);
                    let h1_ty = d.le(sm, sk);
                    let h1_fv = d.fresh_fvar();
                    let h1 = d.kernel().fvar(h1_fv);
                    let h2_ty = d.le(sm, fuel2);
                    let h2_fv = d.fresh_fvar();
                    let h2 = d.kernel().fvar(h2_fv);

                    // `fuel2` is positive (it bounds `succ m`), so it is
                    // `succ (pred fuel2)`; work there and transport back.
                    let one = d.num(1);
                    let zero = d.zero();
                    let zero_le_m = d.lemma(p.zero_le, &[m]);
                    let one_le_sm = d.lemma(p.succ_le_succ, &[zero, m, zero_le_m]);
                    let pos_fuel2 = d.lemma(p.le_trans, &[one, sm, fuel2, one_le_sm, h2]);
                    let f2p = d.pred(fuel2);
                    let sf2p = d.succ(f2p);
                    let fuel2_eq = d.lemma(p.succ_pred_of_pos, &[fuel2, pos_fuel2]);

                    // Move `h2` to the `succ (pred fuel2)` shape.
                    let h2_at_s = {
                        let motive = d.eq_motive(fuel2, &|d, x| d.le(sm, x));
                        d.transport(fuel2, motive, h2, sf2p, fuel2_eq)
                    };

                    let hh = halve(d, sm);
                    let half_le_k = d.lemma(p.half_le_of_succ_le_succ, &[m, k, h1]);
                    let half_le_f2p = d.lemma(p.half_le_of_succ_le_succ, &[m, f2p, h2_at_s]);
                    let ih_at = d.apply(ih, &[hh, f2p]);
                    let recursive = d.apply(ih_at, &[half_le_k, half_le_f2p]);

                    // Both sides iota-reduce to `f b hh (aux _ hh)`; congr in
                    // the third argument alone.
                    let b = low_bit(d, sm);
                    let left_inner = aux(d, alpha, z, f, k, hh);
                    let right_inner = aux(d, alpha, z, f, f2p, hh);
                    let at_succ = congr_at(d, alpha, left_inner, right_inner, recursive, &|d, x| {
                        d.apply(f, &[b, hh, x])
                    });

                    // Transport the RIGHT-hand fuel back from `succ (pred
                    // fuel2)` to `fuel2`.
                    let rev = d.symm(fuel2, sf2p, fuel2_eq);
                    let lhs = aux(d, alpha, z, f, sk, sm);
                    let motive = d.eq_motive(sf2p, &|d, x| {
                        let rhs = aux(d, alpha, z, f, x, sm);
                        eq_at(d, alpha, lhs, rhs)
                    });
                    let body = d.transport(sf2p, motive, at_succ, fuel2, rev);

                    let with_h2 = d.lam_fv(h2_fv, h2_ty, body);
                    d.lam_fv(h1_fv, h1_ty, with_h2)
                },
            )
        };

        let fuel1_fv = d.fresh_fvar();
        let fuel1 = d.kernel().fvar(fuel1_fv);
        let proof_fn = agree_by_fuel_induction(d, &statement, &base, &step, fuel1);

        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let fuel2_fv = d.fresh_fvar();
        let fuel2 = d.kernel().fvar(fuel2_fv);
        let proof = d.apply(proof_fn, &[n, fuel2]);
        let stmt = statement(d, fuel1, n, fuel2);
        let ty = {
            let with_f2 = d.pi_fv(fuel2_fv, nat, stmt);
            let with_n = d.pi_fv(n_fv, nat, with_f2);
            d.pi_fv(fuel1_fv, nat, with_n)
        };
        let value = {
            let with_f2 = d.lam_fv(fuel2_fv, nat, proof);
            let with_n = d.lam_fv(n_fv, nat, with_f2);
            d.lam_fv(fuel1_fv, nat, with_n)
        };
        (ty, value)
    });
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.binary_rec_aux_agree_of_fuel,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(())
}

/// `binaryRec_succ : ∀ alpha z f m, binaryRec alpha z f (succ m)
/// = f (beq ((succ m) % 2) 1) ((succ m) / 2) (binaryRec alpha z f ((succ m) / 2))`
///
/// This is the recursive equation Mathlib's `binaryRec` gets definitionally
/// from `WellFounded.fix`. Here it is a THEOREM, because the canonical
/// instance supplies fuel `succ m` while the recursive call needs fuel
/// `(succ m) / 2`; [`declare_binary_rec_aux_agree_of_fuel`] closes the gap.
///
/// # Errors
///
/// Returns the kernel's rejection if the proof is refused.
pub(super) fn declare_binary_rec_succ(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let (ty, value) = with_carrier(d, &|d, alpha, z, f| {
        let nat = d.nat_ty();
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let sm = d.succ(m);
        let hh = halve(d, sm);
        let b = low_bit(d, sm);

        // `binaryRec … (succ m) ≡ aux (succ m) (succ m) ≡ f b hh (aux m hh)`.
        let inner_at_m = aux(d, alpha, z, f, m, hh);
        let inner_canonical = aux(d, alpha, z, f, hh, hh);

        let le_refl_sm = d.lemma(p.le_refl, &[sm]);
        let half_le_m = d.lemma(p.half_le_of_succ_le_succ, &[m, m, le_refl_sm]);
        let half_le_half = d.lemma(p.le_refl, &[hh]);
        let agree_fn = d.const_app(p.binary_rec_aux_agree_of_fuel, &[alpha, z, f, m, hh, hh]);
        let agreement = d.apply(agree_fn, &[half_le_m, half_le_half]);
        let proof = congr_at(d, alpha, inner_at_m, inner_canonical, agreement, &|d, x| {
            d.apply(f, &[b, hh, x])
        });

        let lhs = canonical(d, alpha, z, f, sm);
        let rhs = {
            let rec_call = canonical(d, alpha, z, f, hh);
            d.apply(f, &[b, hh, rec_call])
        };
        let stmt = eq_at(d, alpha, lhs, rhs);
        let ty = d.pi_fv(m_fv, nat, stmt);
        let value = d.lam_fv(m_fv, nat, proof);
        (ty, value)
    });
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.binary_rec_succ,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(())
}

/// The concrete evaluation checks the trusted gate CANNOT perform on its own.
///
/// `Kernel::add_declaration` type-checks a `Definition`'s value against its
/// stated type; a function that computes the wrong number has the right type,
/// so `binaryRecAux`'s admission says nothing about what it computes. These
/// two theorems close by `Eq.refl` only if the definition actually evaluates
/// to the stated numerals.
///
/// The instance is deliberately the **round trip**: rebuilding `n` from its own
/// bits with `Nat.bit`, i.e. `binaryRec 0 (fun b _ acc => bit b acc) n = n`.
/// Any misplaced bit, swapped guard, or off-by-one in the halving changes the
/// answer, and `13 = 0b1101` is asymmetric under bit reversal (`0b1011 = 11`),
/// so a reversed traversal fails rather than coincidentally passing. `6` adds
/// a trailing zero bit, which a `mod`/`div` transposition would drop. Both
/// magnitudes are tiny, which matters: every numeral here is unary
/// (`NatOps::num` is a `succ` tower), so kernel cost is superlinear in the
/// largest value FORMED.
///
/// # Errors
///
/// Returns the kernel's rejection — which for these is exactly the finding
/// that the definition computes something else.
pub(super) fn declare_binary_rec_evaluation(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();

    // `fun (b : Bool) (_ : Nat) (acc : Nat) => Nat.bit b acc`.
    let rebuild = {
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let ignored_fv = d.fresh_fvar();
        let acc_fv = d.fresh_fvar();
        let acc = d.kernel().fvar(acc_fv);
        let body = d.const_app(p.bit, &[b, acc]);
        let with_acc = d.lam_fv(acc_fv, nat, body);
        let with_ignored = d.lam_fv(ignored_fv, nat, with_acc);
        d.lam_fv(b_fv, bool_ty, with_ignored)
    };

    for (name, value) in [
        (p.binary_rec_rebuilds_thirteen, 13u32),
        (p.binary_rec_rebuilds_six, 6u32),
    ] {
        let zero = d.zero();
        let numeral = d.num(value);
        let lhs = d.const_app(p.binary_rec, &[nat, zero, rebuild, numeral]);
        let stmt = d.eq(lhs, numeral);
        let proof = d.refl(numeral);
        d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: stmt,
            value: proof,
        })?;
    }

    Ok(())
}

/// Everything this module declares, in dependency order.
///
/// # Errors
///
/// Returns the kernel's rejection if any declaration is refused.
pub(super) fn declare_binary_rec_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_pair_all(d, p)?;
    declare_halving_arithmetic(d, p)?;
    declare_binary_rec_defs(d, p)?;
    declare_binary_rec_aux_agree_of_fuel(d, p)?;
    declare_binary_rec_succ(d, p)?;
    declare_binary_rec_evaluation(d, p)?;
    Ok(())
}

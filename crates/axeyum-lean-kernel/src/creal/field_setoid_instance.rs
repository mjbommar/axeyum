//! ADR-1627: **ℝ as an `AlgS.Field`** — the instance the field record was
//! designed around, and the one that decided the design.
//!
//! # The question this module answers
//!
//! The obvious shape for a constructive field's inverse is
//! `inv : (x : α) → apart x zero → α`, and the obvious guess is that
//! `CReal.inv`'s positive-bound witness IS the apartness witness. **It is
//! not.** `CReal.inv : (x : CReal) → (k : Nat) → PosBound x k → CReal` takes
//! the modulus `k` as **data**; `CReal.Apart x zero` is
//! `Or (lt x zero) (lt zero x)`, a `Prop`, and `CReal.pos_bound_of_lt` hands
//! the modulus over only inside an `Exists`, also a `Prop`. Neither the sign
//! nor the modulus can be eliminated out of a `Prop` into a `CReal`, so the
//! functional field is **undefinable here** — a large-elimination wall, not a
//! missing lemma.
//!
//! `AlgS.Field`'s `mulInvEx : ∀ a, apart a zero → ∃ b, equiv (mul a b) one`
//! is a `Prop`, so both eliminations are legal, and this module performs
//! exactly them: one `Or.elim` on the sign and one `Exists.rec` on the
//! modulus, per branch.
//!
//! # What each branch costs
//!
//! - **Positive** (`0 < x`): free. `CReal.pos_bound_of_lt` then
//!   `CReal.mul_inv_cancel`, verbatim.
//! - **Negative** (`x < 0`): two new steps. `CReal.pos_of_neg_lt_zero` turns
//!   `x < 0` into `0 < −x` (one `add_lt_add_of_le_of_lt` read back through
//!   `lt_congr`), and the witness is `−(−x)⁻¹`, which needs the sign pushed
//!   through a product. `CReal` has `neg_mul_neg` (squares only) and no
//!   `mul_neg`, so this uses `AlgS.mul_neg_right` at `CReal.commRingS` —
//!   declared in `nat_prelude::field_setoid` precisely for this branch.
//!
//! # What is declared
//!
//! | name | what it is |
//! |---|---|
//! | `CReal.apart_compat` | `Equiv x y → Apart x y → False` — `not_equiv_of_apart` with its arguments swapped |
//! | `CReal.one_apart_zero` | `Apart one zero`, from `apart_zero_one` by `apart_symm` |
//! | `CReal.pos_of_neg_lt_zero` | `lt x zero → lt zero (neg x)` |
//! | `CReal.mulInvEx` | the existential inverse |
//! | `CReal.fieldS` | `AlgS.Field` |
//!
//! **`AlgS.Field.IsTight CReal.fieldS` is NOT declared, and that is the
//! finding.** Tightness (`¬(Apart x y) → Equiv x y`) is not Markov's
//! principle — `creal.rs`'s own doc block on `not_apart_one_of_pow_succ_eq_one`
//! says it is, and that is wrong; Markov is the converse. It is constructively
//! true of the Bishop reals, but its proof needs `¬(lt x y) → le y x`, i.e. a
//! single-index introduction rule for `CReal.lt` (`x_n − y_n > 2/(n+1)`
//! implies `y < x` with an explicit rational gap), and no such lemma exists
//! among `CReal`'s order theorems. That is why `AlgS.Field` carries tightness
//! as a predicate and not as a field: making it a field would have made `ℝ`
//! not a field in this library, for a property no theorem above it uses.

use crate::Kernel;
use crate::KernelError;
use crate::creal::CRealPrelude;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;
use crate::nat_prelude::structures::{app2, arrow, lam_over, pi_over};

const X_FV: u64 = 27_000;
const Y_FV: u64 = 27_001;
const K_FV: u64 = 27_003;
const H1_FV: u64 = 27_010;
const H2_FV: u64 = 27_011;
const H3_FV: u64 = 27_012;
const SCRATCH_FV: u64 = 27_020;

fn t_app(k: &mut Kernel, f: ExprId, xs: &[ExprId]) -> ExprId {
    let mut e = f;
    for x in xs {
        e = k.app(e, *x);
    }
    e
}

/// This module's own name registry (ADR-1512), so adding a declaration here
/// touches this module and `creal.rs`'s `STEP_DISPATCH` and nothing else.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FieldSNames {
    /// `CReal.apart_compat : ∀ x y, Equiv x y → Apart x y → False`.
    pub apart_compat: NameId,
    /// `CReal.one_apart_zero : Apart CReal.one CReal.zero`.
    pub one_apart_zero: NameId,
    /// `CReal.pos_of_neg_lt_zero : ∀ x, lt x zero → lt zero (neg x)`.
    pub pos_of_neg_lt_zero: NameId,
    /// `CReal.mulInvEx : ∀ x, Apart x zero → ∃ y, Equiv (mul x y) one`.
    pub mul_inv_ex: NameId,
    /// `CReal.fieldS : AlgS.Field`.
    pub field_s: NameId,
}

impl FieldSNames {
    /// Intern this module's five names under the `CReal` root.
    pub fn intern(kernel: &mut Kernel, creal: NameId) -> Self {
        Self {
            apart_compat: kernel.name_str(creal, "apart_compat"),
            one_apart_zero: kernel.name_str(creal, "one_apart_zero"),
            pos_of_neg_lt_zero: kernel.name_str(creal, "pos_of_neg_lt_zero"),
            mul_inv_ex: kernel.name_str(creal, "mulInvEx"),
            field_s: kernel.name_str(creal, "fieldS"),
        }
    }

    /// Every name this module declares, for a test that wants to walk them.
    #[must_use]
    pub fn all(&self) -> [NameId; 5] {
        [
            self.apart_compat,
            self.one_apart_zero,
            self.pos_of_neg_lt_zero,
            self.mul_inv_ex,
            self.field_s,
        ]
    }
}

/// `AlgS.Field.ofCommRing`, `AlgS.mul_neg_right` and `AlgS.Field` itself,
/// re-derived from the interned `AlgS` root (`name_str` is interned, so these
/// are the same `NameId`s `nat_prelude::field_setoid` produced).
struct Algs {
    field_ind: NameId,
    of_comm_ring: NameId,
    mul_neg_right: NameId,
}

fn algs(k: &mut Kernel) -> Algs {
    let anon = k.anon();
    let root = k.name_str(anon, "AlgS");
    let field = k.name_str(root, "Field");
    Algs {
        field_ind: field,
        of_comm_ring: k.name_str(field, "ofCommRing"),
        mul_neg_right: k.name_str(root, "mul_neg_right"),
    }
}

/// The `CReal` constants every proof below is built from.
struct C {
    creal: ExprId,
    zero: ExprId,
    one: ExprId,
    add: ExprId,
    mul: ExprId,
    neg: ExprId,
    lt: ExprId,
    equiv: ExprId,
    equiv_symm: ExprId,
    equiv_trans: ExprId,
    neg_congr: ExprId,
    mul_comm: ExprId,
    false_: ExprId,
    lvl1: crate::level::LevelId,
}

fn cctx(k: &mut Kernel, p: &CRealPrelude) -> C {
    let lg = p.rat.int.nat.logic;
    let l0 = k.level_zero();
    C {
        creal: k.const_(p.creal, vec![]),
        zero: k.const_(p.zero, vec![]),
        one: k.const_(p.one, vec![]),
        add: k.const_(p.add, vec![]),
        mul: k.const_(p.mul, vec![]),
        neg: k.const_(p.neg, vec![]),
        lt: k.const_(p.lt, vec![]),
        equiv: k.const_(p.equiv, vec![]),
        equiv_symm: k.const_(p.equiv_symm, vec![]),
        equiv_trans: k.const_(p.equiv_trans, vec![]),
        neg_congr: k.const_(p.neg_congr, vec![]),
        mul_comm: k.const_(p.mul_comm, vec![]),
        false_: k.const_(lg.false_, vec![]),
        lvl1: k.level_succ(l0),
    }
}

impl C {
    fn eqv(&self, k: &mut Kernel, a: ExprId, b: ExprId) -> ExprId {
        app2(k, self.equiv, a, b)
    }
    fn lt_of(&self, k: &mut Kernel, a: ExprId, b: ExprId) -> ExprId {
        app2(k, self.lt, a, b)
    }
    fn times(&self, k: &mut Kernel, a: ExprId, b: ExprId) -> ExprId {
        app2(k, self.mul, a, b)
    }
    fn tr(
        &self,
        k: &mut Kernel,
        a: ExprId,
        b: ExprId,
        c: ExprId,
        h1: ExprId,
        h2: ExprId,
    ) -> ExprId {
        t_app(k, self.equiv_trans, &[a, b, c, h1, h2])
    }
    fn sy(&self, k: &mut Kernel, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
        t_app(k, self.equiv_symm, &[a, b, h])
    }
}

/// `CReal.apart_compat : forall x y, Equiv x y -> Apart x y -> False` —
/// `not_equiv_of_apart` with its two arguments the other way round, which is
/// the order `AlgS.Field`'s `apartCompat` slot wants.
fn declare_apart_compat(k: &mut Kernel, p: &CRealPrelude) -> Result<(), KernelError> {
    let c = cctx(k, p);
    let x = k.fvar(X_FV);
    let y = k.fvar(Y_FV);
    let apart_c = k.const_(p.apart, vec![]);
    let heq_ty = c.eqv(k, x, y);
    let hap_ty = app2(k, apart_c, x, y);
    let heq = k.fvar(H1_FV);
    let hap = k.fvar(H2_FV);

    let nea = {
        let t = k.const_(p.not_equiv_of_apart, vec![]);
        t_app(k, t, &[x, y, hap])
    };
    let proof = k.app(nea, heq);

    let value = lam_over(k, H2_FV, hap_ty, proof);
    let value = lam_over(k, H1_FV, heq_ty, value);
    let value = lam_over(k, Y_FV, c.creal, value);
    let value = lam_over(k, X_FV, c.creal, value);

    let ty = arrow(k, hap_ty, c.false_);
    let ty = arrow(k, heq_ty, ty);
    let ty = pi_over(k, Y_FV, c.creal, ty);
    let ty = pi_over(k, X_FV, c.creal, ty);

    k.add_declaration(Declaration::Theorem {
        name: p.field_s.apart_compat,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.one_apart_zero : Apart CReal.one CReal.zero` — the non-vacuity
/// witness, `apart_zero_one` symmetrised.
fn declare_one_apart_zero(k: &mut Kernel, p: &CRealPrelude) -> Result<(), KernelError> {
    let c = cctx(k, p);
    let apart_c = k.const_(p.apart, vec![]);
    let ty = app2(k, apart_c, c.one, c.zero);
    let value = {
        let t = k.const_(p.apart_symm, vec![]);
        let w = k.const_(p.apart_zero_one, vec![]);
        t_app(k, t, &[c.zero, c.one, w])
    };
    k.add_declaration(Declaration::Theorem {
        name: p.field_s.one_apart_zero,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.pos_of_neg_lt_zero : forall x, lt x zero -> lt zero (neg x)`.
///
/// `add_lt_add_of_le_of_lt (−x) (−x) x 0 (le_refl (−x)) h` gives
/// `(−x)+x < (−x)+0`; `lt_congr` reads both sides back through
/// `add_comm`/`add_neg` and `add_zero`. No new estimate.
fn declare_pos_of_neg_lt_zero(k: &mut Kernel, p: &CRealPrelude) -> Result<(), KernelError> {
    let c = cctx(k, p);
    let x = k.fvar(X_FV);
    let h_ty = c.lt_of(k, x, c.zero);
    let h = k.fvar(H1_FV);
    let nx = k.app(c.neg, x);

    let base = {
        let t = k.const_(p.add_lt_add_of_le_of_lt, vec![]);
        let lr = {
            let r = k.const_(p.le_refl, vec![]);
            k.app(r, nx)
        };
        t_app(k, t, &[nx, nx, x, c.zero, lr, h])
    }; // lt (add (neg x) x) (add (neg x) zero)

    let nx_x = app2(k, c.add, nx, x);
    let x_nx = app2(k, c.add, x, nx);
    let nx_zero = app2(k, c.add, nx, c.zero);

    let e1 = {
        let comm = {
            let t = k.const_(p.add_comm, vec![]);
            app2(k, t, nx, x)
        }; // Equiv (add (neg x) x) (add x (neg x))
        let an = {
            let t = k.const_(p.add_neg, vec![]);
            k.app(t, x)
        }; // Equiv (add x (neg x)) zero
        c.tr(k, nx_x, x_nx, c.zero, comm, an)
    };
    let e2 = {
        let t = k.const_(p.add_zero, vec![]);
        k.app(t, nx)
    }; // Equiv (add (neg x) zero) (neg x)

    let proof = {
        let t = k.const_(p.lt_congr, vec![]);
        t_app(k, t, &[nx_x, c.zero, nx_zero, nx, e1, e2, base])
    };

    let value = lam_over(k, H1_FV, h_ty, proof);
    let value = lam_over(k, X_FV, c.creal, value);

    let concl = c.lt_of(k, c.zero, nx);
    let ty = arrow(k, h_ty, concl);
    let ty = pi_over(k, X_FV, c.creal, ty);

    k.add_declaration(Declaration::Theorem {
        name: p.field_s.pos_of_neg_lt_zero,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.mulInvEx : forall x, Apart x zero ->
/// Exists CReal (fun y => Equiv (mul x y) one)`.
#[allow(clippy::too_many_lines)]
fn declare_mul_inv_ex(k: &mut Kernel, p: &CRealPrelude, a: &Algs) -> Result<(), KernelError> {
    let lg = p.rat.int.nat.logic;
    let c = cctx(k, p);
    let x = k.fvar(X_FV);
    let apart_c = k.const_(p.apart, vec![]);
    let h_ty = app2(k, apart_c, x, c.zero);
    let h = k.fvar(H1_FV);
    let nat = k.const_(lg.nat, vec![]);

    let pred = {
        let y = k.fvar(Y_FV);
        let xy = c.times(k, x, y);
        let body = c.eqv(k, xy, c.one);
        lam_over(k, Y_FV, c.creal, body)
    };
    let ex_c = k.const_(lg.exists_, vec![c.lvl1]);
    let goal = app2(k, ex_c, c.creal, pred);
    let intro = k.const_(lg.exists_intro, vec![c.lvl1]);
    let ex_rec = k.const_(lg.exists_rec, vec![c.lvl1]);

    // `Exists (fun k : Nat => PosBound t k)` and the eliminator over it, for
    // a modulus target `t`.
    let bound_pred = |k: &mut Kernel, t: ExprId| {
        let kk = k.fvar(K_FV);
        let pb = k.const_(p.pos_bound, vec![]);
        let body = app2(k, pb, t, kk);
        lam_over(k, K_FV, nat, body)
    };

    // --- positive branch: `0 < x`. Free. ---------------------------------
    let branch_pos = {
        let hp = k.fvar(H2_FV);
        let hp_ty = c.lt_of(k, c.zero, x);
        let bp = bound_pred(k, x);
        let witness = {
            let t = k.const_(p.pos_bound_of_lt, vec![]);
            t_app(k, t, &[x, hp])
        };
        let motive = {
            let ex_ty = app2(k, ex_c, nat, bp);
            lam_over(k, SCRATCH_FV, ex_ty, goal)
        };
        let minor = {
            let kk = k.fvar(K_FV);
            let pb = k.const_(p.pos_bound, vec![]);
            let hk_ty = app2(k, pb, x, kk);
            let hk = k.fvar(H3_FV);
            let inv = {
                let t = k.const_(p.inv, vec![]);
                t_app(k, t, &[x, kk, hk])
            };
            let cancel = {
                let t = k.const_(p.mul_inv_cancel, vec![]);
                t_app(k, t, &[x, kk, hk])
            };
            let body = t_app(k, intro, &[c.creal, pred, inv, cancel]);
            let inner = lam_over(k, H3_FV, hk_ty, body);
            lam_over(k, K_FV, nat, inner)
        };
        let body = t_app(k, ex_rec, &[nat, bp, motive, minor, witness]);
        lam_over(k, H2_FV, hp_ty, body)
    };

    // --- negative branch: `x < 0`. Two new steps. -------------------------
    let branch_neg = {
        let hn = k.fvar(H2_FV);
        let hn_ty = c.lt_of(k, x, c.zero);
        let nx = k.app(c.neg, x);
        let pos = {
            let t = k.const_(p.field_s.pos_of_neg_lt_zero, vec![]);
            t_app(k, t, &[x, hn])
        };
        let bp = bound_pred(k, nx);
        let witness = {
            let t = k.const_(p.pos_bound_of_lt, vec![]);
            t_app(k, t, &[nx, pos])
        };
        let motive = {
            let ex_ty = app2(k, ex_c, nat, bp);
            lam_over(k, SCRATCH_FV, ex_ty, goal)
        };
        let minor = {
            let kk = k.fvar(K_FV);
            let pb = k.const_(p.pos_bound, vec![]);
            let hk_ty = app2(k, pb, nx, kk);
            let hk = k.fvar(H3_FV);
            let tinv = {
                let t = k.const_(p.inv, vec![]);
                t_app(k, t, &[nx, kk, hk])
            };
            let neg_t = k.app(c.neg, tinv);
            let mnr = {
                let t = k.const_(a.mul_neg_right, vec![]);
                let ring = k.const_(p.comm_ring_s, vec![]);
                k.app(t, ring)
            };
            // `x·(−t) ~ −(x·t) ~ −(t·x) ~ t·(−x) ~ (−x)·t ~ 1`.
            let x_negt = c.times(k, x, neg_t);
            let xt = c.times(k, x, tinv);
            let neg_xt = k.app(c.neg, xt);
            let tx = c.times(k, tinv, x);
            let neg_tx = k.app(c.neg, tx);
            let t_negx = c.times(k, tinv, nx);
            let negx_t = c.times(k, nx, tinv);

            let s1 = t_app(k, mnr, &[x, tinv]); // x·(−t) ~ −(x·t)
            let s2 = {
                let comm = app2(k, c.mul_comm, x, tinv); // x·t ~ t·x
                t_app(k, c.neg_congr, &[xt, tx, comm])
            }; // −(x·t) ~ −(t·x)
            let s3 = {
                let fwd = t_app(k, mnr, &[tinv, x]); // t·(−x) ~ −(t·x)
                c.sy(k, t_negx, neg_tx, fwd)
            }; // −(t·x) ~ t·(−x)
            let s4 = app2(k, c.mul_comm, tinv, nx); // t·(−x) ~ (−x)·t
            let s5 = {
                let t = k.const_(p.mul_inv_cancel, vec![]);
                t_app(k, t, &[nx, kk, hk])
            }; // (−x)·t ~ 1

            let c4 = c.tr(k, t_negx, negx_t, c.one, s4, s5);
            let c3 = c.tr(k, neg_tx, t_negx, c.one, s3, c4);
            let c2 = c.tr(k, neg_xt, neg_tx, c.one, s2, c3);
            let chain = c.tr(k, x_negt, neg_xt, c.one, s1, c2);

            let body = t_app(k, intro, &[c.creal, pred, neg_t, chain]);
            let inner = lam_over(k, H3_FV, hk_ty, body);
            lam_over(k, K_FV, nat, inner)
        };
        let body = t_app(k, ex_rec, &[nat, bp, motive, minor, witness]);
        lam_over(k, H2_FV, hn_ty, body)
    };

    // `Apart x zero` beta/delta-reduces to `Or (lt x zero) (lt zero x)`, so
    // `Or.elim` applies with no transport.
    let lt_x0 = c.lt_of(k, x, c.zero);
    let lt_0x = c.lt_of(k, c.zero, x);
    let elim = k.const_(lg.or_elim, vec![]);
    let proof = t_app(k, elim, &[lt_x0, lt_0x, goal, h, branch_neg, branch_pos]);

    let value = lam_over(k, H1_FV, h_ty, proof);
    let value = lam_over(k, X_FV, c.creal, value);
    let ty = arrow(k, h_ty, goal);
    let ty = pi_over(k, X_FV, c.creal, ty);

    k.add_declaration(Declaration::Theorem {
        name: p.field_s.mul_inv_ex,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.fieldS : AlgS.Field` — `ofCommRing` at `CReal.commRingS`, the
/// existing `Apart` and its three existing laws, plus this module's two.
fn declare_field_s(k: &mut Kernel, p: &CRealPrelude, a: &Algs) -> Result<(), KernelError> {
    let ring = k.const_(p.comm_ring_s, vec![]);
    let args = [
        p.apart,
        p.apart_symm,
        p.apart_cotrans,
        p.field_s.apart_compat,
        p.field_s.mul_inv_ex,
        p.field_s.one_apart_zero,
    ];
    let of_c = k.const_(a.of_comm_ring, vec![]);
    let mut value = k.app(of_c, ring);
    for n in args {
        let t = k.const_(n, vec![]);
        value = k.app(value, t);
    }
    let ty = k.const_(a.field_ind, vec![]);
    k.add_declaration(Declaration::Definition {
        name: p.field_s.field_s,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

/// The `STEP_DISPATCH` entry: declare `CReal.fieldS` and its four supports.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means
/// [`Kernel::add_declaration`] **refused** a proof term.
pub(super) fn declare_field_s_all(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let p = &p;
    let k = d.kernel();
    let a = algs(k);
    declare_apart_compat(k, p)?;
    declare_one_apart_zero(k, p)?;
    declare_pos_of_neg_lt_zero(k, p)?;
    declare_mul_inv_ex(k, p, &a)?;
    declare_field_s(k, p, &a)
}

#[cfg(test)]
mod field_setoid_instance_tests {
    use super::*;
    use crate::creal::build_creal_prelude;

    /// **ℝ is a field.** Every declaration is present and `CReal.fieldS`'s
    /// type is `AlgS.Field` — read from the environment, not from source.
    #[test]
    fn creal_is_a_field_over_the_setoid_spine() {
        let mut k = Kernel::new();
        let p = build_creal_prelude(&mut k).expect("creal prelude must build");
        for n in p.field_s.all() {
            assert!(
                k.environment().get(n).is_some(),
                "{n:?} missing from the environment"
            );
        }
        let decl = k
            .environment()
            .get(p.field_s.field_s)
            .expect("must exist")
            .clone();
        let Declaration::Definition { ty, .. } = decl else {
            panic!("CReal.fieldS must be a Definition")
        };
        assert_eq!(
            k.render_lean(ty).trim(),
            "AlgS.Field",
            "CReal.fieldS must be an AlgS.Field"
        );
    }

    /// **The headline claim**, read from `Kernel::axiom_footprint`.
    #[test]
    fn the_creal_field_instance_is_axiom_free() {
        let mut k = Kernel::new();
        let p = build_creal_prelude(&mut k).expect("creal prelude must build");
        for n in p.field_s.all() {
            let fp = k.axiom_footprint(n);
            assert!(
                fp.is_empty(),
                "{n:?} axiom footprint must be empty, got {} entries",
                fp.len()
            );
        }
    }

    /// The four supports are `Theorem`s, so the kernel checked their proof
    /// terms. `mulInvEx` in particular cannot be a stub.
    #[test]
    fn the_supports_are_checked_theorems() {
        let mut k = Kernel::new();
        let p = build_creal_prelude(&mut k).expect("creal prelude must build");
        for n in [
            p.field_s.apart_compat,
            p.field_s.one_apart_zero,
            p.field_s.pos_of_neg_lt_zero,
            p.field_s.mul_inv_ex,
        ] {
            let decl = k.environment().get(n).expect("must exist").clone();
            assert!(
                matches!(decl, Declaration::Theorem { .. }),
                "{n:?} must be a Theorem"
            );
        }
        let decl = k
            .environment()
            .get(p.field_s.mul_inv_ex)
            .expect("must exist")
            .clone();
        let Declaration::Theorem { ty, .. } = decl else {
            panic!("mulInvEx must be a Theorem")
        };
        let rendered = k.render_lean(ty);
        println!("CReal.mulInvEx : {rendered}");
        assert!(
            rendered.contains("CReal.Apart"),
            "the hypothesis must be APARTNESS, not a disequality: {rendered}"
        );
        assert!(
            rendered.contains("Exists"),
            "the inverse must be EXISTENTIAL: {rendered}"
        );
    }

    /// **Evaluation test for the instance.** The `AlgS.Field` selectors at
    /// `CReal.fieldS` must reduce to `CReal`'s own constants, and `apart` must
    /// be `CReal.Apart` and NOT `CReal.Equiv`. A `fieldS` built with its
    /// arguments in a different order would still have type `AlgS.Field`.
    #[test]
    fn the_creal_field_selectors_reduce_to_creals_own_constants() {
        let mut k = Kernel::new();
        let p = build_creal_prelude(&mut k).expect("creal prelude must build");
        let anon = k.anon();
        let algs = k.name_str(anon, "AlgS");
        let field = k.name_str(algs, "Field");
        let field_s = k.const_(p.field_s.field_s, vec![]);

        for (suffix, target) in [
            ("carrier", p.creal),
            ("equiv", p.equiv),
            ("zero", p.zero),
            ("one", p.one),
            ("mul", p.mul),
            ("neg", p.neg),
            ("apart", p.apart),
            ("apartSymm", p.apart_symm),
            ("apartCotrans", p.apart_cotrans),
            ("mulInvEx", p.field_s.mul_inv_ex),
        ] {
            let selname = k.name_str(field, suffix);
            let sel = k.const_(selname, vec![]);
            let lhs = k.app(sel, field_s);
            let rhs = k.const_(target, vec![]);
            assert!(
                k.def_eq(lhs, rhs),
                "AlgS.Field.{suffix} CReal.fieldS must reduce to {target:?}"
            );
        }

        // Apartness is DATA, not the negation of the equivalence.
        let selname = k.name_str(field, "apart");
        let sel = k.const_(selname, vec![]);
        let lhs = k.app(sel, field_s);
        let equiv = k.const_(p.equiv, vec![]);
        assert!(
            !k.def_eq(lhs, equiv),
            "AlgS.Field.apart CReal.fieldS must not be CReal.Equiv"
        );
    }

    /// `AlgS.Field.mul_left_cancel` — the generic field theorem — really
    /// applies at `CReal.fieldS`, which is what having the instance is for.
    #[test]
    fn the_generic_field_cancellation_applies_at_creal() {
        let mut k = Kernel::new();
        let p = build_creal_prelude(&mut k).expect("creal prelude must build");
        let anon = k.anon();
        let algs = k.name_str(anon, "AlgS");
        let field = k.name_str(algs, "Field");
        let cancel = k.name_str(field, "mul_left_cancel");
        let c = k.const_(cancel, vec![]);
        let fs = k.const_(p.field_s.field_s, vec![]);
        let applied = k.app(c, fs);
        let ty = k
            .infer(applied)
            .expect("AlgS.Field.mul_left_cancel must apply at CReal.fieldS");
        let rendered = k.render_lean(ty);
        println!("AlgS.Field.mul_left_cancel CReal.fieldS : {rendered}");
        assert!(
            rendered.contains("CReal"),
            "the instantiated type must be about CReal, got: {rendered}"
        );
    }

    /// **Negative control.** The negative branch of `mulInvEx` needs
    /// `pos_of_neg_lt_zero` to flip the sign; using the hypothesis `lt zero x`
    /// where `lt x zero` belongs — the two arguments swapped, one small change
    /// — must be refused.
    #[test]
    fn control_pos_of_neg_lt_zero_needs_the_negative_hypothesis() {
        let mut k = Kernel::new();
        let p = build_creal_prelude(&mut k).expect("creal prelude must build");
        let c = cctx(&mut k, &p);
        let x = k.fvar(98_000);
        // MUTATION: the hypothesis is `0 < x`, not `x < 0`.
        let wrong_ty = c.lt_of(&mut k, c.zero, x);
        let h = k.fvar(98_001);
        let applied = {
            let t = k.const_(p.field_s.pos_of_neg_lt_zero, vec![]);
            t_app(&mut k, t, &[x, h])
        };
        let nx = k.app(c.neg, x);
        let concl = c.lt_of(&mut k, c.zero, nx);
        let value = lam_over(&mut k, 98_001, wrong_ty, applied);
        let value = lam_over(&mut k, 98_000, c.creal, value);
        let ty = arrow(&mut k, wrong_ty, concl);
        let ty = pi_over(&mut k, 98_000, c.creal, ty);
        let ns = k.name_str(p.creal, "FieldSControl");
        let name = k.name_str(ns, "pos_of_neg_wrong_side");
        let got = k.add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            got.is_err(),
            "`0 < x` must not be accepted where `x < 0` is required"
        );
        // Positive twin.
        assert!(
            k.environment().get(p.field_s.pos_of_neg_lt_zero).is_some(),
            "the real CReal.pos_of_neg_lt_zero must be present"
        );
    }
}

#[cfg(test)]
mod field_setoid_inventory_tests {
    use crate::Kernel;
    use crate::creal::build_creal_prelude;
    use crate::env::Declaration;

    /// **The inventory for ADR-1627's fact ledger entries.** Prints every
    /// declaration this ADR records, as `FIELD-INVENTORY|<name>|<rendered
    /// type>`, read from `Kernel::environment` — so a fact's
    /// `formal.statement` is transcribed from the KERNEL and never from
    /// source text or from memory.
    ///
    /// The assertion is that every name resolves and renders non-empty, so the
    /// test cannot pass by printing nothing; run with `--nocapture` to read it.
    #[test]
    fn adr_1627_declaration_inventory() {
        let mut k = Kernel::new();
        build_creal_prelude(&mut k).expect("creal prelude must build");
        let anon = k.anon();
        let names: &[&str] = &[
            "AlgS.Field.toCommRing",
            "AlgS.Field.ofCommRing",
            "AlgS.Field.IsTight",
            "AlgS.Field.apart_irrefl",
            "AlgS.Field.apart_left_congr",
            "AlgS.Field.apart_right_congr",
            "AlgS.Field.inv_unique",
            "AlgS.Field.mul_left_cancel",
            "AlgS.mul_neg_right",
            "AlgS.VectorSpace.IsVectorSpace",
            "AlgS.VectorSpace.smul_left_cancel",
            "AlgS.VectorSpace.solve_smul",
            "AlgS.VectorSpace.basis_zero_unique",
            "Rat.apart",
            "Rat.apart_cotrans",
            "Rat.mulInvEx",
            "Rat.fieldS",
            "Rat.fieldS_isTight",
            "Rat.vectorSpaceS",
            "Rat.linComb_eq_sumRange",
            "CReal.apart_compat",
            "CReal.one_apart_zero",
            "CReal.pos_of_neg_lt_zero",
            "CReal.mulInvEx",
            "CReal.fieldS",
        ];
        let mut printed = 0usize;
        for dotted in names {
            let mut n = anon;
            for part in dotted.split('.') {
                n = k.name_str(n, part);
            }
            let decl = k
                .environment()
                .get(n)
                .unwrap_or_else(|| panic!("{dotted} missing from the environment"))
                .clone();
            let ty = match &decl {
                Declaration::Definition { ty, .. } | Declaration::Theorem { ty, .. } => *ty,
                _ => panic!("{dotted}: unexpected declaration kind"),
            };
            let rendered = k.render_lean(ty);
            assert!(!rendered.trim().is_empty(), "{dotted} rendered empty");
            let fp = k.axiom_footprint(n);
            assert!(fp.is_empty(), "{dotted} footprint must be empty");
            println!("FIELD-INVENTORY|{dotted}|{rendered}");
            printed += 1;
        }
        assert_eq!(printed, names.len(), "every name must have printed");
    }
}

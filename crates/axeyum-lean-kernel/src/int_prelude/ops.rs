//! The reusable proof-construction layer for the **constructed** integer
//! development: [`IntDev`].
//!
//! `IntDev` implements [`NatOps`], so every natural-number term builder, `Eq`
//! combinator, `Nat.rec` induction helper and declaration helper is available
//! unchanged; the inherent methods here add the `Int` counterparts (`Int`-typed
//! `Eq`, `Int.rec` case analysis, the ring/order operations) and the two
//! *cross-carrier* combinators a construction of `ℤ` over `ℕ` actually needs:
//! transporting a `Nat` equation into an `Int` equation, and transporting a
//! `Nat` equation into an arbitrary `Prop`.

use super::IntPrelude;
use crate::BinderInfo;
use crate::Kernel;
use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::name::NameId;
use crate::nat_prelude::{NatOps, NatState};

/// Which `Int` constructor a case-analysis branch is under.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Shape {
    /// `Int.ofNat n` — the non-negative branch.
    OfNat,
    /// `Int.negSucc n` — the branch for `-(n+1)`.
    NegSucc,
}

/// One case-analysis branch: the constructor and the `Nat` field bound in it.
pub(crate) type Branch = (Shape, ExprId);

/// A development over a kernel that already carries (or is in the middle of
/// declaring) the integer prelude.
pub(crate) struct IntDev<'k> {
    kernel: &'k mut Kernel,
    state: NatState,
    int: IntPrelude,
    int_ty: ExprId,
}

impl<'k> IntDev<'k> {
    /// A development over `kernel` for the interned (not necessarily yet
    /// declared) names in `int`.
    pub(crate) fn new(kernel: &'k mut Kernel, int: IntPrelude) -> Self {
        let state = NatState::new(kernel, int.nat);
        let int_ty = kernel.const_(int.z, vec![]);
        Self {
            kernel,
            state,
            int,
            int_ty,
        }
    }

    /// The interned integer names (a `Copy` snapshot).
    pub(crate) fn int(&self) -> IntPrelude {
        self.int
    }

    /// The expression `Int`.
    pub(crate) fn int_ty(&self) -> ExprId {
        self.int_ty
    }

    // --- carrier terms -------------------------------------------------------

    /// `Int.ofNat n`.
    pub(crate) fn of_nat(&mut self, n: ExprId) -> ExprId {
        let f = self.int.of_nat;
        self.const_app(f, &[n])
    }

    /// `Int.negSucc n` (the integer `-(n+1)`).
    pub(crate) fn neg_succ(&mut self, n: ExprId) -> ExprId {
        let f = self.int.neg_succ;
        self.const_app(f, &[n])
    }

    /// Rebuild the constructor application a [`Branch`] stands for.
    pub(crate) fn branch_term(&mut self, branch: Branch) -> ExprId {
        match branch {
            (Shape::OfNat, n) => self.of_nat(n),
            (Shape::NegSucc, n) => self.neg_succ(n),
        }
    }

    /// `Int.zero`.
    pub(crate) fn izero(&mut self) -> ExprId {
        let n = self.int.zero;
        self.kernel.const_(n, vec![])
    }

    /// `Int.one`.
    pub(crate) fn ione(&mut self) -> ExprId {
        let n = self.int.one;
        self.kernel.const_(n, vec![])
    }

    /// `Int.add a b`.
    pub(crate) fn iadd(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let f = self.int.add;
        self.const_app(f, &[a, b])
    }

    /// `Int.mul a b`.
    pub(crate) fn imul(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let f = self.int.mul;
        self.const_app(f, &[a, b])
    }

    /// `Int.pow a n` — `a` raised to the natural exponent `n`.
    pub(crate) fn ipow(&mut self, a: ExprId, n: ExprId) -> ExprId {
        let f = self.int.pow;
        self.const_app(f, &[a, n])
    }

    /// `Int.neg a`.
    pub(crate) fn ineg(&mut self, a: ExprId) -> ExprId {
        let f = self.int.neg;
        self.const_app(f, &[a])
    }

    /// `Int.sub a b`, i.e. `a + (-b)` under the `Int.sub` definition.
    pub(crate) fn isub(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let f = self.int.sub;
        self.const_app(f, &[a, b])
    }

    /// `Int.ediv a b` — the Euclidean ("E-rounding") quotient.
    pub(crate) fn iediv(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let f = self.int.ediv;
        self.const_app(f, &[a, b])
    }

    /// `Int.emod a b` — the Euclidean ("E-rounding") remainder.
    pub(crate) fn iemod(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let f = self.int.emod;
        self.const_app(f, &[a, b])
    }

    /// `Int.negOfNat n` — the integer `-n`, for a natural `n`.
    pub(crate) fn neg_of_nat(&mut self, n: ExprId) -> ExprId {
        let f = self.int.neg_of_nat;
        self.const_app(f, &[n])
    }

    /// `Int.subNatNat m n` — the normalized integer `m - n`.
    pub(crate) fn sub_nat_nat(&mut self, m: ExprId, n: ExprId) -> ExprId {
        let f = self.int.sub_nat_nat;
        self.const_app(f, &[m, n])
    }

    /// `Int.le a b`.
    pub(crate) fn ile(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let f = self.int.le;
        self.const_app(f, &[a, b])
    }

    /// `Int.lt a b`.
    pub(crate) fn ilt(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let f = self.int.lt;
        self.const_app(f, &[a, b])
    }

    // --- Eq at Int -----------------------------------------------------------

    /// `Eq.{1} Int a b` (the carrier is `Sort 1`, so the universe argument is 1).
    pub(crate) fn ieq(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let one = self.level_one();
        let name = self.int.logic.eq;
        let eq = self.kernel.const_(name, vec![one]);
        let int_ty = self.int_ty;
        self.apply(eq, &[int_ty, a, b])
    }

    /// `Eq.refl.{1} Int a`.
    pub(crate) fn irefl(&mut self, a: ExprId) -> ExprId {
        let one = self.level_one();
        let name = self.int.logic.eq_refl;
        let refl = self.kernel.const_(name, vec![one]);
        let int_ty = self.int_ty;
        self.apply(refl, &[int_ty, a])
    }

    /// `Eq.rec.{0,1} Int p motive refl_case q h`.
    pub(crate) fn itransport(
        &mut self,
        p: ExprId,
        motive: ExprId,
        refl_case: ExprId,
        q: ExprId,
        h: ExprId,
    ) -> ExprId {
        let zero = self.kernel.level_zero();
        let one = self.level_one();
        let name = self.int.logic.eq_rec;
        let rec = self.kernel.const_(name, vec![zero, one]);
        let int_ty = self.int_ty;
        self.apply(rec, &[int_ty, p, motive, refl_case, q, h])
    }

    /// `fun (x : Int) (_ : Eq Int a x) => body(x)`.
    pub(crate) fn ieq_motive(
        &mut self,
        a: ExprId,
        body: &dyn Fn(&mut Self, ExprId) -> ExprId,
    ) -> ExprId {
        let x_fv = self.fresh_fvar();
        let x = self.kernel.fvar(x_fv);
        let concl = body(self, x);
        let hyp = self.ieq(a, x);
        let anon = self.anon_name();
        let inner = self.kernel.lam(anon, hyp, concl, BinderInfo::Default);
        let int_ty = self.int_ty;
        self.lam_fv(x_fv, int_ty, inner)
    }

    /// `h : Eq Int a b  ⊢  Eq Int b a`.
    pub(crate) fn isymm(&mut self, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
        let motive = self.ieq_motive(a, &|d, x| d.ieq(x, a));
        let refl_case = self.irefl(a);
        self.itransport(a, motive, refl_case, b, h)
    }

    /// `h1 : Eq Int a b`, `h2 : Eq Int b c  ⊢  Eq Int a c`.
    pub(crate) fn itrans(
        &mut self,
        a: ExprId,
        b: ExprId,
        c: ExprId,
        h1: ExprId,
        h2: ExprId,
    ) -> ExprId {
        let motive = self.ieq_motive(b, &|d, x| d.ieq(a, x));
        self.itransport(b, motive, h1, c, h2)
    }

    /// Chain `Eq Int start …` through `(next, step)` pairs, returning the final
    /// right-hand side and the composed proof.
    ///
    /// Every intermediate term only has to be **definitionally** the previous
    /// step's right-hand side, which is what makes the branch scripts readable:
    /// a step may be stated at whichever ι-reduct of the term is convenient.
    pub(crate) fn ichain(&mut self, start: ExprId, steps: &[(ExprId, ExprId)]) -> (ExprId, ExprId) {
        let mut current = start;
        let mut proof = self.irefl(start);
        for &(next, step) in steps {
            proof = self.itrans(start, current, next, proof, step);
            current = next;
        }
        (current, proof)
    }

    /// Congruence at `Int`: `h : Eq Int a b  ⊢  Eq Int (f a) (f b)`.
    pub(crate) fn icongr(
        &mut self,
        a: ExprId,
        b: ExprId,
        h: ExprId,
        f: &dyn Fn(&mut Self, ExprId) -> ExprId,
    ) -> ExprId {
        let fa = f(self, a);
        let motive = self.ieq_motive(a, &|d, x| {
            let fx = f(d, x);
            d.ieq(fa, fx)
        });
        let refl_case = self.irefl(fa);
        self.itransport(a, motive, refl_case, b, h)
    }

    /// From `h : Eq Nat a b` and a proof of `motive a`, derive `motive b` — the
    /// `Nat`-indexed rewrite the `subNatNat` scripts run on, where the equation
    /// is between naturals but the proposition being moved is about integers.
    pub(crate) fn nat_rewrite(
        &mut self,
        a: ExprId,
        b: ExprId,
        h: ExprId,
        proof: ExprId,
        motive: &dyn Fn(&mut Self, ExprId) -> ExprId,
    ) -> ExprId {
        let built = self.eq_motive(a, motive);
        self.transport(a, built, proof, b, h)
    }

    /// From `h : Eq Int p q` and a proof of `motive p`, derive `motive q`.
    ///
    /// Both directions of constructor reasoning go through this: injectivity
    /// (`motive y := Eq Nat (magnitude p) (magnitude y)`) and discrimination
    /// (`motive y := <a Prop that is True on one constructor and False on the
    /// other>`).
    pub(crate) fn int_eq_rewrite(
        &mut self,
        p: ExprId,
        q: ExprId,
        h: ExprId,
        proof: ExprId,
        motive: &dyn Fn(&mut Self, ExprId) -> ExprId,
    ) -> ExprId {
        let built = self.ieq_motive(p, motive);
        self.itransport(p, built, proof, q, h)
    }

    // --- cross-carrier transport --------------------------------------------

    /// From `h : Eq Nat a b`, derive `Eq Int (f a) (f b)` for any `Int`-valued
    /// context `f` over a natural.
    ///
    /// This is the workhorse of the construction: every algebraic law of `ℤ`
    /// that lives inside one constructor is exactly a law of `ℕ` pushed through
    /// `Int.ofNat`, `Int.negSucc`, or `Int.negOfNat` by this combinator.
    pub(crate) fn nat_eq_to_int(
        &mut self,
        a: ExprId,
        b: ExprId,
        h: ExprId,
        f: &dyn Fn(&mut Self, ExprId) -> ExprId,
    ) -> ExprId {
        let fa = f(self, a);
        let motive = self.eq_motive(a, &|d, x| {
            let fx = f(d, x);
            d.ieq(fa, fx)
        });
        let refl_case = self.irefl(fa);
        self.transport(a, motive, refl_case, b, h)
    }

    // --- propositional plumbing ---------------------------------------------

    /// `True.intro`.
    pub(crate) fn true_intro(&mut self) -> ExprId {
        let n = self.int.logic.true_intro;
        self.kernel.const_(n, vec![])
    }

    /// `True`.
    pub(crate) fn true_ty(&mut self) -> ExprId {
        let n = self.int.logic.true_;
        self.kernel.const_(n, vec![])
    }

    /// `False`.
    pub(crate) fn false_ty(&mut self) -> ExprId {
        let n = self.int.logic.false_;
        self.kernel.const_(n, vec![])
    }

    /// `Not p`.
    pub(crate) fn not(&mut self, p: ExprId) -> ExprId {
        let n = self.int.logic.not;
        self.const_app(n, &[p])
    }

    /// `And p q`.
    pub(crate) fn and(&mut self, p: ExprId, q: ExprId) -> ExprId {
        let n = self.int.logic.and;
        self.const_app(n, &[p, q])
    }

    /// `Or p q`.
    pub(crate) fn or(&mut self, p: ExprId, q: ExprId) -> ExprId {
        let n = self.int.logic.or;
        self.const_app(n, &[p, q])
    }

    /// `Or.inl p q proof : Or p q`.
    pub(crate) fn or_inl(&mut self, p: ExprId, q: ExprId, proof: ExprId) -> ExprId {
        let n = self.int.logic.or_inl;
        self.const_app(n, &[p, q, proof])
    }

    /// `Or.inr p q proof : Or p q`.
    pub(crate) fn or_inr(&mut self, p: ExprId, q: ExprId, proof: ExprId) -> ExprId {
        let n = self.int.logic.or_inr;
        self.const_app(n, &[p, q, proof])
    }

    /// `False.rec.{0} (fun _ => target) proof : target`.
    pub(crate) fn absurd(&mut self, target: ExprId, proof: ExprId) -> ExprId {
        let zero = self.kernel.level_zero();
        let false_rec = self.int.logic.false_rec;
        let rec = self.kernel.const_(false_rec, vec![zero]);
        let false_ty = self.false_ty();
        let anon = self.anon_name();
        let motive = self.kernel.lam(anon, false_ty, target, BinderInfo::Default);
        self.apply(rec, &[motive, proof])
    }

    /// The left projection of `proof : And left right`.
    pub(crate) fn and_left(&mut self, left: ExprId, right: ExprId, proof: ExprId) -> ExprId {
        let and_ty = self.and(left, right);
        let motive = {
            let pair_fv = self.fresh_fvar();
            self.lam_fv(pair_fv, and_ty, left)
        };
        let minor = {
            let left_fv = self.fresh_fvar();
            let left_proof = self.kernel.fvar(left_fv);
            let right_fv = self.fresh_fvar();
            let with_right = self.lam_fv(right_fv, right, left_proof);
            self.lam_fv(left_fv, left, with_right)
        };
        let zero = self.kernel.level_zero();
        let and_rec = self.int.logic.and_rec;
        let rec = self.kernel.const_(and_rec, vec![zero]);
        self.apply(rec, &[left, right, motive, minor, proof])
    }

    /// The right projection of `proof : And left right`.
    pub(crate) fn and_right(&mut self, left: ExprId, right: ExprId, proof: ExprId) -> ExprId {
        let and_ty = self.and(left, right);
        let motive = {
            let pair_fv = self.fresh_fvar();
            self.lam_fv(pair_fv, and_ty, right)
        };
        let minor = {
            let left_fv = self.fresh_fvar();
            let right_fv = self.fresh_fvar();
            let right_proof = self.kernel.fvar(right_fv);
            let with_right = self.lam_fv(right_fv, right, right_proof);
            self.lam_fv(left_fv, left, with_right)
        };
        let zero = self.kernel.level_zero();
        let and_rec = self.int.logic.and_rec;
        let rec = self.kernel.const_(and_rec, vec![zero]);
        self.apply(rec, &[left, right, motive, minor, proof])
    }

    /// Case-eliminate `proof : Or left right` into `target`, given both
    /// branch builders.
    pub(crate) fn or_elim(
        &mut self,
        left: ExprId,
        right: ExprId,
        target: ExprId,
        proof: ExprId,
        on_left: &dyn Fn(&mut Self, ExprId) -> ExprId,
        on_right: &dyn Fn(&mut Self, ExprId) -> ExprId,
    ) -> ExprId {
        let or_ty = self.or(left, right);
        let motive = {
            let disjunction_fv = self.fresh_fvar();
            self.lam_fv(disjunction_fv, or_ty, target)
        };
        let minor_left = {
            let fv = self.fresh_fvar();
            let hypothesis = self.kernel.fvar(fv);
            let body = on_left(self, hypothesis);
            self.lam_fv(fv, left, body)
        };
        let minor_right = {
            let fv = self.fresh_fvar();
            let hypothesis = self.kernel.fvar(fv);
            let body = on_right(self, hypothesis);
            self.lam_fv(fv, right, body)
        };
        // `Or` is a `Prop` with two non-subsingleton constructors, so its
        // recursor eliminates only into `Prop` and carries **no** universe
        // parameter — unlike `And.rec`, which takes one.
        let or_rec = self.int.logic.or_rec;
        let rec = self.kernel.const_(or_rec, vec![]);
        self.apply(rec, &[left, right, motive, minor_left, minor_right, proof])
    }

    // --- declaration plumbing ------------------------------------------------

    /// Declare `axiom name : ∀ (x_0 … x_{arity-1} : Int), stmt` — an integer law
    /// this development has **not** derived, asserted outright.
    ///
    /// # Errors
    ///
    /// Returns the trusted gate's rejection (a malformed statement, or a name
    /// Declare `theorem name : ∀ (x_0 … x_{arity-1} : Int), stmt := fun … => proof`.
    ///
    /// # Errors
    ///
    /// Returns the trusted gate's rejection — the kernel re-checks `proof`
    /// against `stmt` inside `add_declaration`, so an `Err` means the proof was
    /// **refused**.
    pub(crate) fn int_theorem(
        &mut self,
        name: NameId,
        arity: usize,
        build: &dyn Fn(&mut Self, &[ExprId]) -> (ExprId, ExprId),
    ) -> Result<NameId, KernelError> {
        let int_ty = self.int_ty;
        let fvs: Vec<u64> = (0..arity).map(|_| self.fresh_fvar()).collect();
        let vars: Vec<ExprId> = fvs.iter().map(|&f| self.kernel.fvar(f)).collect();
        let (stmt, proof) = build(self, &vars);
        let mut ty = stmt;
        let mut value = proof;
        for &fv in fvs.iter().rev() {
            ty = self.pi_fv(fv, int_ty, ty);
            value = self.lam_fv(fv, int_ty, value);
        }
        self.kernel.add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })?;
        Ok(name)
    }
}

impl NatOps for IntDev<'_> {
    fn kernel(&mut self) -> &mut Kernel {
        self.kernel
    }

    fn nat_state(&mut self) -> &mut NatState {
        &mut self.state
    }
}

/// Eliminate `witness : Exists Nat predicate` into `target`, given a
/// `minor : ∀ (x : Nat), predicate x → target`.
///
/// `Exists` is a `Prop` with one non-subsingleton constructor, so its recursor
/// eliminates only into `Prop` and carries exactly one universe parameter — the
/// one of the *quantified* type, here `Nat : Sort 1`.
pub(crate) fn exists_elim(
    d: &mut IntDev<'_>,
    predicate: ExprId,
    target: ExprId,
    witness: ExprId,
    minor: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let exists_name = d.int().logic.exists_;
    let exists = d.kernel().const_(exists_name, vec![one]);
    let exists_ty = d.apply(exists, &[nat, predicate]);
    let motive = {
        let fv = d.fresh_fvar();
        d.lam_fv(fv, exists_ty, target)
    };
    let rec_name = d.int().logic.exists_rec;
    let rec = d.kernel().const_(rec_name, vec![one]);
    d.apply(rec, &[nat, predicate, motive, minor, witness])
}

/// Prove `stmt(targets)` by exhaustive `Int.rec` case analysis on every element
/// of `targets`, calling `case` once per constructor combination.
///
/// `stmt` receives the argument list with already-split positions replaced by
/// their constructor applications, and must build the *statement* for those
/// arguments; `case` receives one [`Branch`] per position and must build the
/// proof for that combination. With `n` targets this generates `2^n` branches.
pub(crate) fn case_split(
    d: &mut IntDev<'_>,
    targets: &[ExprId],
    stmt: &dyn Fn(&mut IntDev<'_>, &[ExprId]) -> ExprId,
    case: &dyn Fn(&mut IntDev<'_>, &[Branch]) -> ExprId,
) -> ExprId {
    let mut done: Vec<Branch> = Vec::with_capacity(targets.len());
    split_at(d, targets, &mut done, stmt, case)
}

fn split_at(
    d: &mut IntDev<'_>,
    targets: &[ExprId],
    done: &mut Vec<Branch>,
    stmt: &dyn Fn(&mut IntDev<'_>, &[ExprId]) -> ExprId,
    case: &dyn Fn(&mut IntDev<'_>, &[Branch]) -> ExprId,
) -> ExprId {
    let depth = done.len();
    if depth == targets.len() {
        return case(d, done);
    }
    // The statement at this depth, as a function of the position being split.
    let arguments = |d: &mut IntDev<'_>, done: &[Branch], hole: ExprId| -> Vec<ExprId> {
        let mut args = Vec::with_capacity(targets.len());
        for (index, &target) in targets.iter().enumerate() {
            match index.cmp(&done.len()) {
                core::cmp::Ordering::Less => {
                    let term = d.branch_term(done[index]);
                    args.push(term);
                }
                core::cmp::Ordering::Equal => args.push(hole),
                core::cmp::Ordering::Greater => args.push(target),
            }
        }
        args
    };
    let motive = |d: &mut IntDev<'_>, x: ExprId| {
        let args = arguments(d, done, x);
        stmt(d, &args)
    };
    let target = targets[depth];
    let int_ty = d.int_ty();
    let nat = d.nat_ty();
    let motive_term = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let body = motive(d, x);
        d.lam_fv(x_fv, int_ty, body)
    };
    let minor_of_nat = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        done.push((Shape::OfNat, n));
        let body = split_at(d, targets, done, stmt, case);
        done.pop();
        d.lam_fv(n_fv, nat, body)
    };
    let minor_neg_succ = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        done.push((Shape::NegSucc, n));
        let body = split_at(d, targets, done, stmt, case);
        done.pop();
        d.lam_fv(n_fv, nat, body)
    };
    let zero = d.kernel().level_zero();
    let rec_name = d.int().rec;
    let rec = d.kernel().const_(rec_name, vec![zero]);
    d.apply(rec, &[motive_term, minor_of_nat, minor_neg_succ, target])
}

//! **Slice 4 — the last piece of `F:excluded-middle-not-intuitionistic`**:
//! soundness of the `Provable` natural-deduction relation
//! (`ipc_provable.rs`) with respect to the 3-element Gödel/Łukasiewicz
//! Heyting-chain semantics (`ipc_heyting.rs`, `ipc_eval.rs`), and the
//! contraposition that closes the fact:
//!
//! ```text
//! ipc_excluded_middle_not_provable : Not (Provable FormulaList.nil (or_ (var 0) (imp (var 0) bot)))
//! ```
//!
//! ## The statement soundness is proved in, and why it is not the obvious one
//!
//! The obvious statement — "if every formula in the context evaluates to the
//! chain's top, so does the goal" — is **not** a statement an induction on the
//! derivation can carry, and the obstruction is `imp_intro`.
//!
//! In the `imp_intro` case the induction hypothesis is about the *extended*
//! context `phi :: ctx`, so it says only: *if `eval phi v = 2` then
//! `eval psi v = 2`*. The goal is `himp3 (eval phi v) (eval psi v) = 2`, i.e.
//! `eval phi v <= eval psi v`, and nothing in that hypothesis constrains the
//! case where `eval phi v` is the chain's **middle** element `1`. The
//! hypothesis is silent exactly where the goal needs information, which is the
//! whole reason the chain has three elements rather than two.
//!
//! (Whether the sat-shaped statement happens to be *true* for this particular
//! algebra is a separate question from whether it carries an induction. A
//! brute-force search over every formula of depth <= 2 in two variables found
//! no counterexample to it, so it may well be true — but no induction on
//! `Provable` establishes it, and this file does not claim it.)
//!
//! The statement that does carry the induction is the standard algebraic one,
//! over the **meet of the context**:
//!
//! ```text
//! ipc_ctx_meet FormulaList.nil        v = 2
//! ipc_ctx_meet (cons a l)             v = meet3 (ipc_eval a v) (ipc_ctx_meet l v)
//!
//! ipc_soundness : forall ctx phi, Provable ctx phi
//!               -> forall v, Le (ipc_ctx_meet ctx v) (ipc_eval phi v)
//! ```
//!
//! Read semantically: *the value of the context is below the value of
//! anything derivable from it*. `imp_intro` then goes through by residuation
//! (`meet3 a m <= b` implies `m <= himp3 a b`), and `or_elim` by the chain's
//! linearity. Both were hand-checked at every point of `{0,…,4}` before any
//! Rust was written, which is also how the one genuine side condition was
//! found: residuation needs `m <= 2`, and it **fails** at `m = 3`
//! (`meet3 3 1 = 1 <= 1` but `3 <= himp3 1 1 = 2` is false). That side
//! condition is discharged by [`declare_ctx_meet_le_top`], since
//! `ipc_ctx_meet` starts at `2` and only ever takes meets.
//!
//! ## Context satisfaction is still built, and bridged
//!
//! [`declare_sat`] builds the requested `ipc_sat : FormulaList -> (Nat -> Nat)
//! -> Prop` by `FormulaList.rec` (`True` at `nil`, `And (Eq (eval a v) 2) …`
//! at `cons`), and [`declare_sat_le_ctx_meet`] bridges it:
//! `ipc_sat ctx v -> Le 2 (ipc_ctx_meet ctx v)`. Composing gives the
//! sat-shaped corollary [`declare_soundness_sat`], so nothing is lost by
//! running the induction on the meet instead.
//!
//! `ipc_sat` is a `Definition`, so the kernel admitting it proves only that it
//! is well-formed. It is pinned two ways: by evaluation at concrete arguments
//! (module tests), and — because a constantly-true `sat` would satisfy any
//! careless evaluation test and make the corollary vacuous — by the kernel
//! `Theorem` [`declare_sat_not_vacuous`], which **refutes**
//! `ipc_sat (cons (var 0) nil) (fun _ => 1)`.
//!
//! ## The eleven cases
//!
//! One minor premise of `Provable.rec` per constructor, each a one-line
//! application of a chain lemma proved above it:
//!
//! | rule | closed by |
//! | --- | --- |
//! | `ax_head` | `meet3_le_left` |
//! | `weaken` | `meet3_le_right` + `le_trans` |
//! | `and_intro` | `le_meet3` |
//! | `and_elim1` / `and_elim2` | `meet3_le_left` / `meet3_le_right` + `le_trans` |
//! | `or_intro1` / `or_intro2` | `le_join3_left` / `le_join3_right` + `le_trans` |
//! | `or_elim` | `or_elim_chain` (linearity) |
//! | `imp_intro` | `himp3_intro` (residuation) + `ctx_meet_le_top` |
//! | `imp_elim` | `himp3_elim` |
//! | `bot_elim` | `zero_le` + `le_trans` |
//!
//! ## Closing the fact
//!
//! `ipc_soundness nil pem_instance h (fun _ => 1)` has type
//! `Le (ipc_ctx_meet nil v) (ipc_eval pem_instance v)`, which the kernel
//! reduces to `Le 2 1` — `ipc_ctx_meet nil v` is `2` by ι, and
//! `ipc_eval pem_instance (fun _ => 1)` is `join3 1 (himp3 1 0) = join3 1 0 =
//! 1`, the same value `ipc_heyting_join_not_ne_top` already computes by the
//! direct route. `Nat.not_succ_le_self 1` refutes it, so the assumed
//! derivation yields `False`.
#![allow(clippy::similar_names)]

use crate::{
    BinderInfo, Declaration, ExprId, IpcProvablePrelude, KernelError, NameId, NatPrelude,
    ReducibilityHint, build_ipc_provable_prelude, build_nat_prelude, pem_instance,
};

/// Names produced by [`build_ipc_soundness_prelude`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IpcSoundnessPrelude {
    /// `FormulaList`, `Provable` and (through it) the `Formula` AST and the
    /// 3-element Heyting chain.
    pub provable: IpcProvablePrelude,
    /// `ipc_eval : Formula -> (Nat -> Nat) -> Nat` (slice 3, re-declared here
    /// so `Provable` and `ipc_eval` live in ONE kernel environment).
    pub eval: NameId,
    /// `ipc_ctx_meet : FormulaList -> (Nat -> Nat) -> Nat`.
    pub ctx_meet: NameId,
    /// `ipc_sat : FormulaList -> (Nat -> Nat) -> Prop`.
    pub sat: NameId,
    /// `ipc_le_of_ble_eq_false : ∀ a b, Eq Bool (Nat.ble a b) Bool.false -> Le b a`.
    pub le_of_ble_eq_false: NameId,
    /// `ipc_meet3_le_left : ∀ a b, Le (meet3 a b) a`.
    pub meet3_le_left: NameId,
    /// `ipc_meet3_le_right : ∀ a b, Le (meet3 a b) b`.
    pub meet3_le_right: NameId,
    /// `ipc_le_meet3 : ∀ a b c, Le c a -> Le c b -> Le c (meet3 a b)`.
    pub le_meet3: NameId,
    /// `ipc_le_join3_left : ∀ a b, Le a (join3 a b)`.
    pub le_join3_left: NameId,
    /// `ipc_le_join3_right : ∀ a b, Le b (join3 a b)`.
    pub le_join3_right: NameId,
    /// `ipc_meet_absorb_le : ∀ x m c, Le m x -> Le (meet3 x m) c -> Le m c`.
    pub meet_absorb_le: NameId,
    /// `ipc_or_elim_chain : ∀ a b m c, Le m (join3 a b) -> Le (meet3 a m) c
    /// -> Le (meet3 b m) c -> Le m c`.
    pub or_elim_chain: NameId,
    /// `ipc_himp3_intro : ∀ a b m, Le m 2 -> Le (meet3 a m) b -> Le m (himp3 a b)`.
    pub himp3_intro: NameId,
    /// `ipc_himp3_elim : ∀ a b m, Le m (himp3 a b) -> Le m a -> Le m b`.
    pub himp3_elim: NameId,
    /// `ipc_ctx_meet_le_top : ∀ l v, Le (ipc_ctx_meet l v) 2`.
    pub ctx_meet_le_top: NameId,
    /// `ipc_soundness : ∀ ctx phi, Provable ctx phi -> ∀ v,
    /// Le (ipc_ctx_meet ctx v) (ipc_eval phi v)`.
    pub soundness: NameId,
    /// `ipc_sat_le_ctx_meet : ∀ l v, ipc_sat l v -> Le 2 (ipc_ctx_meet l v)`.
    pub sat_le_ctx_meet: NameId,
    /// `ipc_soundness_sat : ∀ ctx phi, Provable ctx phi -> ∀ v,
    /// ipc_sat ctx v -> Le 2 (ipc_eval phi v)`.
    pub soundness_sat: NameId,
    /// `ipc_sat_not_vacuous : Not (ipc_sat (cons (var 0) nil) (fun _ => 1))`.
    pub sat_not_vacuous: NameId,
    /// `ipc_excluded_middle_not_provable :
    /// Not (Provable FormulaList.nil (or_ (var 0) (imp (var 0) bot)))`.
    pub pem_not_provable: NameId,
}

/// Build the whole slice-4 package on top of `ipc_provable.rs` and
/// `ipc_eval.rs`, registering every declaration through the trusted
/// [`crate::Kernel::add_declaration`] gate.
///
/// Note this re-declares `ipc_eval` itself rather than calling
/// [`crate::build_ipc_eval_prelude`]: both that builder and
/// [`crate::build_ipc_provable_prelude`] call `build_ipc_heyting_prelude`,
/// which is deliberately uncached, so calling both in one kernel would try to
/// declare `Formula` twice.
///
/// # Errors
///
/// Returns the [`KernelError`] from any of the underlying trusted gates if a
/// declaration fails to admit.
pub fn build_ipc_soundness_prelude(
    kernel: &mut crate::Kernel,
) -> Result<IpcSoundnessPrelude, KernelError> {
    let provable = build_ipc_provable_prelude(kernel)?;
    let nat = build_nat_prelude(kernel)?;
    let eval = crate::ipc_eval::declare_eval(kernel, &provable.heyting)?;
    // Placeholder until `ipc_ctx_meet` itself is declared, three lines below;
    // nothing reads `Dev::ctx_meet` before then.
    let anon = kernel.anon();

    let mut d = Dev {
        k: kernel,
        nat,
        p: provable,
        eval,
        ctx_meet: anon,
        next: 970_000,
    };

    let ctx_meet = declare_ctx_meet(&mut d)?;
    d.ctx_meet = ctx_meet;
    let sat = declare_sat(&mut d)?;

    let le_of_ble_eq_false = declare_le_of_ble_eq_false(&mut d)?;
    let meet3_le_left = declare_meet3_le_left(&mut d, le_of_ble_eq_false)?;
    let meet3_le_right = declare_meet3_le_right(&mut d)?;
    let le_meet3 = declare_le_meet3(&mut d)?;
    let le_join3_left = declare_le_join3_left(&mut d)?;
    let le_join3_right = declare_le_join3_right(&mut d, le_of_ble_eq_false)?;
    let meet_absorb_le = declare_meet_absorb_le(&mut d)?;
    let or_elim_chain = declare_or_elim_chain(&mut d, meet_absorb_le)?;
    let himp3_intro = declare_himp3_intro(&mut d)?;
    let himp3_elim = declare_himp3_elim(&mut d)?;
    let ctx_meet_le_top = declare_ctx_meet_le_top(&mut d, meet3_le_right)?;

    let lemmas = ChainLemmas {
        meet3_le_left,
        meet3_le_right,
        le_meet3,
        le_join3_left,
        le_join3_right,
        or_elim_chain,
        himp3_intro,
        himp3_elim,
        ctx_meet_le_top,
    };
    let soundness = declare_soundness(&mut d, &lemmas)?;
    let sat_le_ctx_meet = declare_sat_le_ctx_meet(&mut d, sat, le_meet3)?;
    let soundness_sat = declare_soundness_sat(&mut d, sat, soundness, sat_le_ctx_meet)?;
    let sat_not_vacuous = declare_sat_not_vacuous(&mut d, sat)?;
    let pem_not_provable = declare_pem_not_provable(&mut d, soundness)?;

    Ok(IpcSoundnessPrelude {
        provable,
        eval,
        ctx_meet,
        sat,
        le_of_ble_eq_false,
        meet3_le_left,
        meet3_le_right,
        le_meet3,
        le_join3_left,
        le_join3_right,
        meet_absorb_le,
        or_elim_chain,
        himp3_intro,
        himp3_elim,
        ctx_meet_le_top,
        soundness,
        sat_le_ctx_meet,
        soundness_sat,
        sat_not_vacuous,
        pem_not_provable,
    })
}

/// The nine chain lemmas the eleven soundness minors consume, gathered so
/// [`declare_soundness`] takes one argument instead of nine.
struct ChainLemmas {
    meet3_le_left: NameId,
    meet3_le_right: NameId,
    le_meet3: NameId,
    le_join3_left: NameId,
    le_join3_right: NameId,
    or_elim_chain: NameId,
    himp3_intro: NameId,
    himp3_elim: NameId,
    ctx_meet_le_top: NameId,
}

/// Term-building conveniences over the raw kernel, in the spirit of
/// `nat_prelude`'s `NatDev` but local to this file (that one is `pub(super)`
/// to `nat_prelude` and hardcodes `Nat` as the carrier of its `congr`/`refl`,
/// which is the wrong carrier for `Formula`/`FormulaList` terms anyway).
struct Dev<'k> {
    k: &'k mut crate::Kernel,
    nat: NatPrelude,
    p: IpcProvablePrelude,
    eval: NameId,
    ctx_meet: NameId,
    next: u64,
}

impl Dev<'_> {
    /// A fresh free variable, as `(id, expression)`. Ids are monotone so no
    /// two binders live at the same time can collide.
    fn fv(&mut self) -> (u64, ExprId) {
        self.next += 1;
        let id = self.next;
        (id, self.k.fvar(id))
    }

    fn c(&mut self, name: NameId) -> ExprId {
        self.k.const_(name, vec![])
    }

    fn apply(&mut self, mut function: ExprId, arguments: &[ExprId]) -> ExprId {
        for &argument in arguments {
            function = self.k.app(function, argument);
        }
        function
    }

    /// `name arg…`, for a constant with no universe parameters.
    fn capp(&mut self, name: NameId, arguments: &[ExprId]) -> ExprId {
        let function = self.c(name);
        self.apply(function, arguments)
    }

    /// `name.{levels} arg…`.
    fn capp_lvl(&mut self, name: NameId, levels: Vec<crate::LevelId>, args: &[ExprId]) -> ExprId {
        let function = self.k.const_(name, levels);
        self.apply(function, args)
    }

    fn lam_fv(&mut self, id: u64, ty: ExprId, body: ExprId) -> ExprId {
        let body = self.k.abstract_fvars(body, &[id]);
        let anon = self.k.anon();
        self.k.lam(anon, ty, body, BinderInfo::Default)
    }

    fn pi_fv(&mut self, id: u64, ty: ExprId, body: ExprId) -> ExprId {
        let body = self.k.abstract_fvars(body, &[id]);
        let anon = self.k.anon();
        self.k.pi(anon, ty, body, BinderInfo::Default)
    }

    /// A non-dependent `hyp -> concl` (`concl` must already be built, so it
    /// carries no reference to the binder being introduced).
    fn arrow(&mut self, hyp: ExprId, concl: ExprId) -> ExprId {
        let anon = self.k.anon();
        self.k.pi(anon, hyp, concl, BinderInfo::Default)
    }

    /// A non-dependent `fun (_ : ty) => body`.
    fn lam_anon(&mut self, ty: ExprId, body: ExprId) -> ExprId {
        let anon = self.k.anon();
        self.k.lam(anon, ty, body, BinderInfo::Default)
    }

    fn nat_ty(&mut self) -> ExprId {
        self.c(self.nat.nat)
    }

    fn bool_ty(&mut self) -> ExprId {
        self.c(self.nat.logic.bool_)
    }

    fn formula_ty(&mut self) -> ExprId {
        self.c(self.p.heyting.formula)
    }

    fn flist_ty(&mut self) -> ExprId {
        self.c(self.p.formula_list)
    }

    /// `Nat -> Nat`, the type of a valuation.
    fn val_ty(&mut self) -> ExprId {
        let nat = self.nat_ty();
        self.arrow(nat, nat)
    }

    /// The unary numeral `succ^n zero`. Only ever called with `n <= 2` — see
    /// the workspace gotcha about unary `Nat` magnitudes.
    fn num(&mut self, n: u32) -> ExprId {
        let mut e = self.c(self.nat.zero);
        let succ = self.c(self.nat.succ);
        for _ in 0..n {
            e = self.k.app(succ, e);
        }
        e
    }

    fn le(&mut self, a: ExprId, b: ExprId) -> ExprId {
        self.capp(self.nat.le, &[a, b])
    }

    /// `Eq.{1} Nat x y`.
    fn eq_nat(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let one = self.level_one();
        let nat = self.nat_ty();
        self.capp_lvl(self.nat.logic.eq, vec![one], &[nat, x, y])
    }

    /// `Eq.{1} Bool x y`.
    fn eq_bool(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let one = self.level_one();
        let bool_ty = self.bool_ty();
        self.capp_lvl(self.nat.logic.eq, vec![one], &[bool_ty, x, y])
    }

    fn level_one(&mut self) -> crate::LevelId {
        let zero = self.k.level_zero();
        self.k.level_succ(zero)
    }

    fn ble(&mut self, a: ExprId, b: ExprId) -> ExprId {
        self.capp(self.nat.ble, &[a, b])
    }

    /// `Bool.rec.{level} motive on_false on_true condition`. Minor order is
    /// `false` then `true`, matching `Bool`'s constructor declaration order
    /// (the same order `nat_prelude`'s `bool_select_nat` uses).
    fn bool_rec(
        &mut self,
        level: crate::LevelId,
        motive: ExprId,
        on_false: ExprId,
        on_true: ExprId,
        condition: ExprId,
    ) -> ExprId {
        self.capp_lvl(
            self.nat.logic.bool_rec,
            vec![level],
            &[motive, on_false, on_true, condition],
        )
    }

    /// `Bool.rec.{1} (fun _ => Nat) on_false on_true condition`, i.e.
    /// `if condition then on_true else on_false : Nat` — the exact shape
    /// `meet3`/`join3`/`himp3` unfold to.
    fn select_nat(&mut self, condition: ExprId, on_true: ExprId, on_false: ExprId) -> ExprId {
        let one = self.level_one();
        let nat = self.nat_ty();
        let bool_ty = self.bool_ty();
        let motive = self.lam_anon(bool_ty, nat);
        self.bool_rec(one, motive, on_false, on_true, condition)
    }

    fn meet3(&mut self, a: ExprId, b: ExprId) -> ExprId {
        self.capp(self.p.heyting.meet3, &[a, b])
    }

    fn join3(&mut self, a: ExprId, b: ExprId) -> ExprId {
        self.capp(self.p.heyting.join3, &[a, b])
    }

    fn himp3(&mut self, a: ExprId, b: ExprId) -> ExprId {
        self.capp(self.p.heyting.himp3, &[a, b])
    }

    /// `ipc_eval f v`.
    fn evalf(&mut self, f: ExprId, v: ExprId) -> ExprId {
        self.capp(self.eval, &[f, v])
    }

    /// `ipc_ctx_meet l v`.
    fn ctxm(&mut self, l: ExprId, v: ExprId) -> ExprId {
        self.capp(self.ctx_meet, &[l, v])
    }

    /// `FormulaList.cons head tail`.
    fn cons(&mut self, head: ExprId, tail: ExprId) -> ExprId {
        self.capp(self.p.cons, &[head, tail])
    }

    /// `Provable ctx phi`.
    fn provable(&mut self, ctx: ExprId, phi: ExprId) -> ExprId {
        self.capp(self.p.provable, &[ctx, phi])
    }

    fn and_(&mut self, a: ExprId, b: ExprId) -> ExprId {
        self.capp(self.p.heyting.and_, &[a, b])
    }

    fn or_(&mut self, a: ExprId, b: ExprId) -> ExprId {
        self.capp(self.p.heyting.or_, &[a, b])
    }

    fn imp(&mut self, a: ExprId, b: ExprId) -> ExprId {
        self.capp(self.p.heyting.imp, &[a, b])
    }

    /// `Not p` (`p -> False`).
    fn not(&mut self, p: ExprId) -> ExprId {
        self.capp(self.nat.logic.not, &[p])
    }

    /// `Eq.refl.{1} alpha a`.
    fn eq_refl(&mut self, alpha: ExprId, a: ExprId) -> ExprId {
        let one = self.level_one();
        self.capp_lvl(self.nat.logic.eq_refl, vec![one], &[alpha, a])
    }

    /// `Le a b -> Le b c -> Le a c`, applied.
    fn le_trans(&mut self, a: ExprId, b: ExprId, c: ExprId, h1: ExprId, h2: ExprId) -> ExprId {
        self.capp(self.nat.le_trans, &[a, b, c, h1, h2])
    }

    fn le_refl(&mut self, a: ExprId) -> ExprId {
        self.capp(self.nat.le_refl, &[a])
    }

    /// `absurd.{0} contra goal h_contra h_refutes : goal`.
    fn absurd_prop(
        &mut self,
        contra: ExprId,
        goal: ExprId,
        h_contra: ExprId,
        refutes: ExprId,
    ) -> ExprId {
        let zero = self.k.level_zero();
        self.capp_lvl(self.nat.logic.absurd, vec![zero], &[contra, goal, h_contra, refutes])
    }

    /// From `h_true : Eq Bool (ble a b) Bool.true` and
    /// `h_false : Eq Bool (ble a b) Bool.false`, build `False`.
    ///
    /// Transports `h_false` along `h_true` (motive
    /// `fun x _ => Eq Bool x Bool.false`) to get `Eq Bool Bool.true
    /// Bool.false`, then applies `Bool.true_ne_false`.
    fn ble_contradiction(&mut self, cond: ExprId, h_true: ExprId, h_false: ExprId) -> ExprId {
        let zero = self.k.level_zero();
        let one = self.level_one();
        let bool_ty = self.bool_ty();
        let bfalse = self.c(self.nat.logic.bool_false);
        let btrue = self.c(self.nat.logic.bool_true);

        // motive := fun (x : Bool) (_ : Eq Bool cond x) => Eq Bool x Bool.false
        let motive = {
            let (x_id, x) = self.fv();
            let body = self.eq_bool(x, bfalse);
            let dom = self.eq_bool(cond, x);
            let inner = self.lam_anon(dom, body);
            self.lam_fv(x_id, bool_ty, inner)
        };
        let transported = self.capp_lvl(
            self.nat.logic.eq_rec,
            vec![zero, one],
            &[bool_ty, cond, motive, h_false, btrue, h_true],
        );
        self.capp(self.nat.logic.bool_true_ne_false, &[transported])
    }

    fn theorem(&mut self, name: &str, ty: ExprId, value: ExprId) -> Result<NameId, KernelError> {
        let anon = self.k.anon();
        let name = self.k.name_str(anon, name);
        self.k.add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })?;
        Ok(name)
    }

    fn definition(&mut self, name: &str, ty: ExprId, value: ExprId) -> Result<NameId, KernelError> {
        let anon = self.k.anon();
        let name = self.k.name_str(anon, name);
        self.k.add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(0),
        })?;
        Ok(name)
    }
}

// ---------------------------------------------------------------------------
// The two `FormulaList.rec` definitions
// ---------------------------------------------------------------------------

/// `ipc_ctx_meet : FormulaList -> (Nat -> Nat) -> Nat`, the meet of the
/// context's values: `2` at `nil` (the chain's top, i.e. the empty meet) and
/// `meet3 (ipc_eval a v) (ipc_ctx_meet l v)` at `cons a l`.
fn declare_ctx_meet(d: &mut Dev<'_>) -> Result<NameId, KernelError> {
    let one = d.level_one();
    let nat = d.nat_ty();
    let val_ty = d.val_ty();
    let flist = d.flist_ty();
    let formula = d.formula_ty();
    let codomain = d.arrow(val_ty, nat);
    let motive = d.lam_anon(flist, codomain);

    // m_nil : (Nat -> Nat) -> Nat := fun v => 2.
    let m_nil = {
        let two = d.num(2);
        d.lam_anon(val_ty, two)
    };
    // m_cons := fun a l ih v => meet3 (ipc_eval a v) (ih v).
    let m_cons = {
        let (a_id, a) = d.fv();
        let (l_id, _l) = d.fv();
        let (ih_id, ih) = d.fv();
        let (v_id, v) = d.fv();
        let ea = d.evalf(a, v);
        let ihv = d.k.app(ih, v);
        let body = d.meet3(ea, ihv);
        let body = d.lam_fv(v_id, val_ty, body);
        let body = d.lam_fv(ih_id, codomain, body);
        let body = d.lam_fv(l_id, flist, body);
        d.lam_fv(a_id, formula, body)
    };

    let (l_id, l) = d.fv();
    let applied = d.capp_lvl(
        d.p.formula_list_rec,
        vec![one],
        &[motive, m_nil, m_cons, l],
    );
    let value = d.lam_fv(l_id, flist, applied);
    let ty = d.arrow(flist, codomain);
    d.definition("ipc_ctx_meet", ty, value)
}

/// `ipc_sat : FormulaList -> (Nat -> Nat) -> Prop` — `True` at `nil`,
/// `And (Eq Nat (ipc_eval a v) 2) (ipc_sat l v)` at `cons a l`.
fn declare_sat(d: &mut Dev<'_>) -> Result<NameId, KernelError> {
    let one = d.level_one();
    let val_ty = d.val_ty();
    let flist = d.flist_ty();
    let formula = d.formula_ty();
    let prop = d.k.sort_zero();
    let codomain = d.arrow(val_ty, prop);
    let motive = d.lam_anon(flist, codomain);

    let m_nil = {
        let true_ = d.c(d.nat.logic.true_);
        d.lam_anon(val_ty, true_)
    };
    let m_cons = {
        let (a_id, a) = d.fv();
        let (l_id, _l) = d.fv();
        let (ih_id, ih) = d.fv();
        let (v_id, v) = d.fv();
        let ea = d.evalf(a, v);
        let two = d.num(2);
        let head = d.eq_nat(ea, two);
        let tail = d.k.app(ih, v);
        let body = d.capp(d.nat.logic.and, &[head, tail]);
        let body = d.lam_fv(v_id, val_ty, body);
        let body = d.lam_fv(ih_id, codomain, body);
        let body = d.lam_fv(l_id, flist, body);
        d.lam_fv(a_id, formula, body)
    };

    let (l_id, l) = d.fv();
    let applied = d.capp_lvl(
        d.p.formula_list_rec,
        vec![one],
        &[motive, m_nil, m_cons, l],
    );
    let value = d.lam_fv(l_id, flist, applied);
    let ty = d.arrow(flist, codomain);
    d.definition("ipc_sat", ty, value)
}

// ---------------------------------------------------------------------------
// Chain lemmas
// ---------------------------------------------------------------------------

/// `ipc_le_of_ble_eq_false : ∀ a b, Eq Bool (Nat.ble a b) Bool.false -> Le b a`.
///
/// By `Nat.le_total a b`: the `Le a b` branch contradicts the hypothesis
/// through `Nat.ble_eq_true_of_le`, and the `Le b a` branch is the goal.
fn declare_le_of_ble_eq_false(d: &mut Dev<'_>) -> Result<NameId, KernelError> {
    let nat = d.nat_ty();
    let (a_id, a) = d.fv();
    let (b_id, b) = d.fv();
    let cond = d.ble(a, b);
    let bfalse = d.c(d.nat.logic.bool_false);
    let hyp_ty = d.eq_bool(cond, bfalse);
    let goal = d.le(b, a);

    let (h_id, h) = d.fv();
    let le_ab = d.le(a, b);
    let le_ba = d.le(b, a);
    let total = d.capp(d.nat.le_total, &[a, b]);

    let branch_ab = {
        let (hab_id, hab) = d.fv();
        let h_true = d.capp(d.nat.ble_eq_true_of_le, &[a, b, hab]);
        let false_proof = d.ble_contradiction(cond, h_true, h);
        // `False` in hand; `absurd` needs a proposition and its refutation, so
        // use `False.rec`-shaped `absurd` at the trivially-refutable `False`.
        let false_ty = d.c(d.nat.logic.false_);
        let identity = {
            let (x_id, x) = d.fv();
            d.lam_fv(x_id, false_ty, x)
        };
        let body = d.absurd_prop(false_ty, goal, false_proof, identity);
        d.lam_fv(hab_id, le_ab, body)
    };
    let branch_ba = {
        let (hba_id, hba) = d.fv();
        d.lam_fv(hba_id, le_ba, hba)
    };
    let body = d.capp(
        d.nat.logic.or_elim,
        &[le_ab, le_ba, goal, total, branch_ab, branch_ba],
    );
    let value = d.lam_fv(h_id, hyp_ty, body);
    let value = d.lam_fv(b_id, nat, value);
    let value = d.lam_fv(a_id, nat, value);

    let ty = {
        let concl = d.arrow(hyp_ty, goal);
        let inner = d.pi_fv(b_id, nat, concl);
        d.pi_fv(a_id, nat, inner)
    };
    d.theorem("ipc_le_of_ble_eq_false", ty, value)
}

/// Build a `Bool.rec.{0}` case split on `Nat.ble a b` that hands each branch
/// the equation `Eq Bool (ble a b) Bool.<branch>`, and whose motive is
/// `fun s => Eq Bool (ble a b) s -> goal_of s`.
///
/// `goal_of` receives the branch's `Bool` and must produce the `Prop` the
/// branch has to prove; it is what puts the *selector* rather than the
/// original condition into the goal, so each branch's `select_nat` ι-reduces.
fn ble_cases_with_eq(
    d: &mut Dev<'_>,
    cond: ExprId,
    goal_of: &dyn Fn(&mut Dev<'_>, ExprId) -> ExprId,
    on_false: &dyn Fn(&mut Dev<'_>, ExprId) -> ExprId,
    on_true: &dyn Fn(&mut Dev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let zero = d.k.level_zero();
    let bool_ty = d.bool_ty();
    let bfalse = d.c(d.nat.logic.bool_false);
    let btrue = d.c(d.nat.logic.bool_true);

    let motive = {
        let (s_id, s) = d.fv();
        let goal = goal_of(d, s);
        let hyp = d.eq_bool(cond, s);
        let body = d.arrow(hyp, goal);
        d.lam_fv(s_id, bool_ty, body)
    };
    let minor_false = {
        let (h_id, h) = d.fv();
        let hyp = d.eq_bool(cond, bfalse);
        let body = on_false(d, h);
        d.lam_fv(h_id, hyp, body)
    };
    let minor_true = {
        let (h_id, h) = d.fv();
        let hyp = d.eq_bool(cond, btrue);
        let body = on_true(d, h);
        d.lam_fv(h_id, hyp, body)
    };
    let applied = d.bool_rec(zero, motive, minor_false, minor_true, cond);
    let refl = d.eq_refl(bool_ty, cond);
    d.k.app(applied, refl)
}

/// `ipc_meet3_le_left : ∀ a b, Le (meet3 a b) a`.
fn declare_meet3_le_left(
    d: &mut Dev<'_>,
    le_of_ble_eq_false: NameId,
) -> Result<NameId, KernelError> {
    let nat = d.nat_ty();
    let (a_id, a) = d.fv();
    let (b_id, b) = d.fv();
    let cond = d.ble(a, b);

    let body = ble_cases_with_eq(
        d,
        cond,
        &|d, s| {
            let selected = d.select_nat(s, a, b);
            d.le(selected, a)
        },
        &|d, h| d.capp(le_of_ble_eq_false, &[a, b, h]),
        &|d, _h| d.le_refl(a),
    );
    let value = d.lam_fv(b_id, nat, body);
    let value = d.lam_fv(a_id, nat, value);

    let ty = {
        let m = d.meet3(a, b);
        let concl = d.le(m, a);
        let inner = d.pi_fv(b_id, nat, concl);
        d.pi_fv(a_id, nat, inner)
    };
    d.theorem("ipc_meet3_le_left", ty, value)
}

/// `ipc_meet3_le_right : ∀ a b, Le (meet3 a b) b`.
fn declare_meet3_le_right(d: &mut Dev<'_>) -> Result<NameId, KernelError> {
    let nat = d.nat_ty();
    let (a_id, a) = d.fv();
    let (b_id, b) = d.fv();
    let cond = d.ble(a, b);

    let body = ble_cases_with_eq(
        d,
        cond,
        &|d, s| {
            let selected = d.select_nat(s, a, b);
            d.le(selected, b)
        },
        &|d, _h| d.le_refl(b),
        &|d, h| d.capp(d.nat.le_of_ble_eq_true, &[a, b, h]),
    );
    let value = d.lam_fv(b_id, nat, body);
    let value = d.lam_fv(a_id, nat, value);

    let ty = {
        let m = d.meet3(a, b);
        let concl = d.le(m, b);
        let inner = d.pi_fv(b_id, nat, concl);
        d.pi_fv(a_id, nat, inner)
    };
    d.theorem("ipc_meet3_le_right", ty, value)
}

/// `ipc_le_meet3 : ∀ a b c, Le c a -> Le c b -> Le c (meet3 a b)`.
///
/// Branch-agnostic: whichever way `ble a b` goes, the selected value is one of
/// `a`/`b` and the matching hypothesis discharges it. No equation needed.
fn declare_le_meet3(d: &mut Dev<'_>) -> Result<NameId, KernelError> {
    let zero = d.k.level_zero();
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let (a_id, a) = d.fv();
    let (b_id, b) = d.fv();
    let (c_id, c) = d.fv();
    let (h1_id, h1) = d.fv();
    let (h2_id, h2) = d.fv();
    let h1_ty = d.le(c, a);
    let h2_ty = d.le(c, b);
    let cond = d.ble(a, b);

    let motive = {
        let (s_id, s) = d.fv();
        let selected = d.select_nat(s, a, b);
        let body = d.le(c, selected);
        d.lam_fv(s_id, bool_ty, body)
    };
    let body = d.bool_rec(zero, motive, h2, h1, cond);
    let value = d.lam_fv(h2_id, h2_ty, body);
    let value = d.lam_fv(h1_id, h1_ty, value);
    let value = d.lam_fv(c_id, nat, value);
    let value = d.lam_fv(b_id, nat, value);
    let value = d.lam_fv(a_id, nat, value);

    let ty = {
        let m = d.meet3(a, b);
        let concl = d.le(c, m);
        let inner = d.arrow(h2_ty, concl);
        let inner = d.arrow(h1_ty, inner);
        let inner = d.pi_fv(c_id, nat, inner);
        let inner = d.pi_fv(b_id, nat, inner);
        d.pi_fv(a_id, nat, inner)
    };
    d.theorem("ipc_le_meet3", ty, value)
}

/// `ipc_le_join3_left : ∀ a b, Le a (join3 a b)`.
///
/// `join3` selects `b` when `ble a b` and `a` otherwise, so the `true` branch
/// needs the equation (to turn `ble a b = true` into `Le a b`) and the
/// `false` branch is reflexivity.
fn declare_le_join3_left(d: &mut Dev<'_>) -> Result<NameId, KernelError> {
    let nat = d.nat_ty();
    let (a_id, a) = d.fv();
    let (b_id, b) = d.fv();
    let cond = d.ble(a, b);

    let body = ble_cases_with_eq(
        d,
        cond,
        &|d, s| {
            let selected = d.select_nat(s, b, a);
            d.le(a, selected)
        },
        &|d, _h| d.le_refl(a),
        &|d, h| d.capp(d.nat.le_of_ble_eq_true, &[a, b, h]),
    );
    let value = d.lam_fv(b_id, nat, body);
    let value = d.lam_fv(a_id, nat, value);

    let ty = {
        let j = d.join3(a, b);
        let concl = d.le(a, j);
        let inner = d.pi_fv(b_id, nat, concl);
        d.pi_fv(a_id, nat, inner)
    };
    d.theorem("ipc_le_join3_left", ty, value)
}

/// `ipc_le_join3_right : ∀ a b, Le b (join3 a b)`.
fn declare_le_join3_right(
    d: &mut Dev<'_>,
    le_of_ble_eq_false: NameId,
) -> Result<NameId, KernelError> {
    let nat = d.nat_ty();
    let (a_id, a) = d.fv();
    let (b_id, b) = d.fv();
    let cond = d.ble(a, b);

    let body = ble_cases_with_eq(
        d,
        cond,
        &|d, s| {
            let selected = d.select_nat(s, b, a);
            d.le(b, selected)
        },
        &|d, h| d.capp(le_of_ble_eq_false, &[a, b, h]),
        &|d, _h| d.le_refl(b),
    );
    let value = d.lam_fv(b_id, nat, body);
    let value = d.lam_fv(a_id, nat, value);

    let ty = {
        let j = d.join3(a, b);
        let concl = d.le(b, j);
        let inner = d.pi_fv(b_id, nat, concl);
        d.pi_fv(a_id, nat, inner)
    };
    d.theorem("ipc_le_join3_right", ty, value)
}

/// `ipc_meet_absorb_le : ∀ x m c, Le m x -> Le (meet3 x m) c -> Le m c`.
///
/// Branch-agnostic: `meet3 x m` is either `x` (then `Le m x` and `Le x c`
/// compose) or `m` (then the hypothesis IS the goal).
fn declare_meet_absorb_le(d: &mut Dev<'_>) -> Result<NameId, KernelError> {
    let zero = d.k.level_zero();
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let (x_id, x) = d.fv();
    let (m_id, m) = d.fv();
    let (c_id, c) = d.fv();
    let (hmx_id, hmx) = d.fv();
    let (h2_id, h2) = d.fv();
    let hmx_ty = d.le(m, x);
    let meet_xm = d.meet3(x, m);
    let h2_ty = d.le(meet_xm, c);
    let goal = d.le(m, c);
    let cond = d.ble(x, m);

    let motive = {
        let (s_id, s) = d.fv();
        let selected = d.select_nat(s, x, m);
        let hyp = d.le(selected, c);
        let body = d.arrow(hyp, goal);
        d.lam_fv(s_id, bool_ty, body)
    };
    let minor_false = {
        let (h_id, h) = d.fv();
        let hyp = d.le(m, c);
        d.lam_fv(h_id, hyp, h)
    };
    let minor_true = {
        let (h_id, h) = d.fv();
        let hyp = d.le(x, c);
        let body = d.le_trans(m, x, c, hmx, h);
        d.lam_fv(h_id, hyp, body)
    };
    let applied = d.bool_rec(zero, motive, minor_false, minor_true, cond);
    let body = d.k.app(applied, h2);

    let value = d.lam_fv(h2_id, h2_ty, body);
    let value = d.lam_fv(hmx_id, hmx_ty, value);
    let value = d.lam_fv(c_id, nat, value);
    let value = d.lam_fv(m_id, nat, value);
    let value = d.lam_fv(x_id, nat, value);

    let ty = {
        let inner = d.arrow(h2_ty, goal);
        let inner = d.arrow(hmx_ty, inner);
        let inner = d.pi_fv(c_id, nat, inner);
        let inner = d.pi_fv(m_id, nat, inner);
        d.pi_fv(x_id, nat, inner)
    };
    d.theorem("ipc_meet_absorb_le", ty, value)
}

/// `ipc_or_elim_chain : ∀ a b m c, Le m (join3 a b) -> Le (meet3 a m) c ->
/// Le (meet3 b m) c -> Le m c`.
///
/// The semantic content of `or_elim`, and the one place the chain's
/// **linearity** is used: `join3 a b` is one of its two arguments outright, so
/// `Le m (join3 a b)` already gives `Le m a` or `Le m b`, and
/// [`declare_meet_absorb_le`] finishes from the matching branch hypothesis.
fn declare_or_elim_chain(
    d: &mut Dev<'_>,
    meet_absorb_le: NameId,
) -> Result<NameId, KernelError> {
    let zero = d.k.level_zero();
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let (a_id, a) = d.fv();
    let (b_id, b) = d.fv();
    let (m_id, m) = d.fv();
    let (c_id, c) = d.fv();
    let (h1_id, h1) = d.fv();
    let (h2_id, h2) = d.fv();
    let (h3_id, h3) = d.fv();

    let join_ab = d.join3(a, b);
    let h1_ty = d.le(m, join_ab);
    let meet_am = d.meet3(a, m);
    let h2_ty = d.le(meet_am, c);
    let meet_bm = d.meet3(b, m);
    let h3_ty = d.le(meet_bm, c);
    let goal = d.le(m, c);
    let cond = d.ble(a, b);

    let motive = {
        let (s_id, s) = d.fv();
        let selected = d.select_nat(s, b, a);
        let hyp = d.le(m, selected);
        let body = d.arrow(hyp, goal);
        d.lam_fv(s_id, bool_ty, body)
    };
    let minor_false = {
        let (h_id, h) = d.fv();
        let hyp = d.le(m, a);
        let body = d.capp(meet_absorb_le, &[a, m, c, h, h2]);
        d.lam_fv(h_id, hyp, body)
    };
    let minor_true = {
        let (h_id, h) = d.fv();
        let hyp = d.le(m, b);
        let body = d.capp(meet_absorb_le, &[b, m, c, h, h3]);
        d.lam_fv(h_id, hyp, body)
    };
    let applied = d.bool_rec(zero, motive, minor_false, minor_true, cond);
    let body = d.k.app(applied, h1);

    let value = d.lam_fv(h3_id, h3_ty, body);
    let value = d.lam_fv(h2_id, h2_ty, value);
    let value = d.lam_fv(h1_id, h1_ty, value);
    let value = d.lam_fv(c_id, nat, value);
    let value = d.lam_fv(m_id, nat, value);
    let value = d.lam_fv(b_id, nat, value);
    let value = d.lam_fv(a_id, nat, value);

    let ty = {
        let inner = d.arrow(h3_ty, goal);
        let inner = d.arrow(h2_ty, inner);
        let inner = d.arrow(h1_ty, inner);
        let inner = d.pi_fv(c_id, nat, inner);
        let inner = d.pi_fv(m_id, nat, inner);
        let inner = d.pi_fv(b_id, nat, inner);
        d.pi_fv(a_id, nat, inner)
    };
    d.theorem("ipc_or_elim_chain", ty, value)
}

/// `ipc_himp3_intro : ∀ a b m, Le m 2 -> Le (meet3 a m) b -> Le m (himp3 a b)`.
///
/// Residuation, the semantic content of `imp_intro`. The `Le m 2` side
/// condition is genuinely needed and is not decoration: at `m = 3, a = 1,
/// b = 1` the conclusion is false (`meet3 1 3 = 1 <= 1` but
/// `3 <= himp3 1 1 = 2` is not), which is why
/// [`declare_ctx_meet_le_top`] exists.
fn declare_himp3_intro(d: &mut Dev<'_>) -> Result<NameId, KernelError> {
    let zero = d.k.level_zero();
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let (a_id, a) = d.fv();
    let (b_id, b) = d.fv();
    let (m_id, m) = d.fv();
    let (htop_id, htop) = d.fv();
    let (h2_id, h2) = d.fv();
    let two = d.num(2);
    let htop_ty = d.le(m, two);
    let meet_am = d.meet3(a, m);
    let h2_ty = d.le(meet_am, b);
    let cond = d.ble(a, b);

    let body = ble_cases_with_eq(
        d,
        cond,
        &|d, s| {
            let two = d.num(2);
            let selected = d.select_nat(s, two, b);
            d.le(m, selected)
        },
        // ble a b = false: goal `Le m b`. Split `meet3 a m`; its `a` branch
        // would give `Le a b`, which contradicts `ble a b = false`.
        &|d, h| {
            let goal = d.le(m, b);
            let inner_cond = d.ble(a, m);
            let motive = {
                let (s_id, s) = d.fv();
                let selected = d.select_nat(s, a, m);
                let hyp = d.le(selected, b);
                let inner = d.arrow(hyp, goal);
                d.lam_fv(s_id, bool_ty, inner)
            };
            let minor_false = {
                let (hm_id, hm) = d.fv();
                let hyp = d.le(m, b);
                d.lam_fv(hm_id, hyp, hm)
            };
            let minor_true = {
                let (hab_id, hab) = d.fv();
                let hyp = d.le(a, b);
                let h_true = d.capp(d.nat.ble_eq_true_of_le, &[a, b, hab]);
                let cond2 = d.ble(a, b);
                let false_proof = d.ble_contradiction(cond2, h_true, h);
                let false_ty = d.c(d.nat.logic.false_);
                let identity = {
                    let (x_id, x) = d.fv();
                    d.lam_fv(x_id, false_ty, x)
                };
                let inner = d.absurd_prop(false_ty, goal, false_proof, identity);
                d.lam_fv(hab_id, hyp, inner)
            };
            let applied = d.bool_rec(zero, motive, minor_false, minor_true, inner_cond);
            d.k.app(applied, h2)
        },
        // ble a b = true: goal `Le m 2`, which is the side condition.
        &|_d, _h| htop,
    );

    let value = d.lam_fv(h2_id, h2_ty, body);
    let value = d.lam_fv(htop_id, htop_ty, value);
    let value = d.lam_fv(m_id, nat, value);
    let value = d.lam_fv(b_id, nat, value);
    let value = d.lam_fv(a_id, nat, value);

    let ty = {
        let hi = d.himp3(a, b);
        let concl = d.le(m, hi);
        let inner = d.arrow(h2_ty, concl);
        let inner = d.arrow(htop_ty, inner);
        let inner = d.pi_fv(m_id, nat, inner);
        let inner = d.pi_fv(b_id, nat, inner);
        d.pi_fv(a_id, nat, inner)
    };
    d.theorem("ipc_himp3_intro", ty, value)
}

/// `ipc_himp3_elim : ∀ a b m, Le m (himp3 a b) -> Le m a -> Le m b` — modus
/// ponens in the algebra, and unconditional (no `Le m 2` needed).
fn declare_himp3_elim(d: &mut Dev<'_>) -> Result<NameId, KernelError> {
    let nat = d.nat_ty();
    let (a_id, a) = d.fv();
    let (b_id, b) = d.fv();
    let (m_id, m) = d.fv();
    let (h1_id, h1) = d.fv();
    let (h2_id, h2) = d.fv();
    let himp_ab = d.himp3(a, b);
    let h1_ty = d.le(m, himp_ab);
    let h2_ty = d.le(m, a);
    let goal = d.le(m, b);
    let cond = d.ble(a, b);

    let cases = ble_cases_with_eq(
        d,
        cond,
        &|d, s| {
            let two = d.num(2);
            let selected = d.select_nat(s, two, b);
            let hyp = d.le(m, selected);
            d.arrow(hyp, goal)
        },
        // ble a b = false: himp3 a b is b, so the hypothesis is the goal.
        &|d, _h| {
            let (hm_id, hm) = d.fv();
            let hyp = d.le(m, b);
            d.lam_fv(hm_id, hyp, hm)
        },
        // ble a b = true: `Le a b`, so `Le m a` composes to `Le m b`.
        &|d, h| {
            let (hm_id, _hm) = d.fv();
            let two = d.num(2);
            let hyp = d.le(m, two);
            let le_ab = d.capp(d.nat.le_of_ble_eq_true, &[a, b, h]);
            let inner = d.le_trans(m, a, b, h2, le_ab);
            d.lam_fv(hm_id, hyp, inner)
        },
    );
    let body = d.k.app(cases, h1);

    let value = d.lam_fv(h2_id, h2_ty, body);
    let value = d.lam_fv(h1_id, h1_ty, value);
    let value = d.lam_fv(m_id, nat, value);
    let value = d.lam_fv(b_id, nat, value);
    let value = d.lam_fv(a_id, nat, value);

    let ty = {
        let inner = d.arrow(h2_ty, goal);
        let inner = d.arrow(h1_ty, inner);
        let inner = d.pi_fv(m_id, nat, inner);
        let inner = d.pi_fv(b_id, nat, inner);
        d.pi_fv(a_id, nat, inner)
    };
    d.theorem("ipc_himp3_elim", ty, value)
}

/// `ipc_ctx_meet_le_top : ∀ l v, Le (ipc_ctx_meet l v) 2`, by `FormulaList.rec`
/// — `nil` is `2` itself and every `cons` takes a meet, which can only go
/// down. Discharges [`declare_himp3_intro`]'s side condition.
fn declare_ctx_meet_le_top(
    d: &mut Dev<'_>,
    meet3_le_right: NameId,
) -> Result<NameId, KernelError> {
    let zero = d.k.level_zero();
    let flist = d.flist_ty();
    let formula = d.formula_ty();
    let val_ty = d.val_ty();

    let motive = {
        let (l_id, l) = d.fv();
        let (v_id, v) = d.fv();
        let m = d.ctxm(l, v);
        let two = d.num(2);
        let body = d.le(m, two);
        let body = d.pi_fv(v_id, val_ty, body);
        d.lam_fv(l_id, flist, body)
    };
    let motive_of = |d: &mut Dev<'_>, l: ExprId| -> ExprId {
        let (v_id, v) = d.fv();
        let m = d.ctxm(l, v);
        let two = d.num(2);
        let body = d.le(m, two);
        d.pi_fv(v_id, val_ty, body)
    };

    let m_nil = {
        let (v_id, _v) = d.fv();
        let two = d.num(2);
        let body = d.le_refl(two);
        d.lam_fv(v_id, val_ty, body)
    };
    let m_cons = {
        let (a_id, a) = d.fv();
        let (l_id, l) = d.fv();
        let (ih_id, ih) = d.fv();
        let ih_ty = motive_of(d, l);
        let (v_id, v) = d.fv();
        let ea = d.evalf(a, v);
        let tail = d.ctxm(l, v);
        let head_meet = d.meet3(ea, tail);
        let two = d.num(2);
        let step = d.capp(meet3_le_right, &[ea, tail]);
        let ihv = d.k.app(ih, v);
        let body = d.le_trans(head_meet, tail, two, step, ihv);
        let body = d.lam_fv(v_id, val_ty, body);
        let body = d.lam_fv(ih_id, ih_ty, body);
        let body = d.lam_fv(l_id, flist, body);
        d.lam_fv(a_id, formula, body)
    };

    let (l_id, l) = d.fv();
    let (v_id, v) = d.fv();
    let applied = d.capp_lvl(
        d.p.formula_list_rec,
        vec![zero],
        &[motive, m_nil, m_cons, l],
    );
    let body = d.k.app(applied, v);
    let value = d.lam_fv(v_id, val_ty, body);
    let value = d.lam_fv(l_id, flist, value);

    let ty = {
        let m = d.ctxm(l, v);
        let two = d.num(2);
        let concl = d.le(m, two);
        let inner = d.pi_fv(v_id, val_ty, concl);
        d.pi_fv(l_id, flist, inner)
    };
    d.theorem("ipc_ctx_meet_le_top", ty, value)
}

// ---------------------------------------------------------------------------
// Soundness: induction on the derivation
// ---------------------------------------------------------------------------

/// `ipc_soundness : ∀ ctx phi, Provable ctx phi -> ∀ v,
/// Le (ipc_ctx_meet ctx v) (ipc_eval phi v)`, by `Provable.rec` — eleven
/// minor premises, one per natural-deduction rule.
#[allow(clippy::too_many_lines)]
fn declare_soundness(d: &mut Dev<'_>, lemmas: &ChainLemmas) -> Result<NameId, KernelError> {
    let flist = d.flist_ty();
    let formula = d.formula_ty();
    let val_ty = d.val_ty();

    // `S c f := Π v, Le (ipc_ctx_meet c v) (ipc_eval f v)`.
    let sound_of = |d: &mut Dev<'_>, c: ExprId, f: ExprId| -> ExprId {
        let (v_id, v) = d.fv();
        let m = d.ctxm(c, v);
        let e = d.evalf(f, v);
        let body = d.le(m, e);
        d.pi_fv(v_id, val_ty, body)
    };

    let motive = {
        let (c_id, c) = d.fv();
        let (f_id, f) = d.fv();
        let inner = sound_of(d, c, f);
        let ph = d.provable(c, f);
        let body = d.lam_anon(ph, inner);
        let body = d.lam_fv(f_id, formula, body);
        d.lam_fv(c_id, flist, body)
    };

    // 1. ax_head : Π c p, Provable (cons p c) p
    let m_ax_head = {
        let (c_id, c) = d.fv();
        let (p_id, p) = d.fv();
        let (v_id, v) = d.fv();
        let ep = d.evalf(p, v);
        let mc = d.ctxm(c, v);
        let body = d.capp(lemmas.meet3_le_left, &[ep, mc]);
        let body = d.lam_fv(v_id, val_ty, body);
        let body = d.lam_fv(p_id, formula, body);
        d.lam_fv(c_id, flist, body)
    };

    // 2. weaken : Π c p q, Provable c p -> Provable (cons q c) p
    let m_weaken = {
        let (c_id, c) = d.fv();
        let (p_id, p) = d.fv();
        let (q_id, q) = d.fv();
        let (h_id, _h) = d.fv();
        let h_ty = d.provable(c, p);
        let (ih_id, ih) = d.fv();
        let ih_ty = sound_of(d, c, p);
        let (v_id, v) = d.fv();
        let eq_ = d.evalf(q, v);
        let mc = d.ctxm(c, v);
        let head_meet = d.meet3(eq_, mc);
        let ep = d.evalf(p, v);
        let step = d.capp(lemmas.meet3_le_right, &[eq_, mc]);
        let ihv = d.k.app(ih, v);
        let body = d.le_trans(head_meet, mc, ep, step, ihv);
        let body = d.lam_fv(v_id, val_ty, body);
        let body = d.lam_fv(ih_id, ih_ty, body);
        let body = d.lam_fv(h_id, h_ty, body);
        let body = d.lam_fv(q_id, formula, body);
        let body = d.lam_fv(p_id, formula, body);
        d.lam_fv(c_id, flist, body)
    };

    // 3. and_intro : Π c p q, Provable c p -> Provable c q -> Provable c (and_ p q)
    let m_and_intro = {
        let (c_id, c) = d.fv();
        let (p_id, p) = d.fv();
        let (q_id, q) = d.fv();
        let (h1_id, _h1) = d.fv();
        let h1_ty = d.provable(c, p);
        let (h2_id, _h2) = d.fv();
        let h2_ty = d.provable(c, q);
        let (ih1_id, ih1) = d.fv();
        let ih1_ty = sound_of(d, c, p);
        let (ih2_id, ih2) = d.fv();
        let ih2_ty = sound_of(d, c, q);
        let (v_id, v) = d.fv();
        let ep = d.evalf(p, v);
        let eq_ = d.evalf(q, v);
        let mc = d.ctxm(c, v);
        let i1 = d.k.app(ih1, v);
        let i2 = d.k.app(ih2, v);
        let body = d.capp(lemmas.le_meet3, &[ep, eq_, mc, i1, i2]);
        let body = d.lam_fv(v_id, val_ty, body);
        let body = d.lam_fv(ih2_id, ih2_ty, body);
        let body = d.lam_fv(ih1_id, ih1_ty, body);
        let body = d.lam_fv(h2_id, h2_ty, body);
        let body = d.lam_fv(h1_id, h1_ty, body);
        let body = d.lam_fv(q_id, formula, body);
        let body = d.lam_fv(p_id, formula, body);
        d.lam_fv(c_id, flist, body)
    };

    // 4/5. and_elim1/2 : Π c p q, Provable c (and_ p q) -> Provable c p (resp. q)
    let mut and_elim = |d: &mut Dev<'_>, first: bool| -> ExprId {
        let (c_id, c) = d.fv();
        let (p_id, p) = d.fv();
        let (q_id, q) = d.fv();
        let conj = d.and_(p, q);
        let (h_id, _h) = d.fv();
        let h_ty = d.provable(c, conj);
        let (ih_id, ih) = d.fv();
        let ih_ty = sound_of(d, c, conj);
        let (v_id, v) = d.fv();
        let ep = d.evalf(p, v);
        let eq_ = d.evalf(q, v);
        let meet = d.meet3(ep, eq_);
        let mc = d.ctxm(c, v);
        let target = if first { ep } else { eq_ };
        let projection = if first {
            lemmas.meet3_le_left
        } else {
            lemmas.meet3_le_right
        };
        let step = d.capp(projection, &[ep, eq_]);
        let ihv = d.k.app(ih, v);
        let body = d.le_trans(mc, meet, target, ihv, step);
        let body = d.lam_fv(v_id, val_ty, body);
        let body = d.lam_fv(ih_id, ih_ty, body);
        let body = d.lam_fv(h_id, h_ty, body);
        let body = d.lam_fv(q_id, formula, body);
        let body = d.lam_fv(p_id, formula, body);
        d.lam_fv(c_id, flist, body)
    };
    let m_and_elim1 = and_elim(d, true);
    let m_and_elim2 = and_elim(d, false);

    // 6/7. or_intro1/2 : Π c p q, Provable c p (resp. q) -> Provable c (or_ p q)
    let mut or_intro = |d: &mut Dev<'_>, first: bool| -> ExprId {
        let (c_id, c) = d.fv();
        let (p_id, p) = d.fv();
        let (q_id, q) = d.fv();
        let (h_id, _h) = d.fv();
        let source = if first { p } else { q };
        let h_ty = d.provable(c, source);
        let (ih_id, ih) = d.fv();
        let ih_ty = sound_of(d, c, source);
        let (v_id, v) = d.fv();
        let ep = d.evalf(p, v);
        let eq_ = d.evalf(q, v);
        let join = d.join3(ep, eq_);
        let mc = d.ctxm(c, v);
        let mid = if first { ep } else { eq_ };
        let injection = if first {
            lemmas.le_join3_left
        } else {
            lemmas.le_join3_right
        };
        let step = d.capp(injection, &[ep, eq_]);
        let ihv = d.k.app(ih, v);
        let body = d.le_trans(mc, mid, join, ihv, step);
        let body = d.lam_fv(v_id, val_ty, body);
        let body = d.lam_fv(ih_id, ih_ty, body);
        let body = d.lam_fv(h_id, h_ty, body);
        let body = d.lam_fv(q_id, formula, body);
        let body = d.lam_fv(p_id, formula, body);
        d.lam_fv(c_id, flist, body)
    };
    let m_or_intro1 = or_intro(d, true);
    let m_or_intro2 = or_intro(d, false);

    // 8. or_elim : Π c p q r, Provable c (or_ p q) -> Provable (cons p c) r
    //              -> Provable (cons q c) r -> Provable c r
    let m_or_elim = {
        let (c_id, c) = d.fv();
        let (p_id, p) = d.fv();
        let (q_id, q) = d.fv();
        let (r_id, r) = d.fv();
        let disj = d.or_(p, q);
        let ctx_p = d.cons(p, c);
        let ctx_q = d.cons(q, c);
        let (h1_id, _h1) = d.fv();
        let h1_ty = d.provable(c, disj);
        let (h2_id, _h2) = d.fv();
        let h2_ty = d.provable(ctx_p, r);
        let (h3_id, _h3) = d.fv();
        let h3_ty = d.provable(ctx_q, r);
        let (ih1_id, ih1) = d.fv();
        let ih1_ty = sound_of(d, c, disj);
        let (ih2_id, ih2) = d.fv();
        let ih2_ty = sound_of(d, ctx_p, r);
        let (ih3_id, ih3) = d.fv();
        let ih3_ty = sound_of(d, ctx_q, r);
        let (v_id, v) = d.fv();
        let ep = d.evalf(p, v);
        let eq_ = d.evalf(q, v);
        let er = d.evalf(r, v);
        let mc = d.ctxm(c, v);
        let i1 = d.k.app(ih1, v);
        let i2 = d.k.app(ih2, v);
        let i3 = d.k.app(ih3, v);
        let body = d.capp(lemmas.or_elim_chain, &[ep, eq_, mc, er, i1, i2, i3]);
        let body = d.lam_fv(v_id, val_ty, body);
        let body = d.lam_fv(ih3_id, ih3_ty, body);
        let body = d.lam_fv(ih2_id, ih2_ty, body);
        let body = d.lam_fv(ih1_id, ih1_ty, body);
        let body = d.lam_fv(h3_id, h3_ty, body);
        let body = d.lam_fv(h2_id, h2_ty, body);
        let body = d.lam_fv(h1_id, h1_ty, body);
        let body = d.lam_fv(r_id, formula, body);
        let body = d.lam_fv(q_id, formula, body);
        let body = d.lam_fv(p_id, formula, body);
        d.lam_fv(c_id, flist, body)
    };

    // 9. imp_intro : Π c p q, Provable (cons p c) q -> Provable c (imp p q)
    let m_imp_intro = {
        let (c_id, c) = d.fv();
        let (p_id, p) = d.fv();
        let (q_id, q) = d.fv();
        let ctx_p = d.cons(p, c);
        let (h_id, _h) = d.fv();
        let h_ty = d.provable(ctx_p, q);
        let (ih_id, ih) = d.fv();
        let ih_ty = sound_of(d, ctx_p, q);
        let (v_id, v) = d.fv();
        let ep = d.evalf(p, v);
        let eq_ = d.evalf(q, v);
        let mc = d.ctxm(c, v);
        let top = d.capp(lemmas.ctx_meet_le_top, &[c, v]);
        let ihv = d.k.app(ih, v);
        let body = d.capp(lemmas.himp3_intro, &[ep, eq_, mc, top, ihv]);
        let body = d.lam_fv(v_id, val_ty, body);
        let body = d.lam_fv(ih_id, ih_ty, body);
        let body = d.lam_fv(h_id, h_ty, body);
        let body = d.lam_fv(q_id, formula, body);
        let body = d.lam_fv(p_id, formula, body);
        d.lam_fv(c_id, flist, body)
    };

    // 10. imp_elim : Π c p q, Provable c (imp p q) -> Provable c p -> Provable c q
    let m_imp_elim = {
        let (c_id, c) = d.fv();
        let (p_id, p) = d.fv();
        let (q_id, q) = d.fv();
        let implication = d.imp(p, q);
        let (h1_id, _h1) = d.fv();
        let h1_ty = d.provable(c, implication);
        let (h2_id, _h2) = d.fv();
        let h2_ty = d.provable(c, p);
        let (ih1_id, ih1) = d.fv();
        let ih1_ty = sound_of(d, c, implication);
        let (ih2_id, ih2) = d.fv();
        let ih2_ty = sound_of(d, c, p);
        let (v_id, v) = d.fv();
        let ep = d.evalf(p, v);
        let eq_ = d.evalf(q, v);
        let mc = d.ctxm(c, v);
        let i1 = d.k.app(ih1, v);
        let i2 = d.k.app(ih2, v);
        let body = d.capp(lemmas.himp3_elim, &[ep, eq_, mc, i1, i2]);
        let body = d.lam_fv(v_id, val_ty, body);
        let body = d.lam_fv(ih2_id, ih2_ty, body);
        let body = d.lam_fv(ih1_id, ih1_ty, body);
        let body = d.lam_fv(h2_id, h2_ty, body);
        let body = d.lam_fv(h1_id, h1_ty, body);
        let body = d.lam_fv(q_id, formula, body);
        let body = d.lam_fv(p_id, formula, body);
        d.lam_fv(c_id, flist, body)
    };

    // 11. bot_elim : Π c p, Provable c bot -> Provable c p
    let m_bot_elim = {
        let (c_id, c) = d.fv();
        let (p_id, p) = d.fv();
        let bot = d.c(d.p.heyting.bot);
        let (h_id, _h) = d.fv();
        let h_ty = d.provable(c, bot);
        let (ih_id, ih) = d.fv();
        let ih_ty = sound_of(d, c, bot);
        let (v_id, v) = d.fv();
        let mc = d.ctxm(c, v);
        let zero_nat = d.c(d.nat.zero);
        let ep = d.evalf(p, v);
        let ihv = d.k.app(ih, v);
        let bottom = d.capp(d.nat.zero_le, &[ep]);
        let body = d.le_trans(mc, zero_nat, ep, ihv, bottom);
        let body = d.lam_fv(v_id, val_ty, body);
        let body = d.lam_fv(ih_id, ih_ty, body);
        let body = d.lam_fv(h_id, h_ty, body);
        let body = d.lam_fv(p_id, formula, body);
        d.lam_fv(c_id, flist, body)
    };

    let provable_rec = d.k.name_str(d.p.provable, "rec");
    let (ctx_id, ctx) = d.fv();
    let (phi_id, phi) = d.fv();
    let (h_id, h) = d.fv();
    let h_ty = d.provable(ctx, phi);
    let body = d.capp(
        provable_rec,
        &[
            motive,
            m_ax_head,
            m_weaken,
            m_and_intro,
            m_and_elim1,
            m_and_elim2,
            m_or_intro1,
            m_or_intro2,
            m_or_elim,
            m_imp_intro,
            m_imp_elim,
            m_bot_elim,
            ctx,
            phi,
            h,
        ],
    );
    let value = d.lam_fv(h_id, h_ty, body);
    let value = d.lam_fv(phi_id, formula, value);
    let value = d.lam_fv(ctx_id, flist, value);

    let ty = {
        let concl = sound_of(d, ctx, phi);
        let inner = d.arrow(h_ty, concl);
        let inner = d.pi_fv(phi_id, formula, inner);
        d.pi_fv(ctx_id, flist, inner)
    };
    d.theorem("ipc_soundness", ty, value)
}

// ---------------------------------------------------------------------------
// The `sat` bridge and the corollary
// ---------------------------------------------------------------------------

/// `ipc_sat_le_ctx_meet : ∀ l v, ipc_sat l v -> Le 2 (ipc_ctx_meet l v)` — a
/// satisfied context has top value, so soundness's conclusion specialises.
fn declare_sat_le_ctx_meet(
    d: &mut Dev<'_>,
    sat: NameId,
    le_meet3: NameId,
) -> Result<NameId, KernelError> {
    let zero = d.k.level_zero();
    let one = d.level_one();
    let flist = d.flist_ty();
    let formula = d.formula_ty();
    let val_ty = d.val_ty();
    let nat = d.nat_ty();

    let motive_of = |d: &mut Dev<'_>, l: ExprId| -> ExprId {
        let (v_id, v) = d.fv();
        let hyp = d.capp(sat, &[l, v]);
        let m = d.ctxm(l, v);
        let two = d.num(2);
        let concl = d.le(two, m);
        let body = d.arrow(hyp, concl);
        d.pi_fv(v_id, val_ty, body)
    };
    let motive = {
        let (l_id, l) = d.fv();
        let body = motive_of(d, l);
        d.lam_fv(l_id, flist, body)
    };

    let m_nil = {
        let (v_id, _v) = d.fv();
        let (h_id, _h) = d.fv();
        let true_ = d.c(d.nat.logic.true_);
        let two = d.num(2);
        let body = d.le_refl(two);
        let body = d.lam_fv(h_id, true_, body);
        d.lam_fv(v_id, val_ty, body)
    };
    let m_cons = {
        let (a_id, a) = d.fv();
        let (l_id, l) = d.fv();
        let (ih_id, ih) = d.fv();
        let ih_ty = motive_of(d, l);
        let (v_id, v) = d.fv();
        let ea = d.evalf(a, v);
        let two = d.num(2);
        let head_eq = d.eq_nat(ea, two);
        let tail_sat = d.capp(sat, &[l, v]);
        let hyp_ty = d.capp(d.nat.logic.and, &[head_eq, tail_sat]);
        let (h_id, h) = d.fv();

        let h_head = d.capp(d.nat.logic.and_left, &[head_eq, tail_sat, h]);
        let h_tail = d.capp(d.nat.logic.and_right, &[head_eq, tail_sat, h]);

        // `Le 2 (ipc_eval a v)` by transporting `Le (eval a v) (eval a v)`
        // along `h_head : Eq Nat (eval a v) 2` with motive `fun y _ => Le y (eval a v)`.
        let head_le = {
            let transport_motive = {
                let (y_id, y) = d.fv();
                let body = d.le(y, ea);
                let dom = d.eq_nat(ea, y);
                let inner = d.lam_anon(dom, body);
                d.lam_fv(y_id, nat, inner)
            };
            let refl_case = d.le_refl(ea);
            d.capp_lvl(
                d.nat.logic.eq_rec,
                vec![zero, one],
                &[nat, ea, transport_motive, refl_case, two, h_head],
            )
        };
        let tail_le = {
            let ihv = d.k.app(ih, v);
            d.k.app(ihv, h_tail)
        };
        let tail_meet = d.ctxm(l, v);
        let body = d.capp(le_meet3, &[ea, tail_meet, two, head_le, tail_le]);
        let body = d.lam_fv(h_id, hyp_ty, body);
        let body = d.lam_fv(v_id, val_ty, body);
        let body = d.lam_fv(ih_id, ih_ty, body);
        let body = d.lam_fv(l_id, flist, body);
        d.lam_fv(a_id, formula, body)
    };

    let (l_id, l) = d.fv();
    let (v_id, v) = d.fv();
    let (h_id, h) = d.fv();
    let h_ty = d.capp(sat, &[l, v]);
    let applied = d.capp_lvl(
        d.p.formula_list_rec,
        vec![zero],
        &[motive, m_nil, m_cons, l],
    );
    let body = d.apply(applied, &[v, h]);
    let value = d.lam_fv(h_id, h_ty, body);
    let value = d.lam_fv(v_id, val_ty, value);
    let value = d.lam_fv(l_id, flist, value);

    let ty = {
        let m = d.ctxm(l, v);
        let two = d.num(2);
        let concl = d.le(two, m);
        let inner = d.arrow(h_ty, concl);
        let inner = d.pi_fv(v_id, val_ty, inner);
        d.pi_fv(l_id, flist, inner)
    };
    d.theorem("ipc_sat_le_ctx_meet", ty, value)
}

/// `ipc_soundness_sat : ∀ ctx phi, Provable ctx phi -> ∀ v, ipc_sat ctx v ->
/// Le 2 (ipc_eval phi v)` — the sat-shaped corollary, by composing
/// [`declare_sat_le_ctx_meet`] with [`declare_soundness`].
fn declare_soundness_sat(
    d: &mut Dev<'_>,
    sat: NameId,
    soundness: NameId,
    sat_le_ctx_meet: NameId,
) -> Result<NameId, KernelError> {
    let flist = d.flist_ty();
    let formula = d.formula_ty();
    let val_ty = d.val_ty();

    let (ctx_id, ctx) = d.fv();
    let (phi_id, phi) = d.fv();
    let (h_id, h) = d.fv();
    let h_ty = d.provable(ctx, phi);
    let (v_id, v) = d.fv();
    let (hs_id, hs) = d.fv();
    let hs_ty = d.capp(sat, &[ctx, v]);

    let two = d.num(2);
    let m = d.ctxm(ctx, v);
    let e = d.evalf(phi, v);
    let left = d.capp(sat_le_ctx_meet, &[ctx, v, hs]);
    let right = {
        let applied = d.capp(soundness, &[ctx, phi, h]);
        d.k.app(applied, v)
    };
    let body = d.le_trans(two, m, e, left, right);
    let value = d.lam_fv(hs_id, hs_ty, body);
    let value = d.lam_fv(v_id, val_ty, value);
    let value = d.lam_fv(h_id, h_ty, value);
    let value = d.lam_fv(phi_id, formula, value);
    let value = d.lam_fv(ctx_id, flist, value);

    let ty = {
        let concl = d.le(two, e);
        let inner = d.arrow(hs_ty, concl);
        let inner = d.pi_fv(v_id, val_ty, inner);
        let inner = d.arrow(h_ty, inner);
        let inner = d.pi_fv(phi_id, formula, inner);
        d.pi_fv(ctx_id, flist, inner)
    };
    d.theorem("ipc_soundness_sat", ty, value)
}

/// `ipc_sat_not_vacuous : Not (ipc_sat (cons (var 0) nil) (fun _ => 1))`.
///
/// The discriminating check on [`declare_sat`]: a constantly-true `sat` would
/// make [`declare_soundness_sat`] vacuous and would pass any careless
/// evaluation test, so the kernel is made to REFUTE one concrete instance.
/// `ipc_eval (var 0) (fun _ => 1)` is `1`, and `1 != 2`.
fn declare_sat_not_vacuous(d: &mut Dev<'_>, sat: NameId) -> Result<NameId, KernelError> {
    let nat = d.nat_ty();
    let one_num = d.num(1);
    let two = d.num(2);
    let valuation = {
        let (junk_id, _junk) = d.fv();
        d.lam_fv(junk_id, nat, one_num)
    };
    let var0 = {
        let zero_nat = d.c(d.nat.zero);
        let var_const = d.c(d.p.heyting.var);
        d.k.app(var_const, zero_nat)
    };
    let nil = d.c(d.p.nil);
    let ctx = d.cons(var0, nil);
    let sat_app = d.capp(sat, &[ctx, valuation]);

    let (h_id, h) = d.fv();
    let ev = d.evalf(var0, valuation);
    let head_eq = d.eq_nat(ev, two);
    let tail_sat = d.capp(sat, &[nil, valuation]);
    let head = d.capp(d.nat.logic.and_left, &[head_eq, tail_sat, h]);

    // Nat.ne_of_beq_eq_false 1 2 (rfl : Eq Bool (Nat.beq 1 2) Bool.false) : Not (Eq Nat 1 2)
    let beq_term = d.capp(d.nat.beq, &[one_num, two]);
    let bool_ty = d.bool_ty();
    let refl = d.eq_refl(bool_ty, beq_term);
    let ne = d.capp(d.nat.ne_of_beq_eq_false, &[one_num, two, refl]);
    let body = d.k.app(ne, head);
    let value = d.lam_fv(h_id, sat_app, body);

    let ty = d.not(sat_app);
    d.theorem("ipc_sat_not_vacuous", ty, value)
}

/// `ipc_excluded_middle_not_provable : Not (Provable FormulaList.nil
/// (or_ (var 0) (imp (var 0) bot)))` — the fact.
///
/// Contraposition of [`declare_soundness`] against `ipc_heyting.rs`'s
/// countermodel: at `v := fun _ => 1` the empty context's meet is `2` and
/// `ipc_eval (p ∨ ¬p) v` is `1`, so an assumed derivation would give
/// `Le 2 1`, refuted by `Nat.not_succ_le_self 1`.
fn declare_pem_not_provable(d: &mut Dev<'_>, soundness: NameId) -> Result<NameId, KernelError> {
    let nat = d.nat_ty();
    let pem = pem_instance(d.k, &d.p.heyting);
    let nil = d.c(d.p.nil);
    let goal = d.provable(nil, pem);

    let one_num = d.num(1);
    let valuation = {
        let (junk_id, _junk) = d.fv();
        d.lam_fv(junk_id, nat, one_num)
    };

    let (h_id, h) = d.fv();
    let applied = d.capp(soundness, &[nil, pem, h]);
    let at_v = d.k.app(applied, valuation);
    let refute = d.capp(d.nat.not_succ_le_self, &[one_num]);
    let body = d.k.app(refute, at_v);
    let value = d.lam_fv(h_id, goal, body);

    let ty = d.not(goal);
    d.theorem("ipc_excluded_middle_not_provable", ty, value)
}

#[cfg(test)]
mod tests;

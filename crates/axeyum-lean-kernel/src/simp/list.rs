//! The `List` fragment — the design ADR-1586 §4 scoped and did not build:
//! `simp`'s first producer over a carrier that is not a fixed, monomorphic
//! type. Same rewrite-chain design as [`super::nat`]/[`super::int`]
//! (outermost-first, first-order matching, [`super::MAX_STEPS`] fixed
//! point), forced into the shape §4 predicted rather than a mechanical port:
//!
//! - **No `NatOps`/`IntDev`-style hardcoded-carrier trait.** `List.{u} α` is
//!   genuinely type-polymorphic — every theorem here carries `α : Type 0` as
//!   a real argument — so [`ListDev`] threads `alpha`/`beta` as EXPLICIT
//!   fields, set per node during traversal, rather than baking one carrier
//!   into a trait method the way `NatOps::congr` bakes in `Nat`.
//! - **No `fresh_fvar()` counter shared with `list_prelude` itself.**
//!   `list_prelude`'s own declarations hand-assign free-variable ids from
//!   reserved numeric blocks (`91_000`, `91_100`, …) rather than using a
//!   counter at all (see `list_prelude::ops`'s module docs) — reusing that
//!   scheme risks a silent id collision the type checker would not
//!   necessarily catch. [`ListDev`] mints its own ids from [`FVAR_BASE`],
//!   far above every block `list_prelude` hand-assigns.
//! - **Congruence via [`crate::list_prelude::ops::congr_of`]**, the
//!   carrier-generic `Eq.rec` combinator that module already exposes (ADR-
//!   1495 G4 pilot 2) — genuinely more general than `NatOps::congr`/
//!   `IntDev::icongr`, since it takes the argument and result carrier types
//!   (and levels) as explicit parameters rather than hardcoding one, so no
//!   analogue of the `App`-spine partial-application trap ADR-1586 §2
//!   describes for ℕ/ℤ is possible here: every congruence step below states
//!   its own carrier explicitly, inferred from the kernel
//!   ([`rewrite_unary`]) rather than assumed.
//!
//! ## Two rule-set tiers, and why
//!
//! `List` sits BEFORE `Nat` in the prelude chain (`List Nat` only needs the
//! `Nat` *type*, not its arithmetic — see `list_prelude`'s own module docs),
//! so `List.length_append`/`List.count_append` (which need the real named
//! `Nat.add`) are declared later, in `list_prelude::bridge`/`::perm`, not in
//! `list_prelude::theorems`. This producer mirrors that split:
//!
//! - [`list_only_rules`] — every default law needing nothing beyond
//!   [`crate::LogicPrelude`] and [`crate::ListPrelude`]: `append_nil`,
//!   `nil_append` (refl — `List.append` recurses on its FIRST argument, so
//!   this is the base case's own defining equation, exactly what ADR-1586
//!   §4 predicted), `reverse_nil`/`length_nil`/`map_nil`/`map_cons`/
//!   `foldr_nil` (refl — the same "defining equation from the recursor's
//!   own base/step case" shape as ℕ's `succ_add`/`add_succ`), `append_assoc`,
//!   `reverse_reverse`, `length_map`. Usable from `list_prelude::theorems`
//!   itself, where no `NatPrelude` exists yet — this is what makes the
//!   base-case retirements in that module possible.
//! - [`default_rules`]/[`default_rules_with_perm`] — `list_only_rules` plus
//!   `length_append` (needs [`crate::ListNatBridge`]) and `count_append`
//!   (needs [`crate::ListPerm`]) — the "default set" in the sense the rest
//!   of this crate's `simp` producers use the term, and the population
//!   ADR-1586 §4 named. Requires a [`ListDev`] built with the full stack
//!   present ([`ListDev::new_full`]).
//!
//! ## `append_assoc`'s termination is a different argument than ℕ/ℤ's
//!
//! [`super`]'s module docs give the confluence criterion `simp::nat`/
//! `simp::int` rely on: a default rule's pattern must require a specific
//! literal subterm its own output never reintroduces. `append_assoc`
//! (`append (append a b) c = append a (append b c)`, FORWARD only) does not
//! fit that shape — its pattern `append (append _ _) _` matches an
//! `append`-headed term, and rewriting produces another `append`-headed
//! term. It still terminates, by a DIFFERENT strictly-decreasing measure:
//! the number of LEFT-nested `append`s strictly drops on every rewrite
//! (`append (append (append x y) z) w` → `append (append x y) (append z
//! w)` → `append x (append y (append z w))`, nesting depth 3 → 2 → 1, no
//! further match). A BACKWARD copy of the same lemma does NOT share this
//! property — its pattern matches ANY `append`-headed second operand, so
//! together the two directions oscillate forever
//! ([`tests::a_looping_extra_rule_set_declines_budget_exceeded_not_a_hang`]
//! confirms this by actually running it, not by inspection).

#![allow(clippy::too_many_arguments, clippy::many_single_char_names)]

use crate::ExprNode;
use crate::LogicPrelude;
use crate::NameId;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::list_prelude::ListNames;
use crate::list_prelude::ops::{
    append_of, cons_of, count_of, eq_of, foldr_of, lam_fvar, length_of, list_of, map_of,
    nat_add_of, nat_succ_of, nil_of, pi_fvar, refl_of, reverse_of, symm_of, trans_of,
};
use crate::{BinderInfo, Kernel, KernelError, ListNatBridge, NatPrelude};

use super::{Decline, MAX_STEPS, Orientation};

/// The first free-variable id [`ListDev`] mints — far above every
/// hand-assigned block `list_prelude` itself uses (`9x_xxx`), so a term
/// this module builds can never collide with one already abstracted into a
/// declaration `list_prelude` admitted earlier.
const FVAR_BASE: u64 = 700_000;

/// [`crate::ListPrelude`]'s first ten fields, restated as a [`ListNames`] —
/// the shape every [`ListDev`] term builder actually needs (never the four
/// theorem `NameId`s a full `ListPrelude` additionally carries). A caller
/// holding a `ListPrelude` (a test, or `crate::tactic`) uses this to build a
/// [`ListDev`]; `list_prelude::theorems` itself already has a `ListNames`
/// directly (it runs BEFORE `ListPrelude` exists) and does not need this.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn names_of(p: &crate::ListPrelude) -> ListNames {
    ListNames {
        list: p.list,
        nil: p.nil,
        cons: p.cons,
        rec: p.rec,
        u_param: p.u_param,
        length: p.length,
        append: p.append,
        map: p.map,
        foldr: p.foldr,
        reverse: p.reverse,
    }
}

/// A development over a kernel that already carries [`ListPrelude`] (and,
/// for [`default_rules`]'s `Nat`-crossing rules, [`NatPrelude`] +
/// [`ListNatBridge`] + [`ListPerm`]) — see the module docs on the two
/// tiers.
///
/// `alpha`/`beta` are the CURRENT node's carrier(s) during traversal, not a
/// fixed field set once — [`rewrite_step`] updates them per subterm (a
/// `map`/`foldr` node's list argument is `List alpha` even though the node
/// itself has result carrier `beta`) and restores them before returning to
/// its caller, so a sibling subterm never sees a stale value.
pub(crate) struct ListDev<'k> {
    kernel: &'k mut Kernel,
    logic: LogicPrelude,
    names: ListNames,
    #[cfg_attr(not(test), allow(dead_code))]
    nat: Option<NatPrelude>,
    bridge: Option<ListNatBridge>,
    alpha: ExprId,
    beta: ExprId,
    next_fvar: u64,
}

impl<'k> ListDev<'k> {
    /// A development with only [`ListPrelude`] — everything
    /// [`list_only_rules`] needs, nothing [`default_rules`]'s
    /// `length_append` (or `count_append`, which needs [`crate::ListPerm`]
    /// only for its own `NameId` — see [`default_rules_with_perm`], which
    /// takes that directly rather than through a `ListDev` field) rule
    /// does. `alpha`/`beta` both start at `alpha`.
    pub(crate) fn new_list_only(
        kernel: &'k mut Kernel,
        logic: &LogicPrelude,
        names: &ListNames,
        alpha: ExprId,
    ) -> Self {
        Self {
            kernel,
            logic: *logic,
            names: *names,
            nat: None,
            bridge: None,
            alpha,
            beta: alpha,
            next_fvar: FVAR_BASE,
        }
    }

    /// A development with [`NatPrelude`] + [`ListNatBridge`] — required for
    /// [`default_rules`]'s `length_append` rule (and any rule set built
    /// with [`default_rules_with_perm`], which needs only [`crate::ListPerm`]'s
    /// own `NameId`, not a `ListDev` field).
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn new_full(
        kernel: &'k mut Kernel,
        logic: &LogicPrelude,
        names: &ListNames,
        nat: &NatPrelude,
        bridge: &ListNatBridge,
        alpha: ExprId,
    ) -> Self {
        Self {
            kernel,
            logic: *logic,
            names: *names,
            nat: Some(*nat),
            bridge: Some(*bridge),
            alpha,
            beta: alpha,
            next_fvar: FVAR_BASE,
        }
    }

    pub(crate) fn kernel(&mut self) -> &mut Kernel {
        self.kernel
    }

    pub(crate) fn names(&self) -> ListNames {
        self.names
    }

    pub(crate) fn has_bridge(&self) -> bool {
        self.bridge.is_some()
    }

    pub(crate) fn bridge(&self) -> ListNatBridge {
        self.bridge
            .expect("a Nat-crossing rule needs a `new_full` ListDev")
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn nat_prelude(&self) -> NatPrelude {
        self.nat
            .expect("a Nat-crossing rule needs a `new_full` ListDev")
    }

    pub(crate) fn alpha(&self) -> ExprId {
        self.alpha
    }

    pub(crate) fn set_alpha(&mut self, alpha: ExprId) {
        self.alpha = alpha;
    }

    pub(crate) fn beta(&self) -> ExprId {
        self.beta
    }

    pub(crate) fn set_beta(&mut self, beta: ExprId) {
        self.beta = beta;
    }

    pub(crate) fn fresh_fvar(&mut self) -> u64 {
        self.next_fvar += 1;
        self.next_fvar
    }

    fn zero_lvl(&mut self) -> LevelId {
        self.kernel.level_zero()
    }

    fn one_lvl(&mut self) -> LevelId {
        let z = self.zero_lvl();
        self.kernel.level_succ(z)
    }

    pub(crate) fn list_ty(&mut self) -> ExprId {
        let zero_lvl = self.zero_lvl();
        let alpha = self.alpha;
        let name = self.names.list;
        list_of(self.kernel, name, zero_lvl, alpha)
    }

    /// `List beta` — the current node's `map`/`foldr` RESULT carrier.
    pub(crate) fn list_ty_beta(&mut self) -> ExprId {
        let zero_lvl = self.zero_lvl();
        let beta = self.beta;
        let name = self.names.list;
        list_of(self.kernel, name, zero_lvl, beta)
    }

    pub(crate) fn nat_ty(&mut self) -> ExprId {
        self.kernel.const_(self.logic.nat, vec![])
    }

    pub(crate) fn nil(&mut self) -> ExprId {
        let zero_lvl = self.zero_lvl();
        let alpha = self.alpha;
        nil_of(self.kernel, self.names.nil, zero_lvl, alpha)
    }

    pub(crate) fn cons(&mut self, head: ExprId, tail: ExprId) -> ExprId {
        let zero_lvl = self.zero_lvl();
        let alpha = self.alpha;
        cons_of(self.kernel, self.names.cons, zero_lvl, alpha, head, tail)
    }

    pub(crate) fn append(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let alpha = self.alpha;
        append_of(self.kernel, self.names.append, alpha, a, b)
    }

    pub(crate) fn reverse(&mut self, a: ExprId) -> ExprId {
        let alpha = self.alpha;
        reverse_of(self.kernel, self.names.reverse, alpha, a)
    }

    pub(crate) fn length(&mut self, a: ExprId) -> ExprId {
        let alpha = self.alpha;
        length_of(self.kernel, self.names.length, alpha, a)
    }

    /// `map` at the current `(alpha, beta)`: `alpha -> beta` applied `f`,
    /// `List alpha` applied `l`.
    pub(crate) fn map(&mut self, f: ExprId, l: ExprId) -> ExprId {
        let alpha = self.alpha;
        let beta = self.beta;
        map_of(self.kernel, self.names.map, alpha, beta, f, l)
    }

    pub(crate) fn foldr(&mut self, f: ExprId, z: ExprId, l: ExprId) -> ExprId {
        let alpha = self.alpha;
        let beta = self.beta;
        foldr_of(self.kernel, self.names.foldr, alpha, beta, f, z, l)
    }

    /// `List.count a l` — monomorphic at `List Nat`; ignores `self.alpha`.
    pub(crate) fn count(&mut self, a: ExprId, l: ExprId) -> ExprId {
        let bridge = self.bridge();
        count_of(self.kernel, bridge.count, a, l)
    }

    pub(crate) fn nat_zero(&mut self) -> ExprId {
        self.kernel.const_(self.logic.nat_zero, vec![])
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn nat_succ(&mut self, a: ExprId) -> ExprId {
        nat_succ_of(self.kernel, self.logic.nat_succ, a)
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn nat_add(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let nat = self.nat_prelude();
        nat_add_of(self.kernel, nat.add, a, b)
    }

    // --- carrier-generic `Eq` layer ------------------------------------

    pub(crate) fn eq(&mut self, ty: ExprId, a: ExprId, b: ExprId) -> ExprId {
        let one = self.one_lvl();
        eq_of(self.kernel, &self.logic, one, ty, a, b)
    }

    pub(crate) fn refl(&mut self, ty: ExprId, a: ExprId) -> ExprId {
        let one = self.one_lvl();
        refl_of(self.kernel, &self.logic, one, ty, a)
    }

    pub(crate) fn symm(&mut self, ty: ExprId, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
        let one = self.one_lvl();
        let x_fv = self.fresh_fvar();
        symm_of(self.kernel, &self.logic, one, ty, a, b, h, x_fv)
    }

    pub(crate) fn trans(
        &mut self,
        ty: ExprId,
        a: ExprId,
        b: ExprId,
        c: ExprId,
        h1: ExprId,
        h2: ExprId,
    ) -> ExprId {
        let one = self.one_lvl();
        let x_fv = self.fresh_fvar();
        trans_of(self.kernel, &self.logic, one, ty, a, b, c, h1, h2, x_fv)
    }

    /// Congruence in an arbitrary one-hole context: `h : Eq ty_a a b` gives
    /// `Eq ty_b (f a) (f b)`. Both carrier types are explicit, unlike
    /// `NatOps::congr`/`IntDev::icongr` — see the module docs. Inlines
    /// `list_prelude::ops::congr_of`'s shape directly (rather than calling
    /// it) so `f` can be an ordinary `ListDev` closure instead of a raw
    /// `&mut Kernel` one — every other `ListDev` term builder needs `self`,
    /// not just `self.kernel()`.
    pub(crate) fn congr(
        &mut self,
        ty_a: ExprId,
        ty_b: ExprId,
        a: ExprId,
        b: ExprId,
        h: ExprId,
        f: &dyn Fn(&mut Self, ExprId) -> ExprId,
    ) -> ExprId {
        let x_fv = self.fresh_fvar();
        let fa = f(self, a);
        let motive = {
            let x = self.kernel.fvar(x_fv);
            let concl = {
                let fx = f(self, x);
                self.eq(ty_b, fa, fx)
            };
            let hyp = self.eq(ty_a, a, x);
            let anon = self.kernel.anon();
            let inner = self.kernel.lam(anon, hyp, concl, BinderInfo::Default);
            self.lam_fv(x_fv, ty_a, inner)
        };
        let refl_case = self.refl(ty_b, fa);
        let zero = self.zero_lvl();
        let one = self.one_lvl();
        let rec_name = self.logic.eq_rec;
        let rec = self.kernel.const_(rec_name, vec![zero, one]);
        self.apply(rec, &[ty_a, a, motive, refl_case, b, h])
    }

    pub(crate) fn chain(
        &mut self,
        ty: ExprId,
        start: ExprId,
        steps: &[(ExprId, ExprId)],
    ) -> (ExprId, ExprId) {
        let mut current = start;
        let mut proof = self.refl(ty, start);
        for &(next, step) in steps {
            proof = self.trans(ty, start, current, next, proof, step);
            current = next;
        }
        (current, proof)
    }

    pub(crate) fn apply(&mut self, head: ExprId, args: &[ExprId]) -> ExprId {
        crate::list_prelude::ops::apply_all(self.kernel, head, args)
    }

    pub(crate) fn lemma(&mut self, name: NameId, args: &[ExprId]) -> ExprId {
        let c = self.kernel.const_(name, vec![]);
        self.apply(c, args)
    }

    pub(crate) fn lam_fv(&mut self, fv: u64, ty: ExprId, body: ExprId) -> ExprId {
        lam_fvar(self.kernel, fv, ty, body, BinderInfo::Default)
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn pi_fv(&mut self, fv: u64, ty: ExprId, body: ExprId) -> ExprId {
        pi_fvar(self.kernel, fv, ty, body, BinderInfo::Default)
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn declare_theorem(
        &mut self,
        name: NameId,
        ty: ExprId,
        value: ExprId,
    ) -> Result<(), KernelError> {
        self.kernel.add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })?;
        Ok(())
    }
}

// --- rules ----------------------------------------------------------------

/// A rule's `(lhs, rhs)` carrier — needed explicitly because, unlike
/// `simp::nat`/`simp::int` (one fixed carrier), a `List` rule's two sides
/// can be typed at `List alpha`, `List beta`, `Nat`, or bare `beta`
/// (`foldr`'s return type). `Kernel::infer` on a rule's reconstructed
/// `lhs`/`rhs` is NOT a safe way to recover this: every symbolic goal this
/// producer runs against carries free variables that are not yet
/// universally quantified at proof-search time (quantification happens
/// only once a caller wraps the finished proof in `pi_fv`/`lam_fv`), so
/// `infer` routinely fails on them mid-search — this must be a STATIC
/// property of the rule, not inferred per call.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Carrier {
    /// `List alpha` — the ambient list carrier.
    ListAlpha,
    /// `List beta` — a `map`-shaped rule's result carrier.
    ListBeta,
    /// `Nat`.
    Nat,
    /// Bare `beta` (`foldr`'s accumulator/return type).
    #[cfg_attr(not(test), allow(dead_code))]
    Beta,
}

impl Carrier {
    fn ty(self, d: &mut ListDev<'_>) -> ExprId {
        match self {
            Carrier::ListAlpha => d.list_ty(),
            Carrier::ListBeta => d.list_ty_beta(),
            Carrier::Nat => d.nat_ty(),
            Carrier::Beta => d.beta(),
        }
    }
}

/// One oriented rewrite rule over `List` (or a `List`-to-`Nat` boundary
/// rule like `length_map`/`length_append`/`count_append`): a previously-
/// declared lemma's `arity`-ary `(lhs, rhs)` pattern, or `name = None` for a
/// DEFINITIONAL identity the recursor's own base/step case already gives —
/// see the module docs on `nil_append` and friends. When `name` is `None`
/// the emitted step is `Eq.refl`, not a lemma citation, and the KERNEL's own
/// `def_eq` (not this producer) is what confirms the two sides really are
/// definitionally equal.
#[derive(Clone, Copy)]
pub(crate) struct Rule {
    pub name: Option<NameId>,
    pub arity: usize,
    pub orientation: Orientation,
    pub carrier: Carrier,
    /// A NAMED lemma's own IMPLICIT type arguments (`{alpha}`, or
    /// `{alpha, beta}` for a `map`-shaped lemma), which `Rule::build`'s
    /// pattern variables do NOT include — `List.append_nil : ∀ {α} l, …`
    /// must be applied `append_nil alpha l`, not `append_nil l`, or the
    /// citation is simply the wrong term (an application short one
    /// argument), not a type error the matcher would catch. Ignored (never
    /// called) when `name` is `None`.
    pub type_args: fn(&mut ListDev<'_>) -> Vec<ExprId>,
    pub build: fn(&mut ListDev<'_>, &[ExprId]) -> (ExprId, ExprId),
}

fn no_type_args(_d: &mut ListDev<'_>) -> Vec<ExprId> {
    Vec::new()
}
fn alpha_type_args(d: &mut ListDev<'_>) -> Vec<ExprId> {
    vec![d.alpha()]
}
#[cfg_attr(not(test), allow(dead_code))]
fn alpha_beta_type_args(d: &mut ListDev<'_>) -> Vec<ExprId> {
    vec![d.alpha(), d.beta()]
}

fn r_append_nil(d: &mut ListDev<'_>, a: &[ExprId]) -> (ExprId, ExprId) {
    let nil = d.nil();
    let lhs = d.append(a[0], nil);
    (lhs, a[0])
}
fn r_nil_append(d: &mut ListDev<'_>, a: &[ExprId]) -> (ExprId, ExprId) {
    let nil = d.nil();
    let lhs = d.append(nil, a[0]);
    (lhs, a[0])
}
#[cfg_attr(not(test), allow(dead_code))]
fn r_append_assoc(d: &mut ListDev<'_>, a: &[ExprId]) -> (ExprId, ExprId) {
    let ab = d.append(a[0], a[1]);
    let lhs = d.append(ab, a[2]);
    let bc = d.append(a[1], a[2]);
    let rhs = d.append(a[0], bc);
    (lhs, rhs)
}
fn r_reverse_nil(d: &mut ListDev<'_>, _a: &[ExprId]) -> (ExprId, ExprId) {
    let nil = d.nil();
    let lhs = d.reverse(nil);
    (lhs, nil)
}
#[cfg_attr(not(test), allow(dead_code))]
fn r_reverse_reverse(d: &mut ListDev<'_>, a: &[ExprId]) -> (ExprId, ExprId) {
    let r = d.reverse(a[0]);
    let lhs = d.reverse(r);
    (lhs, a[0])
}
fn r_length_nil(d: &mut ListDev<'_>, _a: &[ExprId]) -> (ExprId, ExprId) {
    let nil = d.nil();
    let lhs = d.length(nil);
    let z = d.nat_zero();
    (lhs, z)
}
#[cfg_attr(not(test), allow(dead_code))]
fn r_length_map(d: &mut ListDev<'_>, a: &[ExprId]) -> (ExprId, ExprId) {
    // a[0] : alpha -> beta, a[1] : List alpha
    let mapped = d.map(a[0], a[1]);
    let lhs = {
        let saved = d.alpha();
        d.set_alpha(d.beta());
        let r = d.length(mapped);
        d.set_alpha(saved);
        r
    };
    let rhs = d.length(a[1]);
    (lhs, rhs)
}
fn r_map_nil(d: &mut ListDev<'_>, a: &[ExprId]) -> (ExprId, ExprId) {
    let nil = d.nil();
    let lhs = d.map(a[0], nil);
    let rhs = {
        let saved = d.alpha();
        d.set_alpha(d.beta());
        let r = d.nil();
        d.set_alpha(saved);
        r
    };
    (lhs, rhs)
}
#[cfg_attr(not(test), allow(dead_code))]
fn r_map_cons(d: &mut ListDev<'_>, a: &[ExprId]) -> (ExprId, ExprId) {
    // a = [f, head, tail]
    let cons_h_t = d.cons(a[1], a[2]);
    let lhs = d.map(a[0], cons_h_t);
    let f_head = d.apply(a[0], &[a[1]]);
    let mapped_tail = d.map(a[0], a[2]);
    let rhs = {
        let saved = d.alpha();
        d.set_alpha(d.beta());
        let r = d.cons(f_head, mapped_tail);
        d.set_alpha(saved);
        r
    };
    (lhs, rhs)
}
#[cfg_attr(not(test), allow(dead_code))]
fn r_foldr_nil(d: &mut ListDev<'_>, a: &[ExprId]) -> (ExprId, ExprId) {
    let nil = d.nil();
    let lhs = d.foldr(a[0], a[1], nil);
    (lhs, a[1])
}
#[cfg_attr(not(test), allow(dead_code))]
fn r_length_append(d: &mut ListDev<'_>, a: &[ExprId]) -> (ExprId, ExprId) {
    let app = d.append(a[0], a[1]);
    let lhs = d.length(app);
    let l1 = d.length(a[0]);
    let l2 = d.length(a[1]);
    let rhs = d.nat_add(l1, l2);
    (lhs, rhs)
}
#[cfg_attr(not(test), allow(dead_code))]
fn r_count_append(d: &mut ListDev<'_>, a: &[ExprId]) -> (ExprId, ExprId) {
    // a = [elem, l1, l2] -- monomorphic at List Nat.
    let app = d.append(a[1], a[2]);
    let lhs = d.count(a[0], app);
    let c1 = d.count(a[0], a[1]);
    let c2 = d.count(a[0], a[2]);
    let rhs = d.nat_add(c1, c2);
    (lhs, rhs)
}

/// The `List`-only default rules — need nothing beyond [`LogicPrelude`] and
/// the four NAMED lemmas' own `NameId`s (not a whole `ListPrelude`, which
/// does not exist yet at the point `list_prelude::theorems` needs to call
/// this — its four theorems are this function's own `append_nil`/
/// `append_assoc`/`reverse_reverse`/`length_map` parameters, each a plain
/// local variable there, not a struct field). See the module docs' two-tier
/// explanation.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn list_only_rules(
    append_nil: NameId,
    append_assoc: NameId,
    reverse_reverse: NameId,
    length_map: NameId,
) -> Vec<Rule> {
    use Carrier::{Beta, ListAlpha, ListBeta, Nat};
    use Orientation::Forward;
    vec![
        Rule {
            name: Some(append_nil),
            arity: 1,
            orientation: Forward,
            carrier: ListAlpha,
            type_args: alpha_type_args,
            build: r_append_nil,
        },
        Rule {
            name: None,
            arity: 1,
            orientation: Forward,
            carrier: ListAlpha,
            type_args: no_type_args,
            build: r_nil_append,
        },
        Rule {
            name: Some(append_assoc),
            arity: 3,
            orientation: Forward,
            carrier: ListAlpha,
            type_args: alpha_type_args,
            build: r_append_assoc,
        },
        Rule {
            name: None,
            arity: 0,
            orientation: Forward,
            carrier: ListAlpha,
            type_args: no_type_args,
            build: r_reverse_nil,
        },
        Rule {
            name: Some(reverse_reverse),
            arity: 1,
            orientation: Forward,
            carrier: ListAlpha,
            type_args: alpha_type_args,
            build: r_reverse_reverse,
        },
        Rule {
            name: None,
            arity: 0,
            orientation: Forward,
            carrier: Nat,
            type_args: no_type_args,
            build: r_length_nil,
        },
        Rule {
            name: Some(length_map),
            arity: 2,
            orientation: Forward,
            carrier: Nat,
            type_args: alpha_beta_type_args,
            build: r_length_map,
        },
        Rule {
            name: None,
            arity: 1,
            orientation: Forward,
            carrier: ListBeta,
            type_args: no_type_args,
            build: r_map_nil,
        },
        Rule {
            name: None,
            arity: 3,
            orientation: Forward,
            carrier: ListBeta,
            type_args: no_type_args,
            build: r_map_cons,
        },
        Rule {
            name: None,
            arity: 2,
            orientation: Forward,
            carrier: Beta,
            type_args: no_type_args,
            build: r_foldr_nil,
        },
    ]
}

/// [`list_only_rules`] plus `length_append` (needs [`ListNatBridge`]).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn default_rules(
    append_nil: NameId,
    append_assoc: NameId,
    reverse_reverse: NameId,
    length_map: NameId,
    length_append: NameId,
) -> Vec<Rule> {
    let mut rules = list_only_rules(append_nil, append_assoc, reverse_reverse, length_map);
    rules.push(Rule {
        name: Some(length_append),
        arity: 2,
        orientation: Orientation::Forward,
        carrier: Carrier::Nat,
        type_args: alpha_type_args,
        build: r_length_append,
    });
    rules
}

/// [`default_rules`] plus `count_append` — the FULL default set ADR-1586
/// §4 named. Split out from [`default_rules`] because `count_append` needs
/// [`ListPerm`], built strictly after [`ListNatBridge`].
#[allow(clippy::too_many_arguments)]
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn default_rules_with_perm(
    append_nil: NameId,
    append_assoc: NameId,
    reverse_reverse: NameId,
    length_map: NameId,
    length_append: NameId,
    count_append: NameId,
) -> Vec<Rule> {
    let mut rules = default_rules(
        append_nil,
        append_assoc,
        reverse_reverse,
        length_map,
        length_append,
    );
    rules.push(Rule {
        name: Some(count_append),
        arity: 3,
        orientation: Orientation::Forward,
        carrier: Carrier::Nat,
        type_args: no_type_args,
        build: r_count_append,
    });
    rules
}

/// `List.append_assoc` in the BACKWARD direction, as a caller-supplied
/// extra — see the module docs on why adding this alongside the (forward)
/// default oscillates forever rather than terminating.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn rule_append_assoc_backward(append_assoc: NameId) -> Rule {
    Rule {
        name: Some(append_assoc),
        arity: 3,
        orientation: Orientation::Backward,
        carrier: Carrier::ListAlpha,
        type_args: alpha_type_args,
        build: r_append_assoc,
    }
}

// --- singleton rule constructors -------------------------------------
//
// `list_prelude::theorems` declares `append_assoc`/`append_nil`/
// `reverse_append`/`reverse_reverse`/`length_map` itself, sequentially, in
// ONE function -- so at the point a given theorem's OWN base case is being
// built, the theorems declared LATER in that same function do not exist
// yet as `NameId`s, and [`list_only_rules`]/[`default_rules`] cannot be
// called (they need all four). Each retirement there instead builds the
// minimal rule SET its own base case actually needs, one singleton rule at
// a time, from these constructors.

/// `List.append_nil` as a single-rule set entry (needs the declared
/// `NameId`, since it is a real citation, not a definitional refl).
pub(crate) fn rule_append_nil(append_nil: NameId) -> Rule {
    Rule {
        name: Some(append_nil),
        arity: 1,
        orientation: Orientation::Forward,
        carrier: Carrier::ListAlpha,
        type_args: alpha_type_args,
        build: r_append_nil,
    }
}

/// `append nil l = l`, definitional (no `NameId` needed) — see the module
/// docs on `nil_append`.
pub(crate) fn rule_nil_append() -> Rule {
    Rule {
        name: None,
        arity: 1,
        orientation: Orientation::Forward,
        carrier: Carrier::ListAlpha,
        type_args: no_type_args,
        build: r_nil_append,
    }
}

/// `reverse nil = nil`, definitional.
pub(crate) fn rule_reverse_nil() -> Rule {
    Rule {
        name: None,
        arity: 0,
        orientation: Orientation::Forward,
        carrier: Carrier::ListAlpha,
        type_args: no_type_args,
        build: r_reverse_nil,
    }
}

/// `length nil = zero`, definitional.
pub(crate) fn rule_length_nil() -> Rule {
    Rule {
        name: None,
        arity: 0,
        orientation: Orientation::Forward,
        carrier: Carrier::Nat,
        type_args: no_type_args,
        build: r_length_nil,
    }
}

/// `map f nil = nil`, definitional.
pub(crate) fn rule_map_nil() -> Rule {
    Rule {
        name: None,
        arity: 1,
        orientation: Orientation::Forward,
        carrier: Carrier::ListBeta,
        type_args: no_type_args,
        build: r_map_nil,
    }
}

// --- matching (identical shape to `super::nat`/`super::int`) -------------

fn instantiate(d: &mut ListDev<'_>, rule: &Rule) -> (Vec<ExprId>, ExprId, ExprId) {
    let vars: Vec<ExprId> = (0..rule.arity)
        .map(|_| {
            let fv = d.fresh_fvar();
            d.kernel().fvar(fv)
        })
        .collect();
    let (lhs, rhs) = (rule.build)(d, &vars);
    (vars, lhs, rhs)
}

fn try_match(
    d: &mut ListDev<'_>,
    pattern_vars: &[ExprId],
    pattern: ExprId,
    target: ExprId,
    bindings: &mut [Option<ExprId>],
) -> bool {
    if let Some(pos) = pattern_vars.iter().position(|&v| v == pattern) {
        return if let Some(bound) = bindings[pos] {
            bound == target
        } else {
            bindings[pos] = Some(target);
            true
        };
    }
    if pattern == target {
        return true;
    }
    let pn = d.kernel().expr_node(pattern).clone();
    let tn = d.kernel().expr_node(target).clone();
    match (pn, tn) {
        (ExprNode::App(f1, a1), ExprNode::App(f2, a2)) => {
            try_match(d, pattern_vars, f1, f2, bindings)
                && try_match(d, pattern_vars, a1, a2, bindings)
        }
        _ => false,
    }
}

fn try_rewrite_at(d: &mut ListDev<'_>, rules: &[Rule], e: ExprId) -> Option<(ExprId, ExprId)> {
    for rule in rules {
        let (vars, lhs_pat, rhs_pat) = instantiate(d, rule);
        let pattern = match rule.orientation {
            Orientation::Forward => lhs_pat,
            Orientation::Backward => rhs_pat,
        };
        let mut bindings: Vec<Option<ExprId>> = vec![None; rule.arity];
        if !try_match(d, &vars, pattern, e, &mut bindings) {
            continue;
        }
        let args: Vec<ExprId> = match bindings.into_iter().collect::<Option<Vec<_>>>() {
            Some(a) => a,
            None => continue,
        };
        let (lhs_c, rhs_c) = (rule.build)(d, &args);
        // The rule's own STATIC carrier -- never `Kernel::infer`, which
        // routinely fails on a symbolic goal's not-yet-quantified free
        // variables mid-search (see the `Carrier` doc).
        let ty = rule.carrier.ty(d);
        let lemma_proof = match rule.name {
            Some(name) => {
                let mut full_args = (rule.type_args)(d);
                full_args.extend_from_slice(&args);
                d.lemma(name, &full_args)
            }
            None => {
                // Definitional identity: the recursor's own base/step case
                // gives this for free, so the "citation" is `Eq.refl` at the
                // LHS (or RHS) side the kernel's own `def_eq` confirms
                // against the other -- see the `Rule` doc.
                match rule.orientation {
                    Orientation::Forward => d.refl(ty, lhs_c),
                    Orientation::Backward => d.refl(ty, rhs_c),
                }
            }
        };
        let (new_e, proof) = match rule.orientation {
            Orientation::Forward => {
                debug_assert_eq!(lhs_c, e, "matched pattern must reconstruct the target");
                (rhs_c, lemma_proof)
            }
            Orientation::Backward => {
                debug_assert_eq!(rhs_c, e, "matched pattern must reconstruct the target");
                (lhs_c, d.symm(ty, lhs_c, rhs_c, lemma_proof))
            }
        };
        return Some((new_e, proof));
    }
    None
}

fn spine(d: &mut ListDev<'_>, e: ExprId) -> (ExprId, Vec<ExprId>) {
    let mut args = Vec::new();
    let mut head = e;
    loop {
        let node = d.kernel().expr_node(head).clone();
        let ExprNode::App(f, a) = node else { break };
        args.push(a);
        head = f;
    }
    args.reverse();
    (head, args)
}

fn head_const(d: &mut ListDev<'_>, e: ExprId) -> Option<NameId> {
    match d.kernel().expr_node(e).clone() {
        ExprNode::Const(n, _) => Some(n),
        _ => None,
    }
}

/// Set `d.alpha()`/`d.beta()` from `e`'s OWN head operator and spine (the
/// implicit type arguments every `List` operator's application carries
/// explicitly, per the module docs) — done UNCONDITIONALLY before either
/// matching or descending at `e`, not only on a failed match. A rule's own
/// pattern-`build` closure (`d.nil()`, `d.map(..)`, …) reads `self.alpha`/
/// `self.beta` internally, so `try_rewrite_at` matching `e` against a
/// rule's pattern needs the SAME correction `rewrite_step_descend`'s own
/// dispatch applies before recursing — otherwise a nested heterogeneous
/// node (`length (map f l)`: the outer `length`'s own carrier is `beta`,
/// but its argument `map f l`'s OWN head carries the original `alpha`)
/// inherits the WRONG ambient value from its parent and no rule matches,
/// even though one should. Found by running the `length_map` retirement in
/// `list_prelude::theorems`, which failed `SidesDiffer` before this fix —
/// not by inspection.
fn set_ambient_carrier(d: &mut ListDev<'_>, name: NameId, args: &[ExprId]) {
    let p = d.names();
    let alpha_only = (name == p.append && args.len() == 3)
        || (name == p.cons && args.len() == 3)
        || (name == p.reverse && args.len() == 2)
        || (name == p.length && args.len() == 2);
    if alpha_only {
        d.set_alpha(args[0]);
    } else if (name == p.map && args.len() == 4) || (name == p.foldr && args.len() == 5) {
        d.set_alpha(args[0]);
        d.set_beta(args[1]);
    } else if d.has_bridge() && name == d.bridge().count && args.len() == 2 {
        // `List.count` is monomorphic at `List Nat` -- independent of
        // whatever the ambient `alpha` was inherited from a parent node.
        let nat = d.nat_ty();
        d.set_alpha(nat);
    }
}

/// Outermost-first: try `e` itself, then descend into the ONE argument slot
/// each recognised operator recurses on structurally, lifting a child
/// rewrite via [`ListDev::congr`] with every other slot held fixed in the
/// congruence closure. `append`/`cons` recurse into their `List`-typed
/// operand(s) (`cons` only into the tail — the head is an opaque `α`
/// element no default rule ever touches); `reverse`/`length`/`map`/
/// `foldr`/`count` each recurse into their single `List`-typed argument,
/// holding any function/accumulator argument fixed.
///
/// `d.alpha()`/`d.beta()` on ENTRY must already match whatever the CALLER's
/// own context needs — this function itself corrects them for `e`'s own
/// head ([`set_ambient_carrier`]) before doing anything else, and restores
/// the entry value before returning, so a sibling subterm a caller
/// processes next never sees a value this call changed.
fn rewrite_step(d: &mut ListDev<'_>, rules: &[Rule], e: ExprId) -> Option<(ExprId, ExprId)> {
    let saved_alpha = d.alpha();
    let saved_beta = d.beta();
    let (head, args) = spine(d, e);
    let name = head_const(d, head);
    if let Some(name) = name {
        set_ambient_carrier(d, name, &args);
    }
    let result = if let Some(step) = try_rewrite_at(d, rules, e) {
        Some(step)
    } else {
        name.and_then(|name| rewrite_step_descend(d, rules, name, &args))
    };
    d.set_alpha(saved_alpha);
    d.set_beta(saved_beta);
    result
}

/// `e`'s own ambient carrier is already set by [`rewrite_step`]
/// ([`set_ambient_carrier`]) before this runs.
fn rewrite_step_descend(
    d: &mut ListDev<'_>,
    rules: &[Rule],
    name: NameId,
    args: &[ExprId],
) -> Option<(ExprId, ExprId)> {
    let p = d.names();

    if name == p.append && args.len() == 3 {
        let ty = d.list_ty();
        return rewrite_binary(d, rules, ty, args[1], args[2], &|d, x, y| d.append(x, y));
    }
    if name == p.cons && args.len() == 3 {
        let ty = d.list_ty();
        let elem = args[1];
        return rewrite_unary(d, rules, ty, ty, args[2], &move |d, x| d.cons(elem, x));
    }
    if name == p.reverse && args.len() == 2 {
        let ty = d.list_ty();
        return rewrite_unary(d, rules, ty, ty, args[1], &|d, x| d.reverse(x));
    }
    if name == p.length && args.len() == 2 {
        let ty = d.list_ty();
        let nat = d.nat_ty();
        return rewrite_unary(d, rules, ty, nat, args[1], &|d, x| d.length(x));
    }
    if name == p.map && args.len() == 4 {
        let ty = d.list_ty();
        let out_ty = d.list_ty_beta();
        let f = args[2];
        return rewrite_unary(d, rules, ty, out_ty, args[3], &move |d, x| d.map(f, x));
    }
    if name == p.foldr && args.len() == 5 {
        let ty = d.list_ty();
        let out_ty = d.beta();
        let f = args[2];
        let z = args[3];
        return rewrite_unary(d, rules, ty, out_ty, args[4], &move |d, x| d.foldr(f, z, x));
    }
    if d.has_bridge() && name == d.bridge().count && args.len() == 2 {
        let elem = args[0];
        let ty = d.list_ty();
        let nat = d.nat_ty();
        return rewrite_unary(d, rules, ty, nat, args[1], &move |d, x| d.count(elem, x));
    }
    None
}

fn rewrite_binary(
    d: &mut ListDev<'_>,
    rules: &[Rule],
    ty: ExprId,
    u: ExprId,
    v: ExprId,
    op: &dyn Fn(&mut ListDev<'_>, ExprId, ExprId) -> ExprId,
) -> Option<(ExprId, ExprId)> {
    if let Some((u2, hu)) = rewrite_step(d, rules, u) {
        let new_e = op(d, u2, v);
        let proof = d.congr(ty, ty, u, u2, hu, &|d, x| op(d, x, v));
        return Some((new_e, proof));
    }
    if let Some((v2, hv)) = rewrite_step(d, rules, v) {
        let new_e = op(d, u, v2);
        let proof = d.congr(ty, ty, v, v2, hv, &|d, x| op(d, u, x));
        return Some((new_e, proof));
    }
    None
}

fn rewrite_unary(
    d: &mut ListDev<'_>,
    rules: &[Rule],
    ty: ExprId,
    result_ty: ExprId,
    u: ExprId,
    op: &dyn Fn(&mut ListDev<'_>, ExprId) -> ExprId,
) -> Option<(ExprId, ExprId)> {
    let (u2, hu) = rewrite_step(d, rules, u)?;
    let new_e = op(d, u2);
    // `result_ty` is the caller's STATIC knowledge of the operator's result
    // carrier (`length`/`count` change carrier, `List a -> Nat`; `reverse`/
    // `cons`/`map`'s own list result does not) -- never `Kernel::infer`,
    // which routinely fails on a symbolic goal's not-yet-quantified free
    // variables mid-search (see `Carrier`'s doc, the same reasoning).
    let proof = d.congr(ty, result_ty, u, u2, hu, op);
    Some((new_e, proof))
}

fn rewrite_to_fixpoint(
    d: &mut ListDev<'_>,
    rules: &[Rule],
    ty: ExprId,
    start: ExprId,
) -> Result<(ExprId, ExprId, usize), Decline> {
    let mut current = start;
    let mut steps: Vec<(ExprId, ExprId)> = Vec::new();
    for _ in 0..MAX_STEPS {
        if let Some((next, proof)) = rewrite_step(d, rules, current) {
            steps.push((next, proof));
            current = next;
        } else {
            let (_last, proof) = d.chain(ty, start, &steps);
            return Ok((current, proof, steps.len()));
        }
    }
    if rewrite_step(d, rules, current).is_some() {
        return Err(Decline::BudgetExceeded);
    }
    let (_last, proof) = d.chain(ty, start, &steps);
    Ok((current, proof, steps.len()))
}

fn prove_eq_inner(
    d: &mut ListDev<'_>,
    rules: &[Rule],
    ty: ExprId,
    lhs: ExprId,
    rhs: ExprId,
    verify: bool,
) -> Result<ExprId, Decline> {
    let (lhs_final, lhs_proof, lhs_steps) = rewrite_to_fixpoint(d, rules, ty, lhs)?;
    let (rhs_final, rhs_proof, rhs_steps) = rewrite_to_fixpoint(d, rules, ty, rhs)?;
    if lhs_steps == 0 && rhs_steps == 0 {
        return Err(Decline::NoProgress);
    }
    if verify && lhs_final != rhs_final {
        return Err(Decline::SidesDiffer);
    }
    let rhs_back = d.symm(ty, rhs, rhs_final, rhs_proof);
    Ok(d.trans(ty, lhs, lhs_final, rhs, lhs_proof, rhs_back))
}

/// Prove `Eq ty lhs rhs` (`ty` is the carrier BOTH sides share — `List α` or
/// `Nat`, the caller's choice, matching `d.alpha()`/`d.beta()` on entry) by
/// rewriting both sides to a fixed point under `rules`, or decline.
///
/// # Errors
///
/// [`Decline::NoProgress`] when neither side matched any rule;
/// [`Decline::BudgetExceeded`] when one side did not reach a fixed point
/// within [`MAX_STEPS`]; [`Decline::SidesDiffer`] when both sides reached a
/// fixed point and the two differ.
pub(crate) fn prove_eq(
    d: &mut ListDev<'_>,
    rules: &[Rule],
    ty: ExprId,
    lhs: ExprId,
    rhs: ExprId,
) -> Result<ExprId, Decline> {
    prove_eq_inner(d, rules, ty, lhs, rhs, true)
}

/// [`prove_eq`] with the procedure's own convergence check switched off —
/// see [`super::nat::prove_eq_unverified`].
///
/// # Errors
///
/// As [`prove_eq`], minus [`Decline::SidesDiffer`].
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn prove_eq_unverified(
    d: &mut ListDev<'_>,
    rules: &[Rule],
    ty: ExprId,
    lhs: ExprId,
    rhs: ExprId,
) -> Result<ExprId, Decline> {
    prove_eq_inner(d, rules, ty, lhs, rhs, false)
}

#[cfg_attr(not(test), allow(dead_code))]
fn parse_eq_goal(d: &mut ListDev<'_>, e: ExprId, ty: ExprId) -> Result<(ExprId, ExprId), Decline> {
    let (head, args) = spine(d, e);
    let name = head_const(d, head).ok_or(Decline::GoalNotAtomic)?;
    if name == d.logic.eq && args.len() == 3 && args[0] == ty {
        return Ok((args[1], args[2]));
    }
    Err(Decline::GoalNotAtomic)
}

/// Prove `goal` (`Eq ty lhs rhs`) by rewriting both sides to a fixed point
/// under `rules`, or decline.
///
/// # Errors
///
/// [`Decline::GoalNotAtomic`] when `goal`'s head is not `Eq ty`; otherwise
/// as [`prove_eq`].
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn prove(
    d: &mut ListDev<'_>,
    rules: &[Rule],
    ty: ExprId,
    goal: ExprId,
) -> Result<ExprId, Decline> {
    let (lhs, rhs) = parse_eq_goal(d, goal, ty)?;
    prove_eq(d, rules, ty, lhs, rhs)
}

#[cfg(test)]
mod tests;

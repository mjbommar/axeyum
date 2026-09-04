//! ADR-1599: `ring::generic` — the commutative-ring equality fragment
//! (`ring::nat`/`ring::int`/`ring::rat`) retargeted at an arbitrary
//! `(R : Alg.CommRing)` term instead of a fixed `NatPrelude`/`IntPrelude`/
//! `RatPrelude`, and — the deliverable's own point — at `(R : AlgS.CommRing)`
//! for a SETOID carrier (`CReal`, `Complex`) whose equality is a *defined*
//! relation, never the kernel's `Eq`.
//!
//! Built by EXTENDING `linarith::generic`'s own `Backend` shape (ADR-1592),
//! not forking a new design: every place the normalizer needs a congruence
//! or transport step goes through one of six wrapper methods on [`Problem`]
//! (`refl`/`symm`/`trans`/`congr_add`/`congr_mul`/`congr_neg`) and one parser
//! (`as_eq`), and only those are backend-aware. `Backend::KernelEq` is
//! unchanged `Eq.rec`-based transport (`nat_prelude::structures`);
//! `Backend::Setoid` uses `AlgS.CommRing`'s own `addCongr`/`mulCongr`/
//! `negCongr` FIELDS directly — a setoid has no generic `Eq.rec`-shaped
//! transport for an arbitrary closure (ADR-1588), so each `congr` call
//! carries a small structural [`AddCtx`]/[`MulCtx`] shape describing what it
//! rewrites under, read off the closure at each call site exactly as
//! `linarith::generic::AddCtx`/`LeCtx` already do.
//!
//! ## The fragment, honestly short of `ring::rat`
//!
//! Parses `t₁ = t₂` (kernel `Eq` or the record's own `equiv`) where each `t`
//! is built from atoms, `zero`, `one`, `add`, `mul`, `neg` over one fixed
//! `(R : Alg.CommRing)`/`(R : AlgS.CommRing)` term, normalizes both sides to
//! a canonical **sorted sum of sorted monomials** (`ring::rat`'s exact
//! shape), and emits a kernel proof term when they agree.
//!
//! - **Coefficients capped at magnitude 1** (`ring::rat`'s own restriction,
//!   ported unchanged): `AlgS.CommRing`/`Alg.CommRing` have no generic
//!   `ofNat` numeral embedding (unlike `Alg.OrderedRing`, ADR-1585, which
//!   built one specifically for `linarith::generic`), so a numeral is
//!   recognised only as `zero`, `one`, or `neg` of either — `2` spelled as a
//!   literal numeral is outside the fragment (`add one one` still works,
//!   through the ordinary additive route).
//! - **`neg` does NOT distribute over `add`.** `Alg.CommRing`'s `negAdd`
//!   field states the additive-inverse law (`add a (neg a) = zero`), not
//!   `neg (add a b) = add (neg a) (neg b)` — deriving the latter generically
//!   needs an extra `Alg.groupInvUnique`-style uniqueness argument over the
//!   ring's derived additive group, real work not attempted here (see
//!   ADR-1599's Alternatives). A source term shaped `neg (add u v)` is
//!   therefore parsed as one opaque atom, sound but incomplete — the same
//!   "declined, not silently wrong" contract `linarith::generic` uses for
//!   `<`. `neg` DOES distribute over `mul` (`mul_neg_proof`/`neg_mul_proof`
//!   below) and cancels under double negation (`Problem::neg_neg`), both
//!   fully generic.
//! - **`div`/`sub` are simply not selectors on `Alg.CommRing`/`AlgS.
//!   CommRing`** (unlike `Rat`, which has both as prelude-level
//!   definitions), so [`Decline::NonRing`] is unreachable from this
//!   module — nothing to decline; any subterm that is not `add`/`mul`/`neg`/
//!   a recognised numeral is simply an atom.
//!
//! ## Derived primitives (no new global declarations)
//!
//! Three facts `ring::rat` gets from `RatPrelude` fields directly are not
//! primitive fields on `Alg.CommRing`/`AlgS.CommRing`, so this module derives
//! them ONCE per `Problem` from what IS generic and already built:
//!
//! - `mul_zero : mul x zero = zero` — `Alg.ringMulZero`/`AlgS.mul_zero`
//!   (both already generic over `Ring`, `rat_prelude::algebra_instances`/
//!   `nat_prelude::structures_setoid`), applied at `R.toRing`/`R.toRingS`.
//! - `mul_neg_one : mul x (neg one) = neg x` — `Alg.mul_neg_one`/`AlgS.
//!   mul_neg_one` (ditto), applied the same way.
//! - `neg_neg : neg (neg x) = x` — `AlgS.neg_neg` is already `Ring`-scoped
//!   (ADR-1592) and applied directly; the `Eq`-flavored `Alg.neg_neg` is
//!   `Group`-scoped only, so [`Problem::new`] composes `Alg.CommRing.toRing`
//!   → `Alg.Ring.toCommGroup` → `Alg.CommGroup.toGroup` (the exact
//!   composition `Alg.mul_neg_one`'s own proof already uses) and applies
//!   `Alg.neg_neg` at the derived group term.
//!
//! From `mul_neg_one` and `mul_assoc`/`mul_comm`, [`Problem::mul_neg_proof`]/
//! [`Problem::neg_mul_proof`] derive `mul x (neg y) = neg (mul x y)` and
//! `mul (neg x) y = neg (mul x y)` locally (proof-term composition, not a
//! declaration) — the two facts `combine_mono_signs` (this module's
//! `ring::rat::apply_mono_signs` twin) needs to combine two signed
//! monomials, and the fact `flatten_neg`'s `mul` case needs to distribute a
//! source-level `neg` into a product.
//!
//! ## A closure-capture discipline, not an accident
//!
//! Every method here that threads a rewrite step through `congr_add`/
//! `congr_mul` (both `&mut self`) passes a `&dyn Fn(&mut Kernel, ExprId) ->
//! ExprId` closure that must NOT capture `self` — `self.congr_add(k, ...,
//! &|k2, t| { ... self.add ... })` does not borrow-check (the call needs
//! `&mut self` for its whole duration while the closure argument also wants
//! `&self`). Every such closure below captures only `Copy` locals
//! (`self.add`/`self.mul` copied out beforehand) or the free `*_ctx`
//! functions with a cloned `atoms`/`ctx` snapshot — `linarith::generic::
//! OpCtx`'s exact discipline, applied here to THREE operators instead of one.

#![allow(dead_code)]

use crate::ExprNode;
use crate::Kernel;
use crate::LogicPrelude;
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::nat_prelude::structures::sel;
use crate::nat_prelude::structures::{self, RecordNames};
use crate::nat_prelude::structures_setoid::{self as structures_s, StructuresSExtraNames};
use crate::rat_prelude::algebra_ext::AlgebraExtNames;
use crate::rat_prelude::algebra_instances::AlgebraNames;

use super::{Coeff, Decline};

/// `ring::rat`'s coefficient cap, ported unchanged (see the module docs on
/// why `Alg.CommRing` cannot build a generic numeral-unrolling bridge the
/// way `Alg.OrderedRing` did for `linarith::generic`).
const MAX_RING_COEFF: Coeff = 1;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Item {
    Mono(Vec<usize>, bool),
    Num(Coeff),
}

impl Item {
    fn key(&self) -> (bool, &[usize], bool) {
        match self {
            Item::Mono(v, neg) => (false, v.as_slice(), *neg),
            Item::Num(_) => (true, &[], false),
        }
    }

    fn negated(&self) -> Item {
        match self {
            Item::Mono(v, neg) => Item::Mono(v.clone(), !neg),
            Item::Num(k) => Item::Num(-k),
        }
    }
}

/// The operator/numeral constants a closure needs to rebuild a term without
/// capturing `Problem` — see the module docs' "closure-capture discipline".
#[derive(Clone, Copy)]
struct OpCtx {
    add: ExprId,
    mul: ExprId,
    neg: ExprId,
    zero: ExprId,
    one: ExprId,
}

fn item_term_ctx(k: &mut Kernel, ctx: OpCtx, atoms: &[ExprId], item: &Item) -> ExprId {
    match item {
        Item::Mono(vars, neg) => {
            let base = fold_mul_ctx(k, ctx, atoms, vars);
            if *neg { k.app(ctx.neg, base) } else { base }
        }
        Item::Num(0) => ctx.zero,
        Item::Num(1) => ctx.one,
        Item::Num(-1) => k.app(ctx.neg, ctx.one),
        Item::Num(_) => unreachable!("|coefficient| > 1 is never constructed in ring::generic"),
    }
}

fn add2_ctx(k: &mut Kernel, ctx: OpCtx, a: ExprId, b: ExprId) -> ExprId {
    let e = k.app(ctx.add, a);
    k.app(e, b)
}

fn mul2_ctx(k: &mut Kernel, ctx: OpCtx, a: ExprId, b: ExprId) -> ExprId {
    let e = k.app(ctx.mul, a);
    k.app(e, b)
}

fn fold_ctx(k: &mut Kernel, ctx: OpCtx, atoms: &[ExprId], items: &[Item]) -> ExprId {
    let mut acc = item_term_ctx(k, ctx, atoms, &items[0]);
    for item in &items[1..] {
        let t = item_term_ctx(k, ctx, atoms, item);
        acc = add2_ctx(k, ctx, acc, t);
    }
    acc
}

fn fold_from_ctx(
    k: &mut Kernel,
    ctx: OpCtx,
    atoms: &[ExprId],
    start: ExprId,
    items: &[Item],
) -> ExprId {
    let mut acc = start;
    for item in items {
        let t = item_term_ctx(k, ctx, atoms, item);
        acc = add2_ctx(k, ctx, acc, t);
    }
    acc
}

fn fold_mul_ctx(k: &mut Kernel, ctx: OpCtx, atoms: &[ExprId], vars: &[usize]) -> ExprId {
    let mut acc = atoms[vars[0]];
    for &v in &vars[1..] {
        acc = mul2_ctx(k, ctx, acc, atoms[v]);
    }
    acc
}

fn fold_mul_from_ctx(
    k: &mut Kernel,
    ctx: OpCtx,
    atoms: &[ExprId],
    start: ExprId,
    vars: &[usize],
) -> ExprId {
    let mut acc = start;
    for &v in vars {
        acc = mul2_ctx(k, ctx, acc, atoms[v]);
    }
    acc
}

/// ADR-1592-shaped: which "equality" flavor this `Problem` reasons about.
#[derive(Clone, Copy)]
enum Backend {
    KernelEq,
    Setoid {
        equiv: ExprId,
        equiv_refl: ExprId,
        equiv_symm: ExprId,
        equiv_trans: ExprId,
        add_congr: ExprId,
        mul_congr: ExprId,
        neg_congr: ExprId,
    },
}

/// Structural description of the ADD-shaped congruence context a
/// `congr_add` call rewrites under. `KernelEq` ignores this; `Setoid` uses
/// it to compose `addCongr` applications directly (no generic `Eq.rec`
/// transport for an arbitrary `equiv`, ADR-1588).
#[derive(Clone)]
enum AddCtx {
    /// `fun t => add t fixed`.
    Left(ExprId),
    /// `fun t => add fixed t`.
    Right(ExprId),
    /// `fun t => fold_from(t, tail)`.
    FoldFrom(Vec<Item>),
}

/// The MUL-shaped twin of [`AddCtx`].
#[derive(Clone)]
enum MulCtx {
    /// `fun t => mul t fixed`.
    Left(ExprId),
    /// `fun t => mul fixed t`.
    Right(ExprId),
    /// `fun t => fold_mul_from(t, tail)`.
    FoldFrom(Vec<usize>),
}

/// The parsing/emission context for one goal over one `(R : CommRing)` term.
pub(crate) struct Problem {
    #[allow(dead_code)]
    ring: ExprId,
    carrier: ExprId,
    zero: ExprId,
    one: ExprId,
    add: ExprId,
    mul: ExprId,
    neg: ExprId,
    add_assoc: ExprId,
    add_comm: ExprId,
    mul_assoc: ExprId,
    mul_comm: ExprId,
    mul_one_r: ExprId,
    distrib_l: ExprId,
    distrib_r: ExprId,
    /// `mul x zero = zero`, awaiting `x`.
    mul_zero: ExprId,
    /// `mul x (neg one) = neg x`, awaiting `x`.
    mul_neg_one: ExprId,
    /// `neg (neg x) = x`, awaiting `x`.
    neg_neg: ExprId,
    lg: LogicPrelude,
    l1: LevelId,
    eq_const: ExprId,
    ctx: OpCtx,
    atoms: Vec<ExprId>,
    next_scratch: u64,
    backend: Backend,
}

impl Problem {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new(
        k: &mut Kernel,
        lg: &LogicPrelude,
        l1: LevelId,
        st: &structures::StructuresNames,
        alg: &AlgebraNames,
        alg_ext: &AlgebraExtNames,
        ring: ExprId,
    ) -> Self {
        use structures::idx::comm_ring::{
            ADD, ADD_ASSOC, ADD_COMM, CARRIER, DISTRIB_L, DISTRIB_R, MUL, MUL_ASSOC, MUL_COMM,
            MUL_ONE_R, NEG, ONE, ZERO,
        };
        let rn: &RecordNames = &st.comm_ring;
        let carrier = sel(k, rn, CARRIER, ring);
        let zero = sel(k, rn, ZERO, ring);
        let one = sel(k, rn, ONE, ring);
        let add = sel(k, rn, ADD, ring);
        let mul = sel(k, rn, MUL, ring);
        let neg = sel(k, rn, NEG, ring);
        let add_assoc = sel(k, rn, ADD_ASSOC, ring);
        let add_comm = sel(k, rn, ADD_COMM, ring);
        let mul_assoc = sel(k, rn, MUL_ASSOC, ring);
        let mul_comm = sel(k, rn, MUL_COMM, ring);
        let mul_one_r = sel(k, rn, MUL_ONE_R, ring);
        let distrib_l = sel(k, rn, DISTRIB_L, ring);
        let distrib_r = sel(k, rn, DISTRIB_R, ring);

        let ring_ring_term = {
            let c = k.const_(alg_ext.comm_ring_to_ring, vec![]);
            k.app(c, ring)
        };
        let mul_zero = {
            let c = k.const_(alg.ring_mul_zero, vec![]);
            k.app(c, ring_ring_term)
        };
        let mul_neg_one = {
            let c = k.const_(alg_ext.mul_neg_one, vec![]);
            k.app(c, ring_ring_term)
        };
        let neg_neg = {
            let comm_group_term = {
                let c = k.const_(alg_ext.ring_to_comm_group, vec![]);
                k.app(c, ring_ring_term)
            };
            let group_term = {
                let c = k.const_(alg_ext.comm_group_to_group, vec![]);
                k.app(c, comm_group_term)
            };
            let c = k.const_(alg_ext.neg_neg, vec![]);
            k.app(c, group_term)
        };

        let eq_const = k.const_(lg.eq, vec![l1]);
        let ctx = OpCtx {
            add,
            mul,
            neg,
            zero,
            one,
        };

        Self {
            ring,
            carrier,
            zero,
            one,
            add,
            mul,
            neg,
            add_assoc,
            add_comm,
            mul_assoc,
            mul_comm,
            mul_one_r,
            distrib_l,
            distrib_r,
            mul_zero,
            mul_neg_one,
            neg_neg,
            lg: *lg,
            l1,
            eq_const,
            ctx,
            atoms: Vec::new(),
            next_scratch: 95_000,
            backend: Backend::KernelEq,
        }
    }

    /// The setoid twin of [`Self::new`] — over `(R : AlgS.CommRing)`.
    pub(crate) fn new_s(
        k: &mut Kernel,
        lg: &LogicPrelude,
        l1: LevelId,
        st: &structures_s::StructuresSRecordNames,
        extra: &StructuresSExtraNames,
        ring: ExprId,
    ) -> Self {
        use structures_s::idx::comm_ring::{
            ADD, ADD_ASSOC, ADD_COMM, ADD_CONGR, CARRIER, DISTRIB_L, DISTRIB_R, EQUIV, EQUIV_REFL,
            EQUIV_SYMM, EQUIV_TRANS, MUL, MUL_ASSOC, MUL_COMM, MUL_CONGR, MUL_ONE_R, NEG,
            NEG_CONGR, ONE, ZERO,
        };
        let rn: &RecordNames = &st.comm_ring;
        let carrier = sel(k, rn, CARRIER, ring);
        let equiv = sel(k, rn, EQUIV, ring);
        let equiv_refl = sel(k, rn, EQUIV_REFL, ring);
        let equiv_symm = sel(k, rn, EQUIV_SYMM, ring);
        let equiv_trans = sel(k, rn, EQUIV_TRANS, ring);
        let zero = sel(k, rn, ZERO, ring);
        let one = sel(k, rn, ONE, ring);
        let add = sel(k, rn, ADD, ring);
        let mul = sel(k, rn, MUL, ring);
        let neg = sel(k, rn, NEG, ring);
        let add_congr = sel(k, rn, ADD_CONGR, ring);
        let mul_congr = sel(k, rn, MUL_CONGR, ring);
        let neg_congr = sel(k, rn, NEG_CONGR, ring);
        let add_assoc = sel(k, rn, ADD_ASSOC, ring);
        let add_comm = sel(k, rn, ADD_COMM, ring);
        let mul_assoc = sel(k, rn, MUL_ASSOC, ring);
        let mul_comm = sel(k, rn, MUL_COMM, ring);
        let mul_one_r = sel(k, rn, MUL_ONE_R, ring);
        let distrib_l = sel(k, rn, DISTRIB_L, ring);
        let distrib_r = sel(k, rn, DISTRIB_R, ring);

        let ring_s_term = {
            let c = k.const_(extra.comm_ring_to_ring_s, vec![]);
            k.app(c, ring)
        };
        let mul_zero = {
            let c = k.const_(extra.mul_zero, vec![]);
            k.app(c, ring_s_term)
        };
        let mul_neg_one = {
            let c = k.const_(extra.mul_neg_one, vec![]);
            k.app(c, ring_s_term)
        };
        let neg_neg = {
            let c = k.const_(extra.neg_neg, vec![]);
            k.app(c, ring_s_term)
        };

        let eq_const = k.const_(lg.eq, vec![l1]);
        let ctx = OpCtx {
            add,
            mul,
            neg,
            zero,
            one,
        };

        Self {
            ring,
            carrier,
            zero,
            one,
            add,
            mul,
            neg,
            add_assoc,
            add_comm,
            mul_assoc,
            mul_comm,
            mul_one_r,
            distrib_l,
            distrib_r,
            mul_zero,
            mul_neg_one,
            neg_neg,
            lg: *lg,
            l1,
            eq_const,
            ctx,
            atoms: Vec::new(),
            next_scratch: 95_000,
            backend: Backend::Setoid {
                equiv,
                equiv_refl,
                equiv_symm,
                equiv_trans,
                add_congr,
                mul_congr,
                neg_congr,
            },
        }
    }

    fn fresh_scratch(&mut self) -> u64 {
        self.next_scratch += 1;
        self.next_scratch
    }

    fn atom_index(&mut self, e: ExprId) -> usize {
        if let Some(i) = self.atoms.iter().position(|&a| a == e) {
            return i;
        }
        self.atoms.push(e);
        self.atoms.len() - 1
    }

    // --- backend-aware combinators ------------------------------------

    fn refl(&self, k: &mut Kernel, a: ExprId) -> ExprId {
        match self.backend {
            Backend::KernelEq => structures::refl_of(k, &self.lg, self.l1, self.carrier, a),
            Backend::Setoid { equiv_refl, .. } => k.app(equiv_refl, a),
        }
    }

    fn symm(&self, k: &mut Kernel, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
        match self.backend {
            Backend::KernelEq => structures::symm_of(k, &self.lg, self.l1, self.carrier, a, b, h),
            Backend::Setoid { equiv_symm, .. } => Self::apply(k, equiv_symm, &[a, b, h]),
        }
    }

    fn trans(
        &mut self,
        k: &mut Kernel,
        a: ExprId,
        b: ExprId,
        c: ExprId,
        h1: ExprId,
        h2: ExprId,
    ) -> ExprId {
        match self.backend {
            Backend::KernelEq => {
                let s = self.fresh_scratch();
                structures::trans_of(k, &self.lg, self.l1, self.carrier, a, b, c, h1, h2, s)
            }
            Backend::Setoid { equiv_trans, .. } => Self::apply(k, equiv_trans, &[a, b, c, h1, h2]),
        }
    }

    /// Chain a sequence of `(target, proof-to-target)` steps starting from
    /// `source`, folding left with [`Self::trans`] — `ring::rat::rchain`'s
    /// shape, inlined.
    fn chain(
        &mut self,
        k: &mut Kernel,
        source: ExprId,
        steps: &[(ExprId, ExprId)],
    ) -> (ExprId, ExprId) {
        let mut cur = source;
        let mut proof = self.refl(k, source);
        for &(target, step) in steps {
            proof = self.trans(k, source, cur, target, proof, step);
            cur = target;
        }
        (cur, proof)
    }

    fn congr_add(
        &mut self,
        k: &mut Kernel,
        a: ExprId,
        b: ExprId,
        h: ExprId,
        shape: AddCtx,
        f: &dyn Fn(&mut Kernel, ExprId) -> ExprId,
    ) -> ExprId {
        match self.backend {
            Backend::KernelEq => {
                let s = self.fresh_scratch();
                structures::congr_arg(k, &self.lg, self.l1, self.carrier, a, b, h, s, f)
            }
            Backend::Setoid { add_congr, .. } => match shape {
                AddCtx::Left(fixed) => {
                    let refl_fixed = self.refl(k, fixed);
                    Self::apply(k, add_congr, &[a, b, fixed, fixed, h, refl_fixed])
                }
                AddCtx::Right(fixed) => {
                    let refl_fixed = self.refl(k, fixed);
                    Self::apply(k, add_congr, &[fixed, fixed, a, b, refl_fixed, h])
                }
                AddCtx::FoldFrom(tail) => {
                    let mut cur = h;
                    let mut cur_a = a;
                    let mut cur_b = b;
                    for item in &tail {
                        let t = self.item_term(k, item);
                        let refl_t = self.refl(k, t);
                        let next = Self::apply(k, add_congr, &[cur_a, cur_b, t, t, cur, refl_t]);
                        cur_a = self.add2(k, cur_a, t);
                        cur_b = self.add2(k, cur_b, t);
                        cur = next;
                    }
                    cur
                }
            },
        }
    }

    fn congr_mul(
        &mut self,
        k: &mut Kernel,
        a: ExprId,
        b: ExprId,
        h: ExprId,
        shape: MulCtx,
        f: &dyn Fn(&mut Kernel, ExprId) -> ExprId,
    ) -> ExprId {
        match self.backend {
            Backend::KernelEq => {
                let s = self.fresh_scratch();
                structures::congr_arg(k, &self.lg, self.l1, self.carrier, a, b, h, s, f)
            }
            Backend::Setoid { mul_congr, .. } => match shape {
                MulCtx::Left(fixed) => {
                    let refl_fixed = self.refl(k, fixed);
                    Self::apply(k, mul_congr, &[a, b, fixed, fixed, h, refl_fixed])
                }
                MulCtx::Right(fixed) => {
                    let refl_fixed = self.refl(k, fixed);
                    Self::apply(k, mul_congr, &[fixed, fixed, a, b, refl_fixed, h])
                }
                MulCtx::FoldFrom(tail) => {
                    let mut cur = h;
                    let mut cur_a = a;
                    let mut cur_b = b;
                    for &v in &tail {
                        let t = self.atoms[v];
                        let refl_t = self.refl(k, t);
                        let next = Self::apply(k, mul_congr, &[cur_a, cur_b, t, t, cur, refl_t]);
                        cur_a = self.mul2(k, cur_a, t);
                        cur_b = self.mul2(k, cur_b, t);
                        cur = next;
                    }
                    cur
                }
            },
        }
    }

    /// Rewrite under `neg` (unary, so no shape parameter is needed — unlike
    /// `congr_add`/`congr_mul`, `negCongr`'s single-argument shape is the
    /// only shape there is).
    fn congr_neg(&mut self, k: &mut Kernel, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
        let neg = self.neg;
        match self.backend {
            Backend::KernelEq => {
                let s = self.fresh_scratch();
                structures::congr_arg(k, &self.lg, self.l1, self.carrier, a, b, h, s, &|k2, x| {
                    k2.app(neg, x)
                })
            }
            Backend::Setoid { neg_congr, .. } => Self::apply(k, neg_congr, &[a, b, h]),
        }
    }

    fn apply(k: &mut Kernel, head: ExprId, args: &[ExprId]) -> ExprId {
        let mut e = head;
        for &a in args {
            e = k.app(e, a);
        }
        e
    }

    fn add2(&self, k: &mut Kernel, a: ExprId, b: ExprId) -> ExprId {
        add2_ctx(k, self.ctx, a, b)
    }

    fn mul2(&self, k: &mut Kernel, a: ExprId, b: ExprId) -> ExprId {
        mul2_ctx(k, self.ctx, a, b)
    }

    fn neg1(&self, k: &mut Kernel, a: ExprId) -> ExprId {
        k.app(self.neg, a)
    }

    fn build_numeral_signed(&self, k: &mut Kernel, n: Coeff) -> ExprId {
        item_term_ctx(k, self.ctx, &self.atoms, &Item::Num(n))
    }

    fn item_term(&self, k: &mut Kernel, item: &Item) -> ExprId {
        item_term_ctx(k, self.ctx, &self.atoms, item)
    }

    fn fold(&self, k: &mut Kernel, items: &[Item]) -> ExprId {
        fold_ctx(k, self.ctx, &self.atoms, items)
    }

    fn fold_from(&self, k: &mut Kernel, start: ExprId, items: &[Item]) -> ExprId {
        fold_from_ctx(k, self.ctx, &self.atoms, start, items)
    }

    fn fold_mul(&self, k: &mut Kernel, vars: &[usize]) -> ExprId {
        fold_mul_ctx(k, self.ctx, &self.atoms, vars)
    }

    fn fold_mul_from(&self, k: &mut Kernel, start: ExprId, vars: &[usize]) -> ExprId {
        fold_mul_from_ctx(k, self.ctx, &self.atoms, start, vars)
    }

    // --- derived primitives (see module docs) --------------------------

    /// `mul x (neg y) = neg (mul x y)`, derived from `mul_neg_one` +
    /// `mul_assoc` + `congr_mul` — no `Alg`/`AlgS` field for this directly.
    fn mul_neg_proof(&mut self, k: &mut Kernel, x: ExprId, y: ExprId) -> ExprId {
        let mul = self.mul;
        let neg_one = self.neg1(k, self.one);
        let neg_y = self.neg1(k, y);
        let mul_y_negone = self.mul2(k, y, neg_one);
        // h1 : mul y (neg one) = neg y ; symm : neg y = mul y (neg one)
        let h1 = Self::apply(k, self.mul_neg_one, &[y]);
        let h1_symm = self.symm(k, mul_y_negone, neg_y, h1);

        let mul_x_negy = self.mul2(k, x, neg_y);
        let mul_x_mulynegone = self.mul2(k, x, mul_y_negone);
        // step B : mul x (neg y) = mul x (mul y (neg one))
        let step_b = self.congr_mul(
            k,
            neg_y,
            mul_y_negone,
            h1_symm,
            MulCtx::Right(x),
            &|k2, t| {
                let e = k2.app(mul, x);
                k2.app(e, t)
            },
        );

        // step C : mul x (mul y (neg one)) = mul (mul x y) (neg one)
        let mul_x_y = self.mul2(k, x, y);
        let mul_xy_negone = self.mul2(k, mul_x_y, neg_one);
        let assoc = Self::apply(k, self.mul_assoc, &[x, y, neg_one]); // mul(mul x y) negone = mul x (mul y negone)
        let step_c = self.symm(k, mul_xy_negone, mul_x_mulynegone, assoc);

        // step D : mul (mul x y) (neg one) = neg (mul x y)
        let neg_mulxy = self.neg1(k, mul_x_y);
        let step_d = Self::apply(k, self.mul_neg_one, &[mul_x_y]);

        let (_, proof) = self.chain(
            k,
            mul_x_negy,
            &[
                (mul_x_mulynegone, step_b),
                (mul_xy_negone, step_c),
                (neg_mulxy, step_d),
            ],
        );
        proof
    }

    /// `mul (neg x) y = neg (mul x y)`, derived from `mul_comm` +
    /// [`Self::mul_neg_proof`] + `congr_neg`.
    fn neg_mul_proof(&mut self, k: &mut Kernel, x: ExprId, y: ExprId) -> ExprId {
        let neg_x = self.neg1(k, x);
        let mul_negx_y = self.mul2(k, neg_x, y);
        let mul_y_negx = self.mul2(k, y, neg_x);
        // step A : mul (neg x) y = mul y (neg x)
        let step_a = Self::apply(k, self.mul_comm, &[neg_x, y]);

        // step B : mul y (neg x) = neg (mul y x)
        let mul_y_x = self.mul2(k, y, x);
        let neg_mulyx = self.neg1(k, mul_y_x);
        let step_b = self.mul_neg_proof(k, y, x);

        // step C : neg (mul y x) = neg (mul x y)
        let mul_x_y = self.mul2(k, x, y);
        let neg_mulxy = self.neg1(k, mul_x_y);
        let comm = Self::apply(k, self.mul_comm, &[y, x]); // mul y x = mul x y
        let step_c = self.congr_neg(k, mul_y_x, mul_x_y, comm);

        let (_, proof) = self.chain(
            k,
            mul_negx_y,
            &[
                (mul_y_negx, step_a),
                (neg_mulyx, step_b),
                (neg_mulxy, step_c),
            ],
        );
        proof
    }

    // --- outer-sum re-association / sorting -----------------------------

    fn reassoc(&mut self, k: &mut Kernel, left: &[Item], right: &[Item]) -> ExprId {
        let add = self.add;
        let fl = self.fold(k, left);
        if right.len() == 1 {
            let joined = self.fold_from(k, fl, right);
            return self.refl(k, joined);
        }
        let (init, last) = right.split_at(right.len() - 1);
        let fi = self.fold(k, init);
        let last_t = self.item_term(k, &last[0]);
        let fr = self.add2(k, fi, last_t);

        let source = self.add2(k, fl, fr);
        let regrouped_inner = self.add2(k, fl, fi);
        let regrouped = self.add2(k, regrouped_inner, last_t);
        let assoc = Self::apply(k, self.add_assoc, &[fl, fi, last_t]);
        let step1 = self.symm(k, regrouped, source, assoc);

        let inner = self.reassoc(k, left, init);
        let mut joined_items = left.to_vec();
        joined_items.extend_from_slice(init);
        let joined_inner = self.fold(k, &joined_items);
        let step2 = self.congr_add(
            k,
            regrouped_inner,
            joined_inner,
            inner,
            AddCtx::Left(last_t),
            &|k2, x| {
                let e = k2.app(add, x);
                k2.app(e, last_t)
            },
        );
        let target = self.add2(k, joined_inner, last_t);
        self.trans(k, source, regrouped, target, step1, step2)
    }

    fn reassoc_mul(&mut self, k: &mut Kernel, left: &[usize], right: &[usize]) -> ExprId {
        let mul = self.mul;
        let fl = self.fold_mul(k, left);
        if right.len() == 1 {
            let joined = self.mul2(k, fl, self.atoms[right[0]]);
            return self.refl(k, joined);
        }
        let (init, last) = right.split_at(right.len() - 1);
        let fi = self.fold_mul(k, init);
        let last_t = self.atoms[last[0]];
        let fr = self.mul2(k, fi, last_t);

        let source = self.mul2(k, fl, fr);
        let regrouped_inner = self.mul2(k, fl, fi);
        let regrouped = self.mul2(k, regrouped_inner, last_t);
        let assoc = Self::apply(k, self.mul_assoc, &[fl, fi, last_t]);
        let step1 = self.symm(k, regrouped, source, assoc);

        let inner = self.reassoc_mul(k, left, init);
        let mut joined_vars = left.to_vec();
        joined_vars.extend_from_slice(init);
        let joined_inner = self.fold_mul(k, &joined_vars);
        let step2 = self.congr_mul(
            k,
            regrouped_inner,
            joined_inner,
            inner,
            MulCtx::Left(last_t),
            &|k2, x| {
                let e = k2.app(mul, x);
                k2.app(e, last_t)
            },
        );
        let target = self.mul2(k, joined_inner, last_t);
        self.trans(k, source, regrouped, target, step1, step2)
    }

    /// Sort a monomial's factor list into canonical (index) order —
    /// `ring::rat::Problem::sort_factors` ported.
    fn sort_factors(&mut self, k: &mut Kernel, vars: &[usize]) -> (Vec<usize>, ExprId) {
        let mul = self.mul;
        let source = self.fold_mul(k, vars);
        let mut current: Vec<usize> = vars.to_vec();
        let mut proof = self.refl(k, source);
        let mut folded = source;
        loop {
            let mut swapped = false;
            for idx in 0..current.len().saturating_sub(1) {
                if current[idx] <= current[idx + 1] {
                    continue;
                }
                let x = self.atoms[current[idx]];
                let y = self.atoms[current[idx + 1]];
                let (inner_before, inner_after, base) = if idx == 0 {
                    let before = self.mul2(k, x, y);
                    let after = self.mul2(k, y, x);
                    let lemma = Self::apply(k, self.mul_comm, &[x, y]);
                    (before, after, lemma)
                } else {
                    let prefix = self.fold_mul(k, &current[..idx]);
                    let before_inner = self.mul2(k, prefix, x);
                    let before = self.mul2(k, before_inner, y);
                    let xy = self.mul2(k, x, y);
                    let assoc1 = Self::apply(k, self.mul_assoc, &[prefix, x, y]);
                    let mid1 = self.mul2(k, prefix, xy);
                    let comm = Self::apply(k, self.mul_comm, &[x, y]);
                    let yx = self.mul2(k, y, x);
                    let step2 = self.congr_mul(k, xy, yx, comm, MulCtx::Right(prefix), &|k2, t| {
                        let e = k2.app(mul, prefix);
                        k2.app(e, t)
                    });
                    let mid2 = self.mul2(k, prefix, yx);
                    let after_inner = self.mul2(k, prefix, y);
                    let after = self.mul2(k, after_inner, x);
                    let assoc2 = Self::apply(k, self.mul_assoc, &[prefix, y, x]);
                    let step3 = self.symm(k, after, mid2, assoc2);
                    let (_, base) =
                        self.chain(k, before, &[(mid1, assoc1), (mid2, step2), (after, step3)]);
                    (before, after, base)
                };
                let tail: Vec<usize> = current[idx + 2..].to_vec();
                let ctx = self.ctx;
                let atoms = self.atoms.clone();
                let tail_for_closure = tail.clone();
                let step = self.congr_mul(
                    k,
                    inner_before,
                    inner_after,
                    base,
                    MulCtx::FoldFrom(tail),
                    &move |k2, t| fold_mul_from_ctx(k2, ctx, &atoms, t, &tail_for_closure),
                );
                current.swap(idx, idx + 1);
                let next = self.fold_mul(k, &current);
                proof = self.trans(k, source, folded, next, proof, step);
                folded = next;
                swapped = true;
            }
            if !swapped {
                break;
            }
        }
        (current, proof)
    }

    fn sort_items(&mut self, k: &mut Kernel, items: &[Item]) -> (Vec<Item>, ExprId) {
        let add = self.add;
        let source = self.fold(k, items);
        let mut current: Vec<Item> = items.to_vec();
        let mut proof = self.refl(k, source);
        let mut folded = source;
        loop {
            let mut swapped = false;
            for idx in 0..current.len().saturating_sub(1) {
                if current[idx].key() <= current[idx + 1].key() {
                    continue;
                }
                let x = self.item_term(k, &current[idx]);
                let y = self.item_term(k, &current[idx + 1]);
                let (inner_before, inner_after, base) = if idx == 0 {
                    let before = self.add2(k, x, y);
                    let after = self.add2(k, y, x);
                    let lemma = Self::apply(k, self.add_comm, &[x, y]);
                    (before, after, lemma)
                } else {
                    let prefix = self.fold(k, &current[..idx]);
                    let before_inner = self.add2(k, prefix, x);
                    let before = self.add2(k, before_inner, y);
                    let xy = self.add2(k, x, y);
                    let assoc1 = Self::apply(k, self.add_assoc, &[prefix, x, y]);
                    let mid1 = self.add2(k, prefix, xy);
                    let comm = Self::apply(k, self.add_comm, &[x, y]);
                    let yx = self.add2(k, y, x);
                    let step2 = self.congr_add(k, xy, yx, comm, AddCtx::Right(prefix), &|k2, t| {
                        let e = k2.app(add, prefix);
                        k2.app(e, t)
                    });
                    let mid2 = self.add2(k, prefix, yx);
                    let after_inner = self.add2(k, prefix, y);
                    let after = self.add2(k, after_inner, x);
                    let assoc2 = Self::apply(k, self.add_assoc, &[prefix, y, x]);
                    let step3 = self.symm(k, after, mid2, assoc2);
                    let (_, base) =
                        self.chain(k, before, &[(mid1, assoc1), (mid2, step2), (after, step3)]);
                    (before, after, base)
                };
                let tail: Vec<Item> = current[idx + 2..].to_vec();
                let ctx = self.ctx;
                let atoms = self.atoms.clone();
                let tail_for_closure = tail.clone();
                let step = self.congr_add(
                    k,
                    inner_before,
                    inner_after,
                    base,
                    AddCtx::FoldFrom(tail),
                    &move |k2, t| fold_from_ctx(k2, ctx, &atoms, t, &tail_for_closure),
                );
                current.swap(idx, idx + 1);
                let next = self.fold(k, &current);
                proof = self.trans(k, source, folded, next, proof, step);
                folded = next;
                swapped = true;
            }
            if !swapped {
                break;
            }
        }
        (current, proof)
    }

    // --- the multiplicative "unroll" (magnitude capped at 1) ------------

    fn scale_item(
        &mut self,
        k: &mut Kernel,
        item: &Item,
        count: Coeff,
        commuted: bool,
    ) -> Result<(Vec<Item>, ExprId), Decline> {
        if count.unsigned_abs() > MAX_RING_COEFF.unsigned_abs() {
            return Err(Decline::CoefficientTooLarge);
        }
        let it = self.item_term(k, item);

        let (items, uncommuted_lhs, base_proof) = if count == 0 {
            let proof = Self::apply(k, self.mul_zero, &[it]);
            (vec![Item::Num(0)], self.mul2(k, it, self.zero), proof)
        } else if count == 1 {
            let proof = Self::apply(k, self.mul_one_r, &[it]);
            (vec![item.clone()], self.mul2(k, it, self.one), proof)
        } else {
            // count == -1 : `mul it (neg one) = neg it`, one step.
            let proof = Self::apply(k, self.mul_neg_one, &[it]);
            let neg_one = self.neg1(k, self.one);
            (vec![item.negated()], self.mul2(k, it, neg_one), proof)
        };

        if commuted {
            let numeral = self.build_numeral_signed(k, count);
            let commuted_lhs = self.mul2(k, numeral, it);
            let comm = Self::apply(k, self.mul_comm, &[numeral, it]);
            let target = self.fold(k, &items);
            let (_, full) = self.chain(
                k,
                commuted_lhs,
                &[(uncommuted_lhs, comm), (target, base_proof)],
            );
            Ok((items, full))
        } else {
            Ok((items, base_proof))
        }
    }

    /// `Eq (mul (item_term a) (item_term b)) (fold result)` — the
    /// `ring::rat::Problem::combine_items` twin.
    fn combine_items(
        &mut self,
        k: &mut Kernel,
        a: &Item,
        b: &Item,
    ) -> Result<(Vec<Item>, ExprId), Decline> {
        match (a, b) {
            (Item::Num(x), Item::Num(y)) => {
                if x.unsigned_abs() > MAX_RING_COEFF.unsigned_abs()
                    || y.unsigned_abs() > MAX_RING_COEFF.unsigned_abs()
                {
                    return Err(Decline::CoefficientTooLarge);
                }
                self.scale_item(k, &Item::Num(*x), *y, false)
            }
            (Item::Num(c), Item::Mono(_, _)) => self.scale_item(k, b, *c, true),
            (Item::Mono(_, _), Item::Num(c)) => self.scale_item(k, a, *c, false),
            (Item::Mono(va, sign_a), Item::Mono(vb, sign_b)) => {
                let raw_a = self.fold_mul(k, va);
                let raw_b = self.fold_mul(k, vb);
                let mut merged = va.clone();
                merged.extend_from_slice(vb);
                let reassoc = self.reassoc_mul(k, va, vb);
                let merged_term = self.fold_mul(k, &merged);
                let (sorted, sort_proof) = self.sort_factors(k, &merged);
                let sorted_term = self.fold_mul(k, &sorted);
                let raw_prod = self.mul2(k, raw_a, raw_b);
                let raw_proof =
                    self.trans(k, raw_prod, merged_term, sorted_term, reassoc, sort_proof);

                let (result_sign, proof) = self.combine_mono_signs(
                    k,
                    *sign_a,
                    *sign_b,
                    raw_a,
                    raw_b,
                    raw_prod,
                    raw_proof,
                    sorted_term,
                );
                Ok((vec![Item::Mono(sorted, result_sign)], proof))
            }
        }
    }

    /// The `ring::rat::apply_mono_signs` twin, using the LOCALLY DERIVED
    /// `mul_neg_proof`/`neg_mul_proof`/`self.neg_neg` instead of `RatPrelude`
    /// fields — see the module docs.
    #[allow(clippy::too_many_arguments)]
    fn combine_mono_signs(
        &mut self,
        k: &mut Kernel,
        sign_a: bool,
        sign_b: bool,
        raw_a: ExprId,
        raw_b: ExprId,
        raw_prod: ExprId,
        raw_proof: ExprId,
        sorted_term: ExprId,
    ) -> (bool, ExprId) {
        match (sign_a, sign_b) {
            (false, false) => (false, raw_proof),
            (true, false) => {
                let neg_a = self.neg1(k, raw_a);
                let source = self.mul2(k, neg_a, raw_b);
                let nm = self.neg_mul_proof(k, raw_a, raw_b);
                let neg_raw_prod = self.neg1(k, raw_prod);
                let congr_r = self.congr_neg(k, raw_prod, sorted_term, raw_proof);
                let target = self.neg1(k, sorted_term);
                let (_, full) = self.chain(k, source, &[(neg_raw_prod, nm), (target, congr_r)]);
                (true, full)
            }
            (false, true) => {
                let neg_b = self.neg1(k, raw_b);
                let source = self.mul2(k, raw_a, neg_b);
                let mn = self.mul_neg_proof(k, raw_a, raw_b);
                let neg_raw_prod = self.neg1(k, raw_prod);
                let congr_r = self.congr_neg(k, raw_prod, sorted_term, raw_proof);
                let target = self.neg1(k, sorted_term);
                let (_, full) = self.chain(k, source, &[(neg_raw_prod, mn), (target, congr_r)]);
                (true, full)
            }
            (true, true) => {
                // (-a)*(-b) = -(a*(-b)) = -(-(a*b)) = a*b
                let neg_a = self.neg1(k, raw_a);
                let neg_b = self.neg1(k, raw_b);
                let source = self.mul2(k, neg_a, neg_b);
                let mul_a_negb = self.mul2(k, raw_a, neg_b);
                let neg_mul_a_negb = self.neg1(k, mul_a_negb);
                let nm = self.neg_mul_proof(k, raw_a, neg_b);
                let neg_raw_prod = self.neg1(k, raw_prod);
                let mn = self.mul_neg_proof(k, raw_a, raw_b);
                let congr2 = self.congr_neg(k, mul_a_negb, neg_raw_prod, mn);
                let neg_neg_raw_prod = self.neg1(k, neg_raw_prod);
                let nn = Self::apply(k, self.neg_neg, &[raw_prod]);
                let (_, chained) = self.chain(
                    k,
                    source,
                    &[
                        (neg_mul_a_negb, nm),
                        (neg_neg_raw_prod, congr2),
                        (raw_prod, nn),
                    ],
                );
                let full = self.trans(k, source, raw_prod, sorted_term, chained, raw_proof);
                (false, full)
            }
        }
    }

    fn distribute_single(
        &mut self,
        k: &mut Kernel,
        item: &Item,
        iv: &[Item],
    ) -> Result<(Vec<Item>, ExprId), Decline> {
        let add = self.add;
        if iv.len() == 1 {
            return self.combine_items(k, item, &iv[0]);
        }
        let (init, last) = iv.split_at(iv.len() - 1);
        let fi = self.fold(k, init);
        let last_t = self.item_term(k, &last[0]);
        let fv = self.add2(k, fi, last_t);
        let it = self.item_term(k, item);
        let source = self.mul2(k, it, fv);

        let mul_it_fi = self.mul2(k, it, fi);
        let mul_it_last = self.mul2(k, it, last_t);
        let sum = self.add2(k, mul_it_fi, mul_it_last);
        let ld = Self::apply(k, self.distrib_l, &[it, fi, last_t]);

        let (items_init, proof_init) = self.distribute_single(k, item, init)?;
        let (items_last, proof_last) = self.combine_items(k, item, &last[0])?;
        let target_init = self.fold(k, &items_init);
        let target_last = self.fold(k, &items_last);
        let step_a = self.congr_add(
            k,
            mul_it_fi,
            target_init,
            proof_init,
            AddCtx::Left(mul_it_last),
            &|k2, t| {
                let e = k2.app(add, t);
                k2.app(e, mul_it_last)
            },
        );
        let mid2 = self.add2(k, target_init, mul_it_last);
        let step_b = self.congr_add(
            k,
            mul_it_last,
            target_last,
            proof_last,
            AddCtx::Right(target_init),
            &|k2, t| {
                let e = k2.app(add, target_init);
                k2.app(e, t)
            },
        );
        let mid3 = self.add2(k, target_init, target_last);
        let step_ab = self.trans(k, sum, mid2, mid3, step_a, step_b);

        let mut items = items_init.clone();
        items.extend_from_slice(&items_last);
        let combined = self.fold(k, &items);
        let reassoc = self.reassoc(k, &items_init, &items_last);
        let joined_proof = self.trans(k, sum, mid3, combined, step_ab, reassoc);
        let full = self.trans(k, source, sum, combined, ld, joined_proof);
        Ok((items, full))
    }

    fn distribute(
        &mut self,
        k: &mut Kernel,
        iu: &[Item],
        iv: &[Item],
    ) -> Result<(Vec<Item>, ExprId), Decline> {
        let add = self.add;
        if iu.len() == 1 {
            return self.distribute_single(k, &iu[0], iv);
        }
        let (init, last) = iu.split_at(iu.len() - 1);
        let fi = self.fold(k, init);
        let last_t = self.item_term(k, &last[0]);
        let fu = self.add2(k, fi, last_t);
        let fv = self.fold(k, iv);
        let source = self.mul2(k, fu, fv);

        let mul_fi_fv = self.mul2(k, fi, fv);
        let mul_last_fv = self.mul2(k, last_t, fv);
        let sum = self.add2(k, mul_fi_fv, mul_last_fv);
        let rd = Self::apply(k, self.distrib_r, &[fi, last_t, fv]);

        let (items_init, proof_init) = self.distribute(k, init, iv)?;
        let (items_last, proof_last) = self.distribute_single(k, &last[0], iv)?;
        let target_init = self.fold(k, &items_init);
        let target_last = self.fold(k, &items_last);
        let step_a = self.congr_add(
            k,
            mul_fi_fv,
            target_init,
            proof_init,
            AddCtx::Left(mul_last_fv),
            &|k2, t| {
                let e = k2.app(add, t);
                k2.app(e, mul_last_fv)
            },
        );
        let mid2 = self.add2(k, target_init, mul_last_fv);
        let step_b = self.congr_add(
            k,
            mul_last_fv,
            target_last,
            proof_last,
            AddCtx::Right(target_init),
            &|k2, t| {
                let e = k2.app(add, target_init);
                k2.app(e, t)
            },
        );
        let mid3 = self.add2(k, target_init, target_last);
        let step_ab = self.trans(k, sum, mid2, mid3, step_a, step_b);

        let mut items = items_init.clone();
        items.extend_from_slice(&items_last);
        let combined = self.fold(k, &items);
        let reassoc = self.reassoc(k, &items_init, &items_last);
        let joined_proof = self.trans(k, sum, mid3, combined, step_ab, reassoc);
        let full = self.trans(k, source, sum, combined, rd, joined_proof);
        Ok((items, full))
    }

    // --- parsing ----------------------------------------------------------

    fn as_binop(k: &mut Kernel, op: ExprId, e: ExprId) -> Option<(ExprId, ExprId)> {
        let ExprNode::App(f, y) = k.expr_node(e).clone() else {
            return None;
        };
        let ExprNode::App(g, x) = k.expr_node(f).clone() else {
            return None;
        };
        if g == op { Some((x, y)) } else { None }
    }

    fn as_unop(k: &mut Kernel, op: ExprId, e: ExprId) -> Option<ExprId> {
        let ExprNode::App(f, x) = k.expr_node(e).clone() else {
            return None;
        };
        if f == op { Some(x) } else { None }
    }

    fn as_eq(&self, k: &mut Kernel, e: ExprId) -> Option<(ExprId, ExprId)> {
        match self.backend {
            Backend::KernelEq => {
                let ExprNode::App(f3, y) = k.expr_node(e).clone() else {
                    return None;
                };
                let ExprNode::App(f2, x) = k.expr_node(f3).clone() else {
                    return None;
                };
                let ExprNode::App(f1, ty) = k.expr_node(f2).clone() else {
                    return None;
                };
                if f1 == self.eq_const && ty == self.carrier {
                    Some((x, y))
                } else {
                    None
                }
            }
            Backend::Setoid { equiv, .. } => Self::as_binop(k, equiv, e),
        }
    }

    fn as_numeral(&self, e: ExprId, k: &mut Kernel) -> Option<Coeff> {
        if e == self.zero {
            return Some(0);
        }
        if e == self.one {
            return Some(1);
        }
        if let Some(inner) = Self::as_unop(k, self.neg, e) {
            return self.as_numeral(inner, k).map(|c| -c);
        }
        None
    }

    // --- flatten: source term -> raw item list -----------------------------

    fn flatten(&mut self, k: &mut Kernel, e: ExprId) -> Result<(Vec<Item>, ExprId), Decline> {
        if let Some(n) = self.as_numeral(e, k) {
            let items = vec![Item::Num(n)];
            let folded = self.fold(k, &items);
            let proof = self.refl(k, folded);
            return Ok((items, proof));
        }
        if let Some((u, v)) = Self::as_binop(k, self.add, e) {
            return self.flatten_add(k, u, v);
        }
        if let Some((u, v)) = Self::as_binop(k, self.mul, e) {
            return self.flatten_mul(k, u, v);
        }
        if let Some(u) = Self::as_unop(k, self.neg, e) {
            return self.flatten_neg(k, u);
        }
        let index = self.atom_index(e);
        let items = vec![Item::Mono(vec![index], false)];
        let proof = self.refl(k, e);
        Ok((items, proof))
    }

    fn flatten_add(
        &mut self,
        k: &mut Kernel,
        u: ExprId,
        v: ExprId,
    ) -> Result<(Vec<Item>, ExprId), Decline> {
        let add = self.add;
        let (iu, pu) = self.flatten(k, u)?;
        let (iv, pv) = self.flatten(k, v)?;
        let fu = self.fold(k, &iu);
        let fv = self.fold(k, &iv);
        let source = self.add2(k, u, v);
        let mid = self.add2(k, fu, v);
        let joined = self.add2(k, fu, fv);

        let step1 = self.congr_add(k, u, fu, pu, AddCtx::Left(v), &|k2, t| {
            let e = k2.app(add, t);
            k2.app(e, v)
        });
        let step2 = self.congr_add(k, v, fv, pv, AddCtx::Right(fu), &|k2, t| {
            let e = k2.app(add, fu);
            k2.app(e, t)
        });
        let p12 = self.trans(k, source, mid, joined, step1, step2);

        let mut items = iu.clone();
        items.extend_from_slice(&iv);
        let target = self.fold(k, &items);
        let step3 = self.reassoc(k, &iu, &iv);
        let proof = self.trans(k, source, joined, target, p12, step3);
        Ok((items, proof))
    }

    /// `neg` distributes over `mul` and cancels a double negation; it does
    /// NOT distribute over `add` (module docs) — a `neg (add u v)` source
    /// term falls to the atom fallback below.
    fn flatten_neg(&mut self, k: &mut Kernel, e: ExprId) -> Result<(Vec<Item>, ExprId), Decline> {
        let neg_e = self.neg1(k, e);
        if let Some(y) = Self::as_unop(k, self.neg, e) {
            let (items, proof_y) = self.flatten(k, y)?;
            let nn = Self::apply(k, self.neg_neg, &[y]);
            let folded = self.fold(k, &items);
            let full = self.trans(k, neg_e, y, folded, nn, proof_y);
            return Ok((items, full));
        }
        if let Some((u, v)) = Self::as_binop(k, self.mul, e) {
            let neg_v = self.neg1(k, v);
            let u_negv = self.mul2(k, u, neg_v);
            let mn = self.mul_neg_proof(k, u, v); // mul u (neg v) = neg (mul u v) = neg_e
            let rev = self.symm(k, u_negv, neg_e, mn);
            let (items, proof_mul) = self.flatten_mul(k, u, neg_v)?;
            let folded = self.fold(k, &items);
            let full = self.trans(k, neg_e, u_negv, folded, rev, proof_mul);
            return Ok((items, full));
        }
        let idx = self.atom_index(e);
        let items = vec![Item::Mono(vec![idx], true)];
        let proof = self.refl(k, neg_e);
        Ok((items, proof))
    }

    fn flatten_mul(
        &mut self,
        k: &mut Kernel,
        u: ExprId,
        v: ExprId,
    ) -> Result<(Vec<Item>, ExprId), Decline> {
        let mul = self.mul;
        let (iu, pu) = self.flatten(k, u)?;
        let (iv, pv) = self.flatten(k, v)?;
        let fu = self.fold(k, &iu);
        let fv = self.fold(k, &iv);
        let source = self.mul2(k, u, v);
        let mid = self.mul2(k, fu, v);
        let joined = self.mul2(k, fu, fv);

        let step1 = self.congr_mul(k, u, fu, pu, MulCtx::Left(v), &|k2, t| {
            let e = k2.app(mul, t);
            k2.app(e, v)
        });
        let step2 = self.congr_mul(k, v, fv, pv, MulCtx::Right(fu), &|k2, t| {
            let e = k2.app(mul, fu);
            k2.app(e, t)
        });
        let p12 = self.trans(k, source, mid, joined, step1, step2);

        let (dist_items, dist_proof) = self.distribute(k, &iu, &iv)?;
        let target = self.fold(k, &dist_items);
        let proof = self.trans(k, source, joined, target, p12, dist_proof);
        Ok((dist_items, proof))
    }

    fn normalize(&mut self, k: &mut Kernel, e: ExprId) -> Result<(Vec<Item>, ExprId), Decline> {
        let (items, p1) = self.flatten(k, e)?;
        let flat = self.fold(k, &items);
        let (sorted, p2) = self.sort_items(k, &items);
        let sorted_term = self.fold(k, &sorted);
        let proof = self.trans(k, e, flat, sorted_term, p1, p2);
        Ok((sorted, proof))
    }

    fn prove_eq(
        &mut self,
        k: &mut Kernel,
        x: ExprId,
        y: ExprId,
        verify: bool,
    ) -> Result<ExprId, Decline> {
        let (ix, px) = self.normalize(k, x)?;
        let (iy, py) = self.normalize(k, y)?;
        if verify && ix != iy {
            return Err(Decline::NotAnIdentity);
        }
        let canon_x = self.fold(k, &ix);
        let canon_y = self.fold(k, &iy);
        let back = self.symm(k, y, canon_y, py);
        Ok(self.trans(k, x, canon_x, y, px, back))
    }
}

/// Prove `Eq lhs rhs` (kernel `Eq` at `R.carrier`) over `(R : Alg.CommRing)`
/// from ring axioms alone, or decline.
///
/// # Errors
///
/// [`Decline`] whenever a side leaves the fragment or the two sides are not
/// (within this normalizer's completeness) the same ring expression.
#[allow(clippy::too_many_arguments)]
pub(crate) fn prove_eq(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    st: &structures::StructuresNames,
    alg: &AlgebraNames,
    alg_ext: &AlgebraExtNames,
    ring: ExprId,
    lhs: ExprId,
    rhs: ExprId,
) -> Result<ExprId, Decline> {
    let mut problem = Problem::new(k, lg, l1, st, alg, alg_ext, ring);
    problem.prove_eq(k, lhs, rhs, true)
}

/// [`prove_eq`] with the procedure's own normal-form check switched off —
/// exposed only for the corrupted-certificate tests.
///
/// # Errors
///
/// As [`prove_eq`], minus [`Decline::NotAnIdentity`].
#[allow(clippy::too_many_arguments)]
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn prove_eq_unverified(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    st: &structures::StructuresNames,
    alg: &AlgebraNames,
    alg_ext: &AlgebraExtNames,
    ring: ExprId,
    lhs: ExprId,
    rhs: ExprId,
) -> Result<ExprId, Decline> {
    let mut problem = Problem::new(k, lg, l1, st, alg, alg_ext, ring);
    problem.prove_eq(k, lhs, rhs, false)
}

/// The setoid twin of [`prove_eq`] — over `(R : AlgS.CommRing)`, proving
/// `R.equiv lhs rhs`.
///
/// # Errors
///
/// As [`prove_eq`].
#[allow(clippy::too_many_arguments)]
pub(crate) fn prove_eq_s(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    st: &structures_s::StructuresSRecordNames,
    extra: &StructuresSExtraNames,
    ring: ExprId,
    lhs: ExprId,
    rhs: ExprId,
) -> Result<ExprId, Decline> {
    let mut problem = Problem::new_s(k, lg, l1, st, extra, ring);
    problem.prove_eq(k, lhs, rhs, true)
}

/// The setoid twin of [`prove_eq_unverified`].
///
/// # Errors
///
/// As [`prove_eq_s`], minus [`Decline::NotAnIdentity`].
#[allow(clippy::too_many_arguments)]
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn prove_eq_s_unverified(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    st: &structures_s::StructuresSRecordNames,
    extra: &StructuresSExtraNames,
    ring: ExprId,
    lhs: ExprId,
    rhs: ExprId,
) -> Result<ExprId, Decline> {
    let mut problem = Problem::new_s(k, lg, l1, st, extra, ring);
    problem.prove_eq(k, lhs, rhs, false)
}

#[cfg(test)]
mod generic_tests {
    use super::*;
    use crate::nat_prelude::structures::lam_over;
    use crate::nat_prelude::structures::sel;
    use crate::{Kernel, build_rat_prelude};

    fn eq_of_carrier(
        k: &mut Kernel,
        carrier: ExprId,
        l1: LevelId,
        lg: &LogicPrelude,
        x: ExprId,
        y: ExprId,
    ) -> ExprId {
        structures::eq_of(k, lg, l1, carrier, x, y)
    }

    fn close_and_infer(k: &mut Kernel, carrier: ExprId, vars: &[u64], body: ExprId) -> ExprId {
        let mut v = body;
        for &fv in vars.iter().rev() {
            v = lam_over(k, fv, carrier, v);
        }
        k.infer(v)
            .expect("closed generic ring proof must type-check")
    }

    fn mul_of(k: &mut Kernel, rn: &RecordNames, ring: ExprId, x: ExprId, y: ExprId) -> ExprId {
        use structures::idx::comm_ring::MUL;
        let mul = sel(k, rn, MUL, ring);
        let e = k.app(mul, x);
        k.app(e, y)
    }

    fn add_of(k: &mut Kernel, rn: &RecordNames, ring: ExprId, x: ExprId, y: ExprId) -> ExprId {
        use structures::idx::comm_ring::ADD;
        let add = sel(k, rn, ADD, ring);
        let e = k.app(add, x);
        k.app(e, y)
    }

    fn neg_of(k: &mut Kernel, rn: &RecordNames, ring: ExprId, x: ExprId) -> ExprId {
        use structures::idx::comm_ring::NEG;
        let neg = sel(k, rn, NEG, ring);
        k.app(neg, x)
    }

    // `AlgS.CommRing`'s field indices are NOT the same numbers as `Alg.
    // CommRing`'s (four extra equiv-infrastructure fields shift every later
    // index) -- these three helpers read `structures_s::idx::comm_ring`,
    // never `structures::idx::comm_ring`, and are the ones every `CReal.
    // commRingS` test below must use.
    fn mul_of_s(k: &mut Kernel, rn: &RecordNames, ring: ExprId, x: ExprId, y: ExprId) -> ExprId {
        use structures_s::idx::comm_ring::MUL;
        let mul = sel(k, rn, MUL, ring);
        let e = k.app(mul, x);
        k.app(e, y)
    }

    fn add_of_s(k: &mut Kernel, rn: &RecordNames, ring: ExprId, x: ExprId, y: ExprId) -> ExprId {
        use structures_s::idx::comm_ring::ADD;
        let add = sel(k, rn, ADD, ring);
        let e = k.app(add, x);
        k.app(e, y)
    }

    fn neg_of_s(k: &mut Kernel, rn: &RecordNames, ring: ExprId, x: ExprId) -> ExprId {
        use structures_s::idx::comm_ring::NEG;
        let neg = sel(k, rn, NEG, ring);
        k.app(neg, x)
    }

    // -----------------------------------------------------------------------
    // `Alg.CommRing` (Eq-flavored), at `Int.commRing`/`Rat.commRing`.
    // -----------------------------------------------------------------------

    #[test]
    fn int_mul_comm_via_generic_matches_normal_form() {
        const A: u64 = 61_000;
        const B: u64 = 61_001;
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.algebra.int_comm_ring, vec![]);
        let carrier = k.const_(p.int.z, vec![]);
        let rn = p.int.nat.structures.comm_ring;
        let (a, b) = (k.fvar(A), k.fvar(B));
        let lhs = mul_of(&mut k, &rn, ring, a, b);
        let rhs = mul_of(&mut k, &rn, ring, b, a);

        let proof = prove_eq(
            &mut k,
            &p.int.nat.logic,
            l1,
            &p.int.nat.structures,
            &p.algebra,
            &p.algebra_ext,
            ring,
            lhs,
            rhs,
        )
        .expect("ring::generic must prove a*b=b*a over Alg.CommRing");
        let ty = close_and_infer(&mut k, carrier, &[A, B], proof);
        let goal = eq_of_carrier(&mut k, carrier, l1, &p.int.nat.logic, lhs, rhs);
        let mut expected_ty = goal;
        for &fv in [A, B].iter().rev() {
            expected_ty = crate::nat_prelude::structures::pi_over(&mut k, fv, carrier, expected_ty);
        }
        assert!(
            k.def_eq(ty, expected_ty),
            "the emitted proof's inferred type must match the stated a*b=b*a goal"
        );
    }

    #[test]
    fn int_false_goal_declines_not_an_identity() {
        const A: u64 = 61_100;
        const B: u64 = 61_101;
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let ring = k.const_(p.algebra.int_comm_ring, vec![]);
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let rn = p.int.nat.structures.comm_ring;
        let (a, b) = (k.fvar(A), k.fvar(B));
        let lhs = mul_of(&mut k, &rn, ring, a, b);
        let rhs = mul_of(&mut k, &rn, ring, a, a);
        let res = prove_eq(
            &mut k,
            &p.int.nat.logic,
            l1,
            &p.int.nat.structures,
            &p.algebra,
            &p.algebra_ext,
            ring,
            lhs,
            rhs,
        );
        assert_eq!(res, Err(Decline::NotAnIdentity));
    }

    #[test]
    fn int_mul_neg_one_shape_via_generic() {
        // (a * b) * (neg one) = neg (b * a)  -- exercises mul_neg_one,
        // mul_comm, and the sign-combination machinery.
        const A: u64 = 61_200;
        const B: u64 = 61_201;
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.algebra.int_comm_ring, vec![]);
        let carrier = k.const_(p.int.z, vec![]);
        let rn = p.int.nat.structures.comm_ring;
        let (a, b) = (k.fvar(A), k.fvar(B));
        let ab = mul_of(&mut k, &rn, ring, a, b);
        let one = sel(&mut k, &rn, structures::idx::comm_ring::ONE, ring);
        let neg_one = neg_of(&mut k, &rn, ring, one);
        let lhs = mul_of(&mut k, &rn, ring, ab, neg_one);
        let ba = mul_of(&mut k, &rn, ring, b, a);
        let rhs = neg_of(&mut k, &rn, ring, ba);

        let proof = prove_eq(
            &mut k,
            &p.int.nat.logic,
            l1,
            &p.int.nat.structures,
            &p.algebra,
            &p.algebra_ext,
            ring,
            lhs,
            rhs,
        )
        .expect("ring::generic must prove (a*b)*(-1) = -(b*a) over Alg.CommRing");
        let _ = close_and_infer(&mut k, carrier, &[A, B], proof);
    }

    // -----------------------------------------------------------------------
    // `AlgS.CommRing` (setoid-flavored), at `CReal.commRingS` — the payoff.
    // -----------------------------------------------------------------------

    fn creal_setup(k: &mut Kernel) -> crate::creal::CRealPrelude {
        crate::creal::build_creal_prelude(k).expect("creal prelude must build")
    }

    fn creal_rn(p: &crate::creal::CRealPrelude) -> RecordNames {
        p.rat.int.nat.structures_s.comm_ring
    }

    #[test]
    fn creal_comm_ring_s_mul_comm_goal() {
        const A: u64 = 62_000;
        const B: u64 = 62_001;
        let mut k = Kernel::new();
        let p = creal_setup(&mut k);
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.comm_ring_s, vec![]);
        let rn = creal_rn(&p);
        let (a, b) = (k.fvar(A), k.fvar(B));
        let lhs = mul_of_s(&mut k, &rn, ring, a, b);
        let rhs = mul_of_s(&mut k, &rn, ring, b, a);
        let proof = prove_eq_s(
            &mut k,
            &p.rat.int.nat.logic,
            l1,
            &p.rat.int.nat.structures_s,
            &p.rat.int.nat.structures_s_extra,
            ring,
            lhs,
            rhs,
        )
        .expect("ring::generic (setoid) must prove a*b=b*a over CReal.commRingS");
        let carrier = sel(&mut k, &rn, structures_s::idx::comm_ring::CARRIER, ring);
        let _ = close_and_infer(&mut k, carrier, &[A, B], proof);
    }

    #[test]
    fn creal_comm_ring_s_distrib_goal() {
        // a * (b + c) = (a*b) + (a*c) -- exercises distribL and reassoc.
        const A: u64 = 62_100;
        const B: u64 = 62_101;
        const C: u64 = 62_102;
        let mut k = Kernel::new();
        let p = creal_setup(&mut k);
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.comm_ring_s, vec![]);
        let rn = creal_rn(&p);
        let (a, b, c) = (k.fvar(A), k.fvar(B), k.fvar(C));
        let bc = add_of_s(&mut k, &rn, ring, b, c);
        let lhs = mul_of_s(&mut k, &rn, ring, a, bc);
        let ab = mul_of_s(&mut k, &rn, ring, a, b);
        let ac = mul_of_s(&mut k, &rn, ring, a, c);
        let rhs = add_of_s(&mut k, &rn, ring, ab, ac);
        let proof = prove_eq_s(
            &mut k,
            &p.rat.int.nat.logic,
            l1,
            &p.rat.int.nat.structures_s,
            &p.rat.int.nat.structures_s_extra,
            ring,
            lhs,
            rhs,
        )
        .expect("ring::generic (setoid) must prove a*(b+c) = a*b+a*c over CReal.commRingS");
        let carrier = sel(&mut k, &rn, structures_s::idx::comm_ring::CARRIER, ring);
        let _ = close_and_infer(&mut k, carrier, &[A, B, C], proof);
    }

    #[test]
    fn creal_comm_ring_s_right_distrib_goal() {
        // (a+b)*c = a*c + b*c -- exercises distribR (the general
        // `distribute` branch, iu.len()>1), the exact shape `right_distrib`
        // needs (a DIAGNOSTIC for the NotAnIdentity found wiring
        // `creal/ring_helpers.rs` into the real prelude build).
        const A: u64 = 62_150;
        const B: u64 = 62_151;
        const C: u64 = 62_152;
        let mut k = Kernel::new();
        let p = creal_setup(&mut k);
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.comm_ring_s, vec![]);
        let rn = creal_rn(&p);
        let (a, b, c) = (k.fvar(A), k.fvar(B), k.fvar(C));
        let ab = add_of_s(&mut k, &rn, ring, a, b);
        let lhs = mul_of_s(&mut k, &rn, ring, ab, c);
        let ac = mul_of_s(&mut k, &rn, ring, a, c);
        let bc = mul_of_s(&mut k, &rn, ring, b, c);
        let rhs = add_of_s(&mut k, &rn, ring, ac, bc);
        let proof = prove_eq_s(
            &mut k,
            &p.rat.int.nat.logic,
            l1,
            &p.rat.int.nat.structures_s,
            &p.rat.int.nat.structures_s_extra,
            ring,
            lhs,
            rhs,
        )
        .expect("ring::generic (setoid) must prove (a+b)*c = a*c+b*c over CReal.commRingS");
        let carrier = sel(&mut k, &rn, structures_s::idx::comm_ring::CARRIER, ring);
        let _ = close_and_infer(&mut k, carrier, &[A, B, C], proof);
    }

    #[test]
    fn creal_comm_ring_s_right_distrib_repeated_arg_goal() {
        // (x+x)*v = x*v + x*v -- `derivative::declare_...`'s own
        // `right_distrib(d, p, half, half, v)` shape: the SAME term used
        // for both summands.
        const X: u64 = 62_160;
        const V: u64 = 62_161;
        let mut k = Kernel::new();
        let p = creal_setup(&mut k);
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.comm_ring_s, vec![]);
        let rn = creal_rn(&p);
        let (x, v) = (k.fvar(X), k.fvar(V));
        let xx = add_of_s(&mut k, &rn, ring, x, x);
        let lhs = mul_of_s(&mut k, &rn, ring, xx, v);
        let xv1 = mul_of_s(&mut k, &rn, ring, x, v);
        let xv2 = mul_of_s(&mut k, &rn, ring, x, v);
        let rhs = add_of_s(&mut k, &rn, ring, xv1, xv2);
        let proof = prove_eq_s(
            &mut k,
            &p.rat.int.nat.logic,
            l1,
            &p.rat.int.nat.structures_s,
            &p.rat.int.nat.structures_s_extra,
            ring,
            lhs,
            rhs,
        )
        .expect("ring::generic (setoid) must prove (x+x)*v = x*v+x*v over CReal.commRingS");
        let carrier = sel(&mut k, &rn, structures_s::idx::comm_ring::CARRIER, ring);
        let _ = close_and_infer(&mut k, carrier, &[X, V], proof);
    }

    #[test]
    fn creal_comm_ring_s_add4_comm_repeated_arg_goal() {
        // (p+p)+(q+q) = (p+q)+(p+q) -- `derivative::declare_...`'s own
        // `add4_comm(d, p, mul_bb, mul_bb, neg_xt, neg_xt)` shape: TWO
        // repeated-argument pairs.
        const P: u64 = 62_170;
        const Q: u64 = 62_171;
        let mut k = Kernel::new();
        let cp = creal_setup(&mut k);
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(cp.comm_ring_s, vec![]);
        let rn = creal_rn(&cp);
        let (p, q) = (k.fvar(P), k.fvar(Q));
        let pp = add_of_s(&mut k, &rn, ring, p, p);
        let qq = add_of_s(&mut k, &rn, ring, q, q);
        let lhs = add_of_s(&mut k, &rn, ring, pp, qq);
        let pq1 = add_of_s(&mut k, &rn, ring, p, q);
        let pq2 = add_of_s(&mut k, &rn, ring, p, q);
        let rhs = add_of_s(&mut k, &rn, ring, pq1, pq2);
        let proof = prove_eq_s(
            &mut k,
            &cp.rat.int.nat.logic,
            l1,
            &cp.rat.int.nat.structures_s,
            &cp.rat.int.nat.structures_s_extra,
            ring,
            lhs,
            rhs,
        )
        .expect("ring::generic (setoid) must prove (p+p)+(q+q) = (p+q)+(p+q) over CReal.commRingS");
        let carrier = sel(&mut k, &rn, structures_s::idx::comm_ring::CARRIER, ring);
        let _ = close_and_infer(&mut k, carrier, &[P, Q], proof);
    }

    #[test]
    fn creal_comm_ring_s_neg_mul_goal() {
        // (neg a) * b = neg (a * b) -- exercises neg_mul_proof directly.
        const A: u64 = 62_200;
        const B: u64 = 62_201;
        let mut k = Kernel::new();
        let p = creal_setup(&mut k);
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.comm_ring_s, vec![]);
        let rn = creal_rn(&p);
        let (a, b) = (k.fvar(A), k.fvar(B));
        let neg_a = neg_of_s(&mut k, &rn, ring, a);
        let lhs = mul_of_s(&mut k, &rn, ring, neg_a, b);
        let ab = mul_of_s(&mut k, &rn, ring, a, b);
        let rhs = neg_of_s(&mut k, &rn, ring, ab);
        let proof = prove_eq_s(
            &mut k,
            &p.rat.int.nat.logic,
            l1,
            &p.rat.int.nat.structures_s,
            &p.rat.int.nat.structures_s_extra,
            ring,
            lhs,
            rhs,
        )
        .expect("ring::generic (setoid) must prove (-a)*b = -(a*b) over CReal.commRingS");
        let carrier = sel(&mut k, &rn, structures_s::idx::comm_ring::CARRIER, ring);
        let _ = close_and_infer(&mut k, carrier, &[A, B], proof);
    }

    #[test]
    fn creal_comm_ring_s_double_neg_goal() {
        // neg (neg a) * b = a * b -- exercises the derived neg_neg.
        const A: u64 = 62_300;
        const B: u64 = 62_301;
        let mut k = Kernel::new();
        let p = creal_setup(&mut k);
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.comm_ring_s, vec![]);
        let rn = creal_rn(&p);
        let (a, b) = (k.fvar(A), k.fvar(B));
        let neg_a = neg_of_s(&mut k, &rn, ring, a);
        let neg_neg_a = neg_of_s(&mut k, &rn, ring, neg_a);
        let lhs = mul_of_s(&mut k, &rn, ring, neg_neg_a, b);
        let rhs = mul_of_s(&mut k, &rn, ring, a, b);
        let proof = prove_eq_s(
            &mut k,
            &p.rat.int.nat.logic,
            l1,
            &p.rat.int.nat.structures_s,
            &p.rat.int.nat.structures_s_extra,
            ring,
            lhs,
            rhs,
        )
        .expect("ring::generic (setoid) must prove -(-a)*b = a*b over CReal.commRingS");
        let carrier = sel(&mut k, &rn, structures_s::idx::comm_ring::CARRIER, ring);
        let _ = close_and_infer(&mut k, carrier, &[A, B], proof);
    }

    #[test]
    fn creal_comm_ring_s_false_goal_declines() {
        const A: u64 = 62_400;
        const B: u64 = 62_401;
        let mut k = Kernel::new();
        let p = creal_setup(&mut k);
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.comm_ring_s, vec![]);
        let rn = creal_rn(&p);
        let (a, b) = (k.fvar(A), k.fvar(B));
        let lhs = mul_of_s(&mut k, &rn, ring, a, b);
        let rhs = mul_of_s(&mut k, &rn, ring, a, a);
        let res = prove_eq_s(
            &mut k,
            &p.rat.int.nat.logic,
            l1,
            &p.rat.int.nat.structures_s,
            &p.rat.int.nat.structures_s_extra,
            ring,
            lhs,
            rhs,
        );
        assert_eq!(res, Err(Decline::NotAnIdentity));
    }

    // -----------------------------------------------------------------------
    // Corrupted certificates — the procedure's own check switched off
    // (`prove_eq_s_unverified`), reaching the KERNEL with a false claim.
    // -----------------------------------------------------------------------

    #[test]
    fn creal_corrupted_certificate_swapped_variable_is_rejected() {
        const A: u64 = 62_500;
        const B: u64 = 62_501;
        let mut k = Kernel::new();
        let p = creal_setup(&mut k);
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.comm_ring_s, vec![]);
        let rn = creal_rn(&p);
        let (a, b) = (k.fvar(A), k.fvar(B));
        // FALSE claim: a*b = a*a (the procedure's own check is disabled, so
        // it happily emits a term of this type; the KERNEL must refuse it
        // against the actually-stated goal).
        let lhs = mul_of_s(&mut k, &rn, ring, a, b);
        let rhs = mul_of_s(&mut k, &rn, ring, a, a);
        let proof = prove_eq_s_unverified(
            &mut k,
            &p.rat.int.nat.logic,
            l1,
            &p.rat.int.nat.structures_s,
            &p.rat.int.nat.structures_s_extra,
            ring,
            lhs,
            rhs,
        )
        .expect("prove_eq_s_unverified must still emit A term (verification is what's disabled)");
        let carrier = sel(&mut k, &rn, structures_s::idx::comm_ring::CARRIER, ring);
        // Close the proof over a and b and declare it directly against the
        // TRUE stated goal `equiv (mul a b) (mul a b)` (reflexivity) -- the
        // emitted term actually proves a DIFFERENT (false) proposition
        // (`equiv (mul a b) (mul a a)`, and for a genuinely non-identical
        // pair the term is not even well-typed on its own, matching
        // `ring::int::tests::kernel_verdict_on`'s own established pattern:
        // go straight to `add_declaration` and require it to fail, rather
        // than asserting anything about a separate `Kernel::infer` call --
        // the trust anchor IS `add_declaration`, and it must reject this
        // either by refusing to infer the value or by refusing the def_eq
        // check against the stated type. Either way is a correct refusal.
        let mut closed = proof;
        for &fv in [A, B].iter().rev() {
            closed = lam_over(&mut k, fv, carrier, closed);
        }
        let true_goal = {
            let equiv = sel(&mut k, &rn, structures_s::idx::comm_ring::EQUIV, ring);
            let e1 = k.app(equiv, lhs);
            k.app(e1, lhs)
        };
        let mut true_ty = true_goal;
        for &fv in [A, B].iter().rev() {
            true_ty = crate::nat_prelude::structures::pi_over(&mut k, fv, carrier, true_ty);
        }
        let anon = k.anon();
        let name = k.name_str(anon, "__ring_generic_corrupted_swapped_variable_test");
        let result = k.add_declaration(crate::Declaration::Theorem {
            name,
            uparams: vec![],
            ty: true_ty,
            value: closed,
        });
        assert!(
            result.is_err(),
            "the KERNEL must reject a corrupted ring::generic certificate proving a*b=a*a \
             when declared against the true reflexive goal a*b=a*b: {result:?}"
        );
    }

    #[test]
    fn creal_uncorrupted_certificate_is_admitted_positive_control() {
        const A: u64 = 62_600;
        const B: u64 = 62_601;
        let mut k = Kernel::new();
        let p = creal_setup(&mut k);
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.comm_ring_s, vec![]);
        let rn = creal_rn(&p);
        let (a, b) = (k.fvar(A), k.fvar(B));
        let lhs = mul_of_s(&mut k, &rn, ring, a, b);
        let rhs = mul_of_s(&mut k, &rn, ring, b, a);
        let proof = prove_eq_s_unverified(
            &mut k,
            &p.rat.int.nat.logic,
            l1,
            &p.rat.int.nat.structures_s,
            &p.rat.int.nat.structures_s_extra,
            ring,
            lhs,
            rhs,
        )
        .expect("must emit a term for the TRUE claim a*b=b*a");
        let carrier = sel(&mut k, &rn, structures_s::idx::comm_ring::CARRIER, ring);
        let mut closed = proof;
        for &fv in [A, B].iter().rev() {
            closed = lam_over(&mut k, fv, carrier, closed);
        }
        let goal = {
            let equiv = sel(&mut k, &rn, structures_s::idx::comm_ring::EQUIV, ring);
            let e1 = k.app(equiv, lhs);
            k.app(e1, rhs)
        };
        let mut ty = goal;
        for &fv in [A, B].iter().rev() {
            ty = crate::nat_prelude::structures::pi_over(&mut k, fv, carrier, ty);
        }
        let anon = k.anon();
        let name = k.name_str(anon, "__ring_generic_uncorrupted_positive_control_test");
        let result = k.add_declaration(crate::Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value: closed,
        });
        assert!(
            result.is_ok(),
            "the KERNEL must ADMIT the true, uncorrupted a*b=b*a certificate: {result:?}"
        );
    }
}

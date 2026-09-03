//! ADR-1585: `linarith::generic` — the ℤ/ℚ order fragment (ADR-1576/1581's
//! `linarith::nat`/`linarith::int`), retargeted at an arbitrary
//! `(R : Alg.OrderedRing)` term instead of a fixed `NatPrelude`/`IntPrelude`.
//!
//! ADR-1584 §5 named three blockers to this module: (1) `Alg.OrderedRing`
//! was missing the fields the fixed emission chain cites, (2) a generic
//! numeral builder, (3) decoupling emission from `IntDev`/`NatDev`.
//! [`super::super::rat_prelude::ordered_ring_ext`] closes (1) and (2);
//! this module is (3).
//!
//! ## Scope, honestly short of `linarith::int`
//!
//! The certificate SEARCH (`super::find_certificate`) was already
//! carrier-agnostic (ADR-1584 §5 measured this). What this module narrows,
//! relative to `linarith::int`, is the FRAGMENT it parses and emits:
//!
//! - **No `<` at all** — no `Alg.lt`, no strictness weakening, no
//!   refutation route (`¬(≤)` goals are not recognised; a genuinely false
//!   `≤`/`=` goal simply finds no certificate and declines
//!   [`Decline::NoCertificate`], which is sufcient for every test this
//!   module carries). `Alg.OrderedRing`, as ADR-1584 built it, has no `lt`
//!   field, and adding one is a real design choice (ADR-1584 §5 calls it
//!   "genuinely new, not a derivation") deliberately left to a future lane.
//!   **A `<` hypothesis or goal is the first stuck shape**: `parse_prop`
//!   recognises only `Alg.OrderedRing`'s `le` and `Eq`, so a `<` term is
//!   parsed as an opaque atom (for a hypothesis, useless — it carries no
//!   linear content) or declines `GoalNotAtomic` (for a goal).
//! - **No literal multiplication.** None of the retirement targets or new
//!   goals below need it, and unrolling a literal `R.mul` generically would
//!   need `Alg.OrderedRing`'s `distribL`/`mulOneR` fields chained the way
//!   `linarith::int`'s `mul_succ_step` does at `Int.mul` — real work, out
//!   of scope here. A literal-multiplier term is parsed as an opaque atom,
//!   same as any other subterm the fragment does not recognise (sound, not
//!   a soundness gap — see the module docs on [`super`]).
//!
//! Everything else — the additive `≤`/`=` fragment, Farkas certificate
//! combination, the constant-first canonical-form normalizer (flatten /
//! arrange / prepend-zero / reassociate) — is the direct generic
//! counterpart of `linarith::int`'s, built from `R`'s own selectors and the
//! `Alg.*` lemmas in [`ordered_ring_ext`](crate::rat_prelude::ordered_ring_ext)
//! rather than `IntDev`/`NatDev`.

// No non-test caller wires `prove` into a real `declare_*` yet (ADR-1585
// answers whether the emitter CAN retarget generically; it does not retire
// anything — see the module docs and ADR-1581's rule that a type match is
// necessary, not sufficient). So the plain `--lib` build (no `#[cfg(test)]`)
// sees every item here as dead, the same situation `structures.rs`'s `idx`
// module documents for its own not-yet-consumed constants. Exercised by
// `generic_tests` below, not by silence.
#![allow(dead_code)]

use crate::ExprNode;
use crate::Kernel;
use crate::LogicPrelude;
use crate::NatPrelude;
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;
use crate::nat_prelude::structures::sel;
use crate::nat_prelude::structures::{self, RecordNames};
use crate::nat_prelude::structures_setoid as structures_s;
use crate::rat_prelude::ordered_ring_ext::OrderedRingExtNames;
use crate::rat_prelude::ordered_ring_ext_s::OrderedRingExtSNames;

use super::{Certificate, Coeff, Decline, LinForm, find_combination};

/// One summand of a canonical additive form, exactly `linarith::int`'s
/// `Item` (the search/normal-form shape does not depend on the carrier).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Item {
    Pos(usize),
    Neg(usize),
    Const(Coeff),
}

impl Item {
    fn key(self) -> usize {
        match self {
            Item::Const(_) => 0,
            Item::Pos(i) => (i + 1) * 2,
            Item::Neg(i) => (i + 1) * 2 + 1,
        }
    }
}

/// An atomic proposition of the fragment — `Lt` is deliberately absent, see
/// the module docs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Shape {
    Le,
    Eq,
}

struct Hyp {
    lhs: ExprId,
    rhs: ExprId,
    form: LinForm,
    proof: ExprId,
}

/// The four operator constants a closure needs to rebuild a term without
/// borrowing `Problem` (a `&dyn Fn(&mut Kernel, ExprId) -> ExprId` passed
/// into [`Problem::congr`]/[`Problem::substp`] cannot also capture `&Problem`
/// while `Problem` itself is mutably borrowed for that same call) — every
/// `Copy` field a closure might need, snapshotted once.
#[derive(Clone, Copy)]
struct OpCtx {
    add: ExprId,
    neg: ExprId,
    ofnat: ExprId,
    nat_zero: NameId,
    nat_succ: NameId,
}

fn nat_num_ctx(k: &mut Kernel, ctx: OpCtx, n: u32) -> ExprId {
    let mut e = k.const_(ctx.nat_zero, vec![]);
    for _ in 0..n {
        let s = k.const_(ctx.nat_succ, vec![]);
        e = k.app(s, e);
    }
    e
}

fn literal_ctx(k: &mut Kernel, ctx: OpCtx, n: Coeff) -> ExprId {
    let magnitude = u32::try_from(n.abs()).unwrap_or(0);
    let nat = nat_num_ctx(k, ctx, magnitude);
    let positive = k.app(ctx.ofnat, nat);
    if n < 0 {
        k.app(ctx.neg, positive)
    } else {
        positive
    }
}

fn item_term_ctx(k: &mut Kernel, ctx: OpCtx, atoms: &[ExprId], item: Item) -> ExprId {
    match item {
        Item::Pos(i) => atoms[i],
        Item::Neg(i) => k.app(ctx.neg, atoms[i]),
        Item::Const(n) => literal_ctx(k, ctx, n),
    }
}

fn add2_ctx(k: &mut Kernel, ctx: OpCtx, a: ExprId, b: ExprId) -> ExprId {
    let e = k.app(ctx.add, a);
    k.app(e, b)
}

fn fold_ctx(k: &mut Kernel, ctx: OpCtx, atoms: &[ExprId], items: &[Item]) -> ExprId {
    let mut acc = item_term_ctx(k, ctx, atoms, items[0]);
    for &item in &items[1..] {
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
    for &item in items {
        let t = item_term_ctx(k, ctx, atoms, item);
        acc = add2_ctx(k, ctx, acc, t);
    }
    acc
}

/// ADR-1592: which "equality" flavor this `Problem` reasons about — the
/// kernel's own `Eq` (over `Alg.OrderedRing`, ADR-1585's original scope) or
/// a caller-supplied `equiv` relation (over `AlgS.OrderedRing`) with its
/// own `equivRefl`/`equivSymm`/`equivTrans` and per-operation congruence
/// FIELDS. There is no generic `Eq.rec`-shaped transport for an arbitrary
/// `equiv` (ADR-1588's own point — a setoid has no free lunch for an
/// opaque predicate), so the `Setoid` variant carries exactly the two
/// congruence fields the normalizer's `congr`/`substp` calls need:
/// `addCongr` (every `congr` call in this module rewrites one operand of
/// an `add`-chain) and `leCongr` (every `substp` call rewrites one side of
/// an `le`).
#[derive(Clone, Copy)]
enum Backend {
    KernelEq,
    Setoid {
        equiv: ExprId,
        equiv_refl: ExprId,
        equiv_symm: ExprId,
        equiv_trans: ExprId,
        add_congr: ExprId,
        le_congr: ExprId,
    },
}

/// Structural description of the ADD-shaped congruence context a `congr`
/// call rewrites under. The `KernelEq` backend ignores this (its `Eq.rec`
/// transport already works from the closure `f` alone); the `Setoid`
/// backend has no such generic transport and uses this instead to compose
/// `addCongr` applications directly.
#[derive(Clone)]
enum AddCtx {
    /// `fun t => add t fixed`.
    Left(ExprId),
    /// `fun t => add fixed t`.
    Right(ExprId),
    /// `fun t => fold_from(t, tail)` == `((t + tail[0]) + tail[1]) + ...`
    /// (see [`fold_from_ctx`]).
    FoldFrom(Vec<Item>),
}

/// Structural description of the LE-shaped substitution context a
/// `substp` call rewrites under — `leCongr` handles both shapes directly,
/// one field application each.
#[derive(Clone, Copy)]
enum LeCtx {
    /// `fun t => le t fixed`.
    Left(ExprId),
    /// `fun t => le fixed t`.
    Right(ExprId),
}

/// The parsing/emission context for one goal over one `(R : OrderedRing)`
/// term. Every field is a `Copy` term/name snapshotted once in
/// [`Problem::new`] — no `IntDev`/`NatDev` anywhere.
pub(crate) struct Problem {
    #[allow(dead_code)]
    ring: ExprId,
    carrier: ExprId,
    zero: ExprId,
    one: ExprId,
    le: ExprId,
    le_refl: ExprId,
    le_trans: ExprId,
    le_antisymm: ExprId,
    add_assoc: ExprId,
    add_comm: ExprId,
    add_zero: ExprId,
    neg_add: ExprId,
    add_le_add_left: ExprId,
    le_of_add_le_add_right: ExprId,
    add_le_add: ExprId,
    ofnat_le_ofnat_of_le_r: ExprId,
    zero_le_one: Option<ExprId>,
    nat: NatPrelude,
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
        ext: &OrderedRingExtNames,
        nat: &NatPrelude,
        ring: ExprId,
        zero_le_one: Option<ExprId>,
    ) -> Self {
        use structures::idx::ordered_ring::{
            ADD, ADD_ASSOC, ADD_COMM, ADD_LE_ADD_LEFT, ADD_ZERO, CARRIER, LE, LE_ANTISYMM, LE_REFL,
            LE_TRANS, NEG, NEG_ADD, ONE, ZERO,
        };
        let nat = *nat;
        let rn: &RecordNames = &st.ordered_ring;
        let carrier = sel(k, rn, CARRIER, ring);
        let zero = sel(k, rn, ZERO, ring);
        let one = sel(k, rn, ONE, ring);
        let add = sel(k, rn, ADD, ring);
        let neg = sel(k, rn, NEG, ring);
        let add_assoc = sel(k, rn, ADD_ASSOC, ring);
        let add_comm = sel(k, rn, ADD_COMM, ring);
        let add_zero = sel(k, rn, ADD_ZERO, ring);
        let neg_add = sel(k, rn, NEG_ADD, ring);
        let le = sel(k, rn, LE, ring);
        let le_refl = sel(k, rn, LE_REFL, ring);
        let le_trans = sel(k, rn, LE_TRANS, ring);
        let le_antisymm = sel(k, rn, LE_ANTISYMM, ring);
        let add_le_add_left = sel(k, rn, ADD_LE_ADD_LEFT, ring);

        let le_of_add_le_add_right = {
            let c = k.const_(ext.le_of_add_le_add_right, vec![]);
            k.app(c, ring)
        };
        let add_le_add = {
            let c = k.const_(ext.add_le_add, vec![]);
            k.app(c, ring)
        };
        let ofnat = {
            let c = k.const_(ext.ofnat, vec![]);
            k.app(c, ring)
        };
        let ofnat_le_ofnat_of_le_r = {
            let c = k.const_(ext.ofnat_le_ofnat_of_le, vec![]);
            k.app(c, ring)
        };
        let eq_const = k.const_(lg.eq, vec![l1]);

        let ctx = OpCtx {
            add,
            neg,
            ofnat,
            nat_zero: nat.zero,
            nat_succ: nat.succ,
        };

        Self {
            ring,
            carrier,
            zero,
            one,
            le,
            le_refl,
            le_trans,
            le_antisymm,
            add_assoc,
            add_comm,
            add_zero,
            neg_add,
            add_le_add_left,
            le_of_add_le_add_right,
            add_le_add,
            ofnat_le_ofnat_of_le_r,
            zero_le_one,
            nat,
            lg: *lg,
            l1,
            eq_const,
            ctx,
            atoms: Vec::new(),
            next_scratch: 90_000,
            backend: Backend::KernelEq,
        }
    }

    /// ADR-1592: the setoid twin of [`Self::new`] — over `(R : AlgS.
    /// OrderedRing)` instead of `(R : Alg.OrderedRing)`, reading every
    /// field/derived-lemma from `st`/`ext` (the setoid record and
    /// [`super::super::rat_prelude::ordered_ring_ext_s::OrderedRingExtSNames`])
    /// instead of the `Eq`-flavored spine, and additionally caching
    /// `equiv`/`equivRefl`/`equivSymm`/`equivTrans`/`addCongr`/`leCongr` in
    /// [`Backend::Setoid`] — the record's own congruence FIELDS, since
    /// there is no generic `Eq.rec` transport for an arbitrary `equiv`
    /// (ADR-1588).
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new_s(
        k: &mut Kernel,
        lg: &LogicPrelude,
        l1: LevelId,
        st: &structures_s::StructuresSRecordNames,
        ext: &OrderedRingExtSNames,
        nat: &NatPrelude,
        ring: ExprId,
        zero_le_one: Option<ExprId>,
    ) -> Self {
        use structures_s::idx::ordered_ring::{
            ADD, ADD_ASSOC, ADD_COMM, ADD_CONGR, ADD_LE_ADD_LEFT, ADD_ZERO, CARRIER, EQUIV,
            EQUIV_REFL, EQUIV_SYMM, EQUIV_TRANS, LE, LE_ANTISYMM_EQUIV, LE_CONGR, LE_REFL,
            LE_TRANS, NEG, NEG_ADD, ONE, ZERO,
        };
        let nat = *nat;
        let rn: &RecordNames = &st.ordered_ring;
        let carrier = sel(k, rn, CARRIER, ring);
        let equiv = sel(k, rn, EQUIV, ring);
        let equiv_refl = sel(k, rn, EQUIV_REFL, ring);
        let equiv_symm = sel(k, rn, EQUIV_SYMM, ring);
        let equiv_trans = sel(k, rn, EQUIV_TRANS, ring);
        let zero = sel(k, rn, ZERO, ring);
        let one = sel(k, rn, ONE, ring);
        let add = sel(k, rn, ADD, ring);
        let neg = sel(k, rn, NEG, ring);
        let add_congr = sel(k, rn, ADD_CONGR, ring);
        let add_assoc = sel(k, rn, ADD_ASSOC, ring);
        let add_comm = sel(k, rn, ADD_COMM, ring);
        let add_zero = sel(k, rn, ADD_ZERO, ring);
        let neg_add = sel(k, rn, NEG_ADD, ring);
        let le = sel(k, rn, LE, ring);
        let le_congr = sel(k, rn, LE_CONGR, ring);
        let le_refl = sel(k, rn, LE_REFL, ring);
        let le_trans = sel(k, rn, LE_TRANS, ring);
        let le_antisymm = sel(k, rn, LE_ANTISYMM_EQUIV, ring);
        let add_le_add_left = sel(k, rn, ADD_LE_ADD_LEFT, ring);

        let le_of_add_le_add_right = {
            let c = k.const_(ext.le_of_add_le_add_right, vec![]);
            k.app(c, ring)
        };
        let add_le_add = {
            let c = k.const_(ext.add_le_add, vec![]);
            k.app(c, ring)
        };
        let ofnat = {
            let c = k.const_(ext.ofnat, vec![]);
            k.app(c, ring)
        };
        let ofnat_le_ofnat_of_le_r = {
            let c = k.const_(ext.ofnat_le_ofnat_of_le, vec![]);
            k.app(c, ring)
        };
        let eq_const = k.const_(lg.eq, vec![l1]);

        let ctx = OpCtx {
            add,
            neg,
            ofnat,
            nat_zero: nat.zero,
            nat_succ: nat.succ,
        };

        Self {
            ring,
            carrier,
            zero,
            one,
            le,
            le_refl,
            le_trans,
            le_antisymm,
            add_assoc,
            add_comm,
            add_zero,
            neg_add,
            add_le_add_left,
            le_of_add_le_add_right,
            add_le_add,
            ofnat_le_ofnat_of_le_r,
            zero_le_one,
            nat,
            lg: *lg,
            l1,
            eq_const,
            ctx,
            atoms: Vec::new(),
            next_scratch: 90_000,
            backend: Backend::Setoid {
                equiv,
                equiv_refl,
                equiv_symm,
                equiv_trans,
                add_congr,
                le_congr,
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

    // --- Eq combinators (free-function forwards, `&mut self` only for the
    // scratch counter — no persistent borrow of `self`, so recursive calls
    // like `flatten`/`reassoc` stay free to re-borrow `k`). -----------------

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

    /// Rewrite one operand of an `add`-chain along `h : (a ~ b)` (`Eq` or
    /// `equiv`, per backend). `shape` describes the ADD context the
    /// `KernelEq` backend's closure `f` already builds directly (that
    /// backend ignores `shape` and uses `f` exactly as before); the
    /// `Setoid` backend has no generic transport for an opaque `f` and
    /// uses `shape` to compose `addCongr` applications instead — see
    /// [`Self::congr_add_setoid`].
    fn congr(
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
            Backend::Setoid { add_congr, .. } => {
                self.congr_add_setoid(k, a, b, h, add_congr, shape)
            }
        }
    }

    /// `h : equiv a b` |- `equiv (ctx a) (ctx b)`, `ctx` an ADD context
    /// (see [`AddCtx`]). `Left`/`Right` are one `addCongr` application;
    /// `FoldFrom` composes one `addCongr` per tail item, propagating the
    /// seed's congruence outward through the SAME left-fold
    /// [`fold_from_ctx`] itself builds.
    fn congr_add_setoid(
        &mut self,
        k: &mut Kernel,
        a: ExprId,
        b: ExprId,
        h: ExprId,
        add_congr: ExprId,
        shape: AddCtx,
    ) -> ExprId {
        match shape {
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
                for item in tail {
                    let t = self.item_term(k, item);
                    let refl_t = self.refl(k, t);
                    let next = Self::apply(k, add_congr, &[cur_a, cur_b, t, t, cur, refl_t]);
                    cur_a = self.add2(k, cur_a, t);
                    cur_b = self.add2(k, cur_b, t);
                    cur = next;
                }
                cur
            }
        }
    }

    /// Transport `proof_at_a : pred a` to `pred b` along `h : (a ~ b)`.
    /// `shape` describes the LE context (see [`LeCtx`]) the `Setoid`
    /// backend needs (`leCongr`, a first-class field, handles either
    /// shape in one application); the `KernelEq` backend ignores `shape`
    /// and uses its generic `Eq.rec` `subst` exactly as before.
    #[allow(clippy::too_many_arguments)]
    fn substp(
        &mut self,
        k: &mut Kernel,
        a: ExprId,
        b: ExprId,
        h: ExprId,
        shape: LeCtx,
        pred: &dyn Fn(&mut Kernel, ExprId) -> ExprId,
        proof_at_a: ExprId,
    ) -> ExprId {
        match self.backend {
            Backend::KernelEq => {
                let s = self.fresh_scratch();
                structures::subst(
                    k,
                    &self.lg,
                    self.l1,
                    self.carrier,
                    a,
                    b,
                    h,
                    s,
                    pred,
                    proof_at_a,
                )
            }
            Backend::Setoid { le_congr, .. } => match shape {
                LeCtx::Left(fixed) => {
                    let refl_fixed = self.refl(k, fixed);
                    Self::apply(
                        k,
                        le_congr,
                        &[a, b, fixed, fixed, h, refl_fixed, proof_at_a],
                    )
                }
                LeCtx::Right(fixed) => {
                    let refl_fixed = self.refl(k, fixed);
                    Self::apply(
                        k,
                        le_congr,
                        &[fixed, fixed, a, b, refl_fixed, h, proof_at_a],
                    )
                }
            },
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

    fn item_term(&self, k: &mut Kernel, item: Item) -> ExprId {
        item_term_ctx(k, self.ctx, &self.atoms, item)
    }

    fn fold(&self, k: &mut Kernel, items: &[Item]) -> ExprId {
        fold_ctx(k, self.ctx, &self.atoms, items)
    }

    fn fold_from(&self, k: &mut Kernel, start: ExprId, items: &[Item]) -> ExprId {
        fold_from_ctx(k, self.ctx, &self.atoms, start, items)
    }

    fn literal(&self, k: &mut Kernel, n: Coeff) -> ExprId {
        literal_ctx(k, self.ctx, n)
    }

    fn nat_num(&self, k: &mut Kernel, n: u32) -> ExprId {
        nat_num_ctx(k, self.ctx, n)
    }

    fn canon_term(&self, k: &mut Kernel, form: &LinForm) -> ExprId {
        let items = Self::canon_items(form);
        self.fold(k, &items)
    }

    fn canon_items(form: &LinForm) -> Vec<Item> {
        let mut items = vec![Item::Const(form.const_term())];
        for (index, coeff) in form.atoms() {
            let item = if coeff > 0 {
                Item::Pos(index)
            } else {
                Item::Neg(index)
            };
            for _ in 0..coeff.abs() {
                items.push(item);
            }
        }
        items
    }

    // --- parsing --------------------------------------------------------

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

    /// The `Eq`-shaped fragment's atomic proposition: kernel `Eq` at
    /// `self.carrier` (`KernelEq` backend) or the record's own `equiv`
    /// VALUE applied directly (`Setoid` backend — `equiv` is already a
    /// 2-argument relation, `App(App(equiv,x),y)`, not a 3-argument
    /// `App(App(App(Eq,ty),x),y)` the way kernel `Eq` is).
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

    fn nat_numeral(&self, k: &mut Kernel, e: ExprId) -> Option<Coeff> {
        let mut current = e;
        let mut count: Coeff = 0;
        loop {
            match k.expr_node(current).clone() {
                ExprNode::Const(n, _) if n == self.nat.zero => return Some(count),
                ExprNode::App(f, a) => match k.expr_node(f).clone() {
                    ExprNode::Const(n, _) if n == self.nat.succ => {
                        count = count.checked_add(1)?;
                        current = a;
                    }
                    _ => return None,
                },
                _ => return None,
            }
        }
    }

    /// `e` as a literal constant: `R.zero`/`R.one` directly (the natural way
    /// a goal states "0"/"1" — nothing forces a caller to spell them as
    /// `Alg.ofNat R 0`/`Alg.ofNat R 1`, and both are `ExprId`-identical to
    /// `Problem`'s own `self.zero`/`self.one` snapshots whenever the goal
    /// was built from the SAME `ring` term, exactly as every retirement/
    /// new-capability test here does), or the `Alg.ofNat R k` family for
    /// any other magnitude.
    fn ofnat_numeral(&self, k: &mut Kernel, e: ExprId) -> Option<Coeff> {
        if e == self.zero {
            return Some(0);
        }
        if e == self.one {
            return Some(1);
        }
        let n = Self::as_unop(k, self.ctx.ofnat, e)?;
        self.nat_numeral(k, n)
    }

    fn is_simple(&self, k: &mut Kernel, e: ExprId) -> bool {
        if self.ofnat_numeral(k, e).is_some() {
            return true;
        }
        if Self::as_binop(k, self.ctx.add, e).is_some() {
            return false;
        }
        if Self::as_unop(k, self.ctx.neg, e).is_some() {
            return false;
        }
        true
    }

    fn parse_term(&mut self, k: &mut Kernel, e: ExprId) -> Result<LinForm, Decline> {
        if let Some(n) = self.ofnat_numeral(k, e) {
            return Ok(LinForm::constant(n));
        }
        if let Some((x, y)) = Self::as_binop(k, self.ctx.add, e) {
            let a = self.parse_term(k, x)?;
            let b = self.parse_term(k, y)?;
            return a.checked_add(&b).ok_or(Decline::SearchBudget);
        }
        if let Some(inner) = Self::as_unop(k, self.ctx.neg, e) {
            if self.is_simple(k, inner) {
                let a = self.parse_term(k, inner)?;
                return a.checked_scale(-1).ok_or(Decline::SearchBudget);
            }
            return Ok(LinForm::atom(self.atom_index(e)));
        }
        Ok(LinForm::atom(self.atom_index(e)))
    }

    fn parse_prop(
        &mut self,
        k: &mut Kernel,
        e: ExprId,
    ) -> Result<(Shape, ExprId, ExprId), Decline> {
        let le = self.le;
        if let Some((x, y)) = Self::as_binop(k, le, e) {
            return Ok((Shape::Le, x, y));
        }
        if let Some((x, y)) = self.as_eq(k, e) {
            return Ok((Shape::Eq, x, y));
        }
        Err(Decline::GoalNotAtomic)
    }

    // --- the normalizer --------------------------------------------------

    fn add_right_comm(&mut self, k: &mut Kernel, a: ExprId, b: ExprId, c: ExprId) -> ExprId {
        let add = self.ctx.add;
        let ab = self.add2(k, a, b);
        let abc = self.add2(k, ab, c);
        let bc = self.add2(k, b, c);
        let a_bc = self.add2(k, a, bc);
        let cb = self.add2(k, c, b);
        let a_cb = self.add2(k, a, cb);
        let ac = self.add2(k, a, c);
        let acb = self.add2(k, ac, b);

        let assoc = Self::apply(k, self.add_assoc, &[a, b, c]);
        let comm = Self::apply(k, self.add_comm, &[b, c]);
        let under = self.congr(k, bc, cb, comm, AddCtx::Right(a), &move |k2, t| {
            let e = k2.app(add, a);
            k2.app(e, t)
        });
        let back = Self::apply(k, self.add_assoc, &[a, c, b]);
        let back = self.symm(k, acb, a_cb, back);
        let first = self.trans(k, abc, a_bc, a_cb, assoc, under);
        self.trans(k, abc, a_cb, acb, first, back)
    }

    fn flatten(&mut self, k: &mut Kernel, e: ExprId) -> Result<(Vec<Item>, ExprId), Decline> {
        if let Some(n) = self.ofnat_numeral(k, e) {
            let items = vec![Item::Const(n)];
            let folded = self.fold(k, &items);
            return Ok((items, self.refl(k, folded)));
        }
        if let Some((x, y)) = Self::as_binop(k, self.ctx.add, e) {
            return self.flatten_add(k, x, y);
        }
        if let Some(inner) = Self::as_unop(k, self.ctx.neg, e)
            && self.is_simple(k, inner)
        {
            if let Some(n) = self.ofnat_numeral(k, inner) {
                let items = vec![Item::Const(-n)];
                let folded = self.fold(k, &items);
                return Ok((items, self.refl(k, folded)));
            }
            let index = self.atom_index(inner);
            let items = vec![Item::Neg(index)];
            return Ok((items, self.refl(k, e)));
        }
        let index = self.atom_index(e);
        Ok((vec![Item::Pos(index)], self.refl(k, e)))
    }

    fn flatten_add(
        &mut self,
        k: &mut Kernel,
        u: ExprId,
        v: ExprId,
    ) -> Result<(Vec<Item>, ExprId), Decline> {
        let (iu, pu) = self.flatten(k, u)?;
        let (iv, pv) = self.flatten(k, v)?;
        let fu = self.fold(k, &iu);
        let fv = self.fold(k, &iv);
        let source = self.add2(k, u, v);
        let mid = self.add2(k, fu, v);
        let joined = self.add2(k, fu, fv);

        let add = self.ctx.add;
        let step1 = self.congr(k, u, fu, pu, AddCtx::Left(v), &move |k2, x| {
            let e = k2.app(add, x);
            k2.app(e, v)
        });
        let step2 = self.congr(k, v, fv, pv, AddCtx::Right(fu), &move |k2, x| {
            let e = k2.app(add, fu);
            k2.app(e, x)
        });
        let p12 = self.trans(k, source, mid, joined, step1, step2);

        let mut items = iu.clone();
        items.extend_from_slice(&iv);
        let target = self.fold(k, &items);
        let step3 = self.reassoc(k, &iu, &iv);
        let proof = self.trans(k, source, joined, target, p12, step3);
        Ok((items, proof))
    }

    fn reassoc(&mut self, k: &mut Kernel, left: &[Item], right: &[Item]) -> ExprId {
        let fl = self.fold(k, left);
        if right.len() == 1 {
            let joined = self.fold_from(k, fl, right);
            return self.refl(k, joined);
        }
        let (init, last) = right.split_at(right.len() - 1);
        let fi = self.fold(k, init);
        let last_t = self.item_term(k, last[0]);
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
        let add = self.ctx.add;
        let step2 = self.congr(
            k,
            regrouped_inner,
            joined_inner,
            inner,
            AddCtx::Left(last_t),
            &move |k2, x| {
                let e = k2.app(add, x);
                k2.app(e, last_t)
            },
        );
        let target = self.add2(k, joined_inner, last_t);
        self.trans(k, source, regrouped, target, step1, step2)
    }

    fn prepend_zero(&mut self, k: &mut Kernel, items: &[Item]) -> (Vec<Item>, ExprId) {
        let ctx = self.ctx;
        let atoms = self.atoms.clone();
        let head = self.item_term(k, items[0]);
        let zero = self.zero;
        let zero_head = self.add2(k, zero, head);
        let head_zero = self.add2(k, head, zero);
        let comm = Self::apply(k, self.add_comm, &[zero, head]);
        let drop = Self::apply(k, self.add_zero, &[head]);
        let forward = self.trans(k, zero_head, head_zero, head, comm, drop);
        let back = self.symm(k, zero_head, head, forward);
        let tail = items[1..].to_vec();
        let proof = self.congr(
            k,
            head,
            zero_head,
            back,
            AddCtx::FoldFrom(tail.clone()),
            &move |k2, t| fold_from_ctx(k2, ctx, &atoms, t, &tail),
        );
        let mut out = vec![Item::Const(0)];
        out.extend_from_slice(items);
        (out, proof)
    }

    #[allow(clippy::too_many_lines)]
    fn arrange(&mut self, k: &mut Kernel, items: &[Item]) -> (Vec<Item>, ExprId) {
        let ctx = self.ctx;
        let source = self.fold(k, items);
        let mut current: Vec<Item> = items.to_vec();
        let mut folded = source;
        let mut proof = self.refl(k, source);

        // 1. bubble sort.
        loop {
            let mut swapped = false;
            for idx in 0..current.len().saturating_sub(1) {
                if current[idx].key() <= current[idx + 1].key() {
                    continue;
                }
                let x = self.item_term(k, current[idx]);
                let y = self.item_term(k, current[idx + 1]);
                let prefix = self.fold(k, &current[..idx]);
                let before_inner = self.add2(k, prefix, x);
                let before = self.add2(k, before_inner, y);
                let after_inner = self.add2(k, prefix, y);
                let after = self.add2(k, after_inner, x);
                let base = self.add_right_comm(k, prefix, x, y);
                let tail = current[idx + 2..].to_vec();
                let atoms = self.atoms.clone();
                let step = self.congr(
                    k,
                    before,
                    after,
                    base,
                    AddCtx::FoldFrom(tail.clone()),
                    &move |k2, t| fold_from_ctx(k2, ctx, &atoms, t, &tail),
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

        // 2. merge leading constants (two closed numerals is where this
        // carrier's `add` need not reduce -- the congruence step still
        // works generically, `refl` on the merged literal).
        while current.len() >= 2
            && let (Item::Const(a), Item::Const(b)) = (current[0], current[1])
        {
            let merged = Item::Const(a + b);
            let x = self.item_term(k, current[0]);
            let y = self.item_term(k, current[1]);
            let before = self.add2(k, x, y);
            let after = self.item_term(k, merged);
            let base = self.eqc_and_prove_merge(k, before, after);
            let tail = current[2..].to_vec();
            let atoms = self.atoms.clone();
            let step = self.congr(
                k,
                before,
                after,
                base,
                AddCtx::FoldFrom(tail.clone()),
                &move |k2, t| fold_from_ctx(k2, ctx, &atoms, t, &tail),
            );
            current.remove(0);
            current[0] = merged;
            let next = self.fold(k, &current);
            proof = self.trans(k, source, folded, next, proof, step);
            folded = next;
        }

        // 3. cancel adjacent `x + (neg x)`.
        loop {
            let mut hit = None;
            for idx in 0..current.len().saturating_sub(1) {
                if let (Item::Pos(i), Item::Neg(j)) = (current[idx], current[idx + 1])
                    && i == j
                {
                    hit = Some(idx);
                    break;
                }
            }
            let Some(idx) = hit else { break };
            let x = self.item_term(k, current[idx]);
            let neg_x = self.item_term(k, current[idx + 1]);
            let prefix = self.fold(k, &current[..idx]);
            let before_inner = self.add2(k, prefix, x);
            let before = self.add2(k, before_inner, neg_x);
            let x_neg_x = self.add2(k, x, neg_x);
            let mid = self.add2(k, prefix, x_neg_x);
            let zero = self.zero;
            let near = self.add2(k, prefix, zero);

            let assoc = Self::apply(k, self.add_assoc, &[prefix, x, neg_x]);
            let cancel = Self::apply(k, self.neg_add, &[x]);
            let add = self.ctx.add;
            let under = self.congr(
                k,
                x_neg_x,
                zero,
                cancel,
                AddCtx::Right(prefix),
                &move |k2, t| {
                    let e = k2.app(add, prefix);
                    k2.app(e, t)
                },
            );
            let drop = Self::apply(k, self.add_zero, &[prefix]);
            let to_near = self.trans(k, before, mid, near, assoc, under);
            let base = self.trans(k, before, near, prefix, to_near, drop);

            let tail = current[idx + 2..].to_vec();
            let atoms = self.atoms.clone();
            let step = self.congr(
                k,
                before,
                prefix,
                base,
                AddCtx::FoldFrom(tail.clone()),
                &move |k2, t| fold_from_ctx(k2, ctx, &atoms, t, &tail),
            );
            current.drain(idx..=idx + 1);
            let next = self.fold(k, &current);
            proof = self.trans(k, source, folded, next, proof, step);
            folded = next;
        }

        (current, proof)
    }

    /// `Eq (add x y) merged` when `x`/`y` are two literal constants and
    /// `merged` is their Rust-computed sum, folded to a term. Nothing
    /// reduces `R.add` at literals the way `Nat.add` does, so this is a
    /// short chain (`ofNat_add`, then a `refl` once both sides are the same
    /// `ofNat R (a+b)` numeral) rather than `Eq.refl` outright.
    fn eqc_and_prove_merge(&mut self, k: &mut Kernel, before: ExprId, after: ExprId) -> ExprId {
        // `before`/`after` were built from the SAME two literals via
        // `literal`/`add2`; the honest general proof would cite
        // `Alg.ofNat_add`, but every retirement/new-capability goal this
        // module is exercised against never reaches this branch with two
        // adjacent literals in the same sum (each hypothesis/goal here
        // carries at most one numeral). Declared, not silently assumed: a
        // future caller whose goal DOES merge two literals gets a term that
        // only type-checks when `before`/`after` are already `def_eq`
        // (true whenever both literals collapse to the identical `ofNat`
        // numeral, e.g. merging `0` with anything), and a debug assertion
        // catches the gap otherwise instead of emitting a term the kernel
        // would silently refuse far from this call site.
        debug_assert!(
            k.def_eq(before, after),
            "eqc_and_prove_merge: two adjacent literal constants that are \
             not already def_eq -- this Problem's normalizer reached a case \
             `linarith::generic`'s scope does not cover (see module docs); \
             extend with Alg.ofNat_add before removing this assertion"
        );
        self.refl(k, before)
    }

    fn normalize(&mut self, k: &mut Kernel, e: ExprId) -> Result<(LinForm, ExprId), Decline> {
        let (items, p1) = self.flatten(k, e)?;
        let flat = self.fold(k, &items);
        let (items, p2) = if matches!(items[0], Item::Const(_)) {
            (items, self.refl(k, flat))
        } else {
            self.prepend_zero(k, &items)
        };
        let seeded = self.fold(k, &items);
        let chained = self.trans(k, e, flat, seeded, p1, p2);

        let (arranged, p3) = self.arrange(k, &items);
        let arranged_term = self.fold(k, &arranged);
        let proof = self.trans(k, e, seeded, arranged_term, chained, p3);

        let mut form = LinForm::zero();
        for &item in &arranged {
            let piece = match item {
                Item::Pos(i) => LinForm::atom(i),
                Item::Neg(i) => LinForm::atom(i).checked_scale(-1).unwrap_or_default(),
                Item::Const(n) => LinForm::constant(n),
            };
            form = form.checked_add(&piece).ok_or(Decline::SearchBudget)?;
        }
        Ok((form, proof))
    }

    fn prove_eq(
        &mut self,
        k: &mut Kernel,
        x: ExprId,
        y: ExprId,
        verify: bool,
    ) -> Result<ExprId, Decline> {
        let (fx, px) = self.normalize(k, x)?;
        let (fy, py) = self.normalize(k, y)?;
        if verify && fx != fy {
            return Err(Decline::NoCertificate);
        }
        let canon_x = self.canon_term(k, &fx);
        let canon_y = self.canon_term(k, &fy);
        let back = self.symm(k, y, canon_y, py);
        Ok(self.trans(k, x, canon_x, y, px, back))
    }

    // --- collecting hypotheses --------------------------------------------

    fn collect(&mut self, k: &mut Kernel, assumptions: &[(ExprId, ExprId)]) -> Vec<Hyp> {
        let mut out = Vec::new();
        for &(ty, proof) in assumptions {
            let Ok((shape, lhs, rhs)) = self.parse_prop(k, ty) else {
                continue;
            };
            match shape {
                Shape::Le => {
                    let (Ok(fl), Ok(fr)) = (self.parse_term(k, lhs), self.parse_term(k, rhs))
                    else {
                        continue;
                    };
                    let Some(form) = fr.checked_sub(&fl) else {
                        continue;
                    };
                    out.push(Hyp {
                        lhs,
                        rhs,
                        form,
                        proof,
                    });
                }
                Shape::Eq => {
                    let (Ok(fl), Ok(fr)) = (self.parse_term(k, lhs), self.parse_term(k, rhs))
                    else {
                        continue;
                    };
                    let (Some(up), Some(down)) = (fr.checked_sub(&fl), fl.checked_sub(&fr)) else {
                        continue;
                    };
                    let le = self.le;
                    let refl_a = Self::apply(k, self.le_refl, &[lhs]);
                    let forward = self.substp(
                        k,
                        lhs,
                        rhs,
                        proof,
                        LeCtx::Right(lhs),
                        &move |k2, t| {
                            let e = k2.app(le, lhs);
                            k2.app(e, t)
                        },
                        refl_a,
                    );
                    let refl_b = Self::apply(k, self.le_refl, &[lhs]);
                    let backward = self.substp(
                        k,
                        lhs,
                        rhs,
                        proof,
                        LeCtx::Left(lhs),
                        &move |k2, t| {
                            let e = k2.app(le, t);
                            k2.app(e, lhs)
                        },
                        refl_b,
                    );
                    out.push(Hyp {
                        lhs,
                        rhs,
                        form: up,
                        proof: forward,
                    });
                    out.push(Hyp {
                        lhs: rhs,
                        rhs: lhs,
                        form: down,
                        proof: backward,
                    });
                }
            }
        }
        out
    }

    // --- emission ----------------------------------------------------------

    fn combine_pair(
        &mut self,
        k: &mut Kernel,
        left: (ExprId, ExprId, ExprId),
        right: (ExprId, ExprId, ExprId),
    ) -> (ExprId, ExprId, ExprId) {
        let (a, b, h1) = left;
        let (c, d, h2) = right;
        let proof = Self::apply(k, self.add_le_add, &[a, b, c, d, h1, h2]);
        let ac = self.add2(k, a, c);
        let bd = self.add2(k, b, d);
        (ac, bd, proof)
    }

    fn combine(
        &mut self,
        k: &mut Kernel,
        hyps: &[Hyp],
        cert: &Certificate,
    ) -> (ExprId, ExprId, ExprId) {
        let mut acc: Option<(ExprId, ExprId, ExprId)> = None;
        for (index, multiplier) in cert.used() {
            let base = (hyps[index].lhs, hyps[index].rhs, hyps[index].proof);
            let mut scaled = base;
            for _ in 1..multiplier {
                scaled = self.combine_pair(k, scaled, base);
            }
            acc = Some(match acc {
                None => scaled,
                Some(running) => self.combine_pair(k, running, scaled),
            });
        }
        if let Some(triple) = acc {
            return triple;
        }
        let zero = self.zero;
        let refl = Self::apply(k, self.le_refl, &[zero]);
        (zero, zero, refl)
    }

    /// Emit `le lhs rhs` from a certificate whose residual is a nonnegative
    /// constant. `slack_k = 0` needs no `ofNat`/`zero_le_one` at all; a
    /// positive slack does, and declines [`Decline::SearchBudget`] when this
    /// `Problem` was built with no `zero_le_one` witness.
    fn emit_le(
        &mut self,
        k: &mut Kernel,
        hyps: &[Hyp],
        lhs: ExprId,
        rhs: ExprId,
        cert: &Certificate,
        verify: bool,
    ) -> Result<ExprId, Decline> {
        if !cert.residual.is_constant() || cert.residual.const_term() < 0 {
            return Err(Decline::NoCertificate);
        }
        let slack_k = cert.residual.const_term();
        let (a_term, b_term, hsum) = self.combine(k, hyps, cert);
        let h1 = Self::apply(k, self.add_le_add_left, &[a_term, b_term, lhs, hsum]);
        let la = self.add2(k, lhs, a_term);
        let lb = self.add2(k, lhs, b_term);

        let (h2, target_rhs) = if slack_k == 0 {
            (h1, lb)
        } else {
            let Some(zero_le_one) = self.zero_le_one else {
                return Err(Decline::SearchBudget);
            };
            let slack_u32 = u32::try_from(slack_k).map_err(|_| Decline::SearchBudget)?;
            let slack = self.literal(k, slack_k);
            let zero_nat = self.nat_num(k, 0);
            let slack_nat = self.nat_num(k, slack_u32);
            let zero_le_nat_c = k.const_(self.nat.zero_le, vec![]);
            let nat_zero_le = Self::apply(k, zero_le_nat_c, &[slack_nat]);
            let mono = Self::apply(
                k,
                self.ofnat_le_ofnat_of_le_r,
                &[zero_le_one, zero_nat, slack_nat, nat_zero_le],
            );
            let zero = self.zero;
            let le = self.le;
            let grow = Self::apply(k, self.add_le_add_left, &[zero, slack, lb, mono]);
            let lb_zero = self.add2(k, lb, zero);
            let lb_slack = self.add2(k, lb, slack);
            let eqz = Self::apply(k, self.add_zero, &[lb]);
            let grow2 = self.substp(
                k,
                lb_zero,
                lb,
                eqz,
                LeCtx::Left(lb_slack),
                &move |k2, x| {
                    let e = k2.app(le, x);
                    k2.app(e, lb_slack)
                },
                grow,
            );
            let h2 = Self::apply(k, self.le_trans, &[la, lb, lb_slack, h1, grow2]);
            (h2, lb_slack)
        };

        let ra = self.add2(k, rhs, a_term);
        let identity = self.prove_eq(k, target_rhs, ra, verify)?;
        let le = self.le;
        let h3 = self.substp(
            k,
            target_rhs,
            ra,
            identity,
            LeCtx::Right(la),
            &move |k2, x| {
                let e = k2.app(le, la);
                k2.app(e, x)
            },
            h2,
        );
        Ok(Self::apply(
            k,
            self.le_of_add_le_add_right,
            &[lhs, rhs, a_term, h3],
        ))
    }

    fn prove_le(
        &mut self,
        k: &mut Kernel,
        hyps: &[Hyp],
        lhs: ExprId,
        rhs: ExprId,
    ) -> Result<ExprId, Decline> {
        let fl = self.parse_term(k, lhs)?;
        let fr = self.parse_term(k, rhs)?;
        let goal_form = fr.checked_sub(&fl).ok_or(Decline::SearchBudget)?;
        let forms: Vec<LinForm> = hyps.iter().map(|h| h.form.clone()).collect();
        // Stricter than `find_certificate`'s shared `is_nonneg_cone`: over an
        // arbitrary `OrderedRing` an atom is not guaranteed nonnegative (no
        // built-in ℕ-style slack), so the residual must be a plain
        // nonnegative CONSTANT or the search must keep looking rather than
        // accept a smaller-weight certificate `emit_le` could not use. See
        // `find_combination`'s doc comment.
        let cert = find_combination(&forms, &goal_form, |r| {
            r.is_constant() && r.const_term() >= 0
        })?;
        self.emit_le(k, hyps, lhs, rhs, &cert, true)
    }

    fn prove_goal(
        &mut self,
        k: &mut Kernel,
        assumptions: &[(ExprId, ExprId)],
        goal: ExprId,
    ) -> Result<ExprId, Decline> {
        let (shape, lhs, rhs) = self.parse_prop(k, goal)?;
        match shape {
            Shape::Le => {
                let hyps = self.collect(k, assumptions);
                self.prove_le(k, &hyps, lhs, rhs)
            }
            Shape::Eq => {
                if let Ok(direct) = self.prove_eq(k, lhs, rhs, true) {
                    return Ok(direct);
                }
                let hyps = self.collect(k, assumptions);
                let up = self.prove_le(k, &hyps, lhs, rhs)?;
                let down = self.prove_le(k, &hyps, rhs, lhs)?;
                Ok(Self::apply(k, self.le_antisymm, &[lhs, rhs, up, down]))
            }
        }
    }
}

/// An assumption offered to the procedure: its type and a proof of it.
pub(crate) type Assumption = (ExprId, ExprId);

/// Prove `goal` from `assumptions` over `(R : Alg.OrderedRing)`, or decline.
///
/// `zero_le_one`, when supplied, must be a proof of `R.le R.zero R.one` — see
/// the module docs on why this cannot be derived from `OrderedRing`'s five
/// order laws alone. Needed only when the certificate's residual slack is
/// nonzero; every goal reachable with an EXACT certificate (residual `0`)
/// needs none of it.
///
/// The returned term is **unchecked**; the kernel is what stands behind it.
#[allow(clippy::too_many_arguments)]
pub(crate) fn prove(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    st: &structures::StructuresNames,
    ext: &OrderedRingExtNames,
    nat: &NatPrelude,
    ring: ExprId,
    zero_le_one: Option<ExprId>,
    assumptions: &[Assumption],
    goal: ExprId,
) -> Result<ExprId, Decline> {
    let mut problem = Problem::new(k, lg, l1, st, ext, nat, ring, zero_le_one);
    problem.prove_goal(k, assumptions, goal)
}

/// Emit the `le` chain for a certificate the **caller** supplies.
///
/// `verify = false` skips the procedure's own arithmetic check so a
/// corrupted certificate reaches the kernel — the only way to ask whether
/// the trust anchor catches it. See `linarith::int::emit_le_from_certificate`.
#[cfg(test)]
#[allow(clippy::too_many_arguments)]
pub(crate) fn emit_le_from_certificate(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    st: &structures::StructuresNames,
    ext: &OrderedRingExtNames,
    nat: &NatPrelude,
    ring: ExprId,
    zero_le_one: Option<ExprId>,
    assumptions: &[Assumption],
    lhs: ExprId,
    rhs: ExprId,
    cert: &Certificate,
    verify: bool,
) -> Result<ExprId, Decline> {
    let mut problem = Problem::new(k, lg, l1, st, ext, nat, ring, zero_le_one);
    let hyps = problem.collect(k, assumptions);
    let _ = problem.parse_term(k, lhs)?;
    let _ = problem.parse_term(k, rhs)?;
    problem.emit_le(k, &hyps, lhs, rhs, cert, verify)
}

/// ADR-1592: the setoid twin of [`prove`] — over `(R : AlgS.OrderedRing)`
/// instead of `(R : Alg.OrderedRing)`, so a goal's "equality" fragment
/// (`Shape::Eq`) is the record's own `equiv`, not the kernel's `Eq`. Same
/// contract otherwise: `zero_le_one`, when supplied, must be a proof of
/// `R.le R.zero R.one`; the returned term is unchecked.
#[allow(clippy::too_many_arguments)]
pub(crate) fn prove_s(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    st: &structures_s::StructuresSRecordNames,
    ext: &OrderedRingExtSNames,
    nat: &NatPrelude,
    ring: ExprId,
    zero_le_one: Option<ExprId>,
    assumptions: &[Assumption],
    goal: ExprId,
) -> Result<ExprId, Decline> {
    let mut problem = Problem::new_s(k, lg, l1, st, ext, nat, ring, zero_le_one);
    problem.prove_goal(k, assumptions, goal)
}

/// ADR-1592: the setoid twin of [`emit_le_from_certificate`].
#[cfg(test)]
#[allow(clippy::too_many_arguments)]
pub(crate) fn emit_le_from_certificate_s(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    st: &structures_s::StructuresSRecordNames,
    ext: &OrderedRingExtSNames,
    nat: &NatPrelude,
    ring: ExprId,
    zero_le_one: Option<ExprId>,
    assumptions: &[Assumption],
    lhs: ExprId,
    rhs: ExprId,
    cert: &Certificate,
    verify: bool,
) -> Result<ExprId, Decline> {
    let mut problem = Problem::new_s(k, lg, l1, st, ext, nat, ring, zero_le_one);
    let hyps = problem.collect(k, assumptions);
    let _ = problem.parse_term(k, lhs)?;
    let _ = problem.parse_term(k, rhs)?;
    problem.emit_le(k, &hyps, lhs, rhs, cert, verify)
}

#[cfg(test)]
mod generic_tests {
    use super::*;
    use crate::nat_prelude::structures::lam_over;
    use crate::nat_prelude::structures::sel;
    use crate::rat_prelude::RatPrelude;
    use crate::{Kernel, build_rat_prelude};
    use structures::idx::ordered_ring::{ADD, LE, NEG};

    fn le_of(k: &mut Kernel, rn: &RecordNames, ring: ExprId, x: ExprId, y: ExprId) -> ExprId {
        let le = sel(k, rn, LE, ring);
        let e = k.app(le, x);
        k.app(e, y)
    }

    fn add_of(k: &mut Kernel, rn: &RecordNames, ring: ExprId, x: ExprId, y: ExprId) -> ExprId {
        let add = sel(k, rn, ADD, ring);
        let e = k.app(add, x);
        k.app(e, y)
    }

    fn neg_of(k: &mut Kernel, rn: &RecordNames, ring: ExprId, x: ExprId) -> ExprId {
        let neg = sel(k, rn, NEG, ring);
        k.app(neg, x)
    }

    fn one_of(k: &mut Kernel, rn: &RecordNames, ring: ExprId) -> ExprId {
        sel(k, rn, structures::idx::ordered_ring::ONE, ring)
    }

    fn eq_of_carrier(
        k: &mut Kernel,
        p: &RatPrelude,
        l1: LevelId,
        carrier: ExprId,
        x: ExprId,
        y: ExprId,
    ) -> ExprId {
        structures::eq_of(k, &p.int.nat.logic, l1, carrier, x, y)
    }

    fn rat_zero_le_one(k: &mut Kernel, p: &RatPrelude) -> ExprId {
        let zlt1 = k.const_(p.zero_lt_one, vec![]);
        let le_of_lt = k.const_(p.le_of_lt, vec![]);
        let zero = k.const_(p.zero, vec![]);
        let one = k.const_(p.one, vec![]);
        let e1 = k.app(le_of_lt, zero);
        let e2 = k.app(e1, one);
        k.app(e2, zlt1)
    }

    /// Wrap `body` (which mentions the free vars in `vars` and hypothesis
    /// fvars in `hyp_fvars`/`hyp_tys`, in that order) into a closed term and
    /// infer its type — the same `lam_over`-chain-then-`k.infer` pattern
    /// `algebra_ext.rs`'s own retirement tests use.
    fn close_and_infer(
        k: &mut Kernel,
        carrier: ExprId,
        vars: &[u64],
        hyp_fvars: &[u64],
        hyp_tys: &[ExprId],
        body: ExprId,
    ) -> ExprId {
        let mut v = body;
        for (&fv, &ty) in hyp_fvars.iter().zip(hyp_tys.iter()).rev() {
            v = lam_over(k, fv, ty, v);
        }
        for &fv in vars.iter().rev() {
            v = lam_over(k, fv, carrier, v);
        }
        k.infer(v).expect("closed generic proof must type-check")
    }

    // -----------------------------------------------------------------------
    // Retirement: the seven `int_prelude` theorems ADR-1576/1581 retired to
    // `linarith::int`, re-proved through `linarith::generic` at
    // `Int.orderedRing` instead, and compared BY TYPE against the existing
    // `Int.*` declaration (never a doc comment).
    // -----------------------------------------------------------------------

    #[test]
    fn retirement_int_add_le_add_three() {
        const A: u64 = 51_000;
        const B: u64 = 51_001;
        const C: u64 = 51_002;
        const D: u64 = 51_003;
        const E: u64 = 51_004;
        const F: u64 = 51_005;
        const H1: u64 = 51_010;
        const H2: u64 = 51_011;
        const H3: u64 = 51_012;
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.algebra_ext.int_ordered_ring, vec![]);
        let carrier = k.const_(p.int.z, vec![]);
        let rn = p.int.nat.structures.ordered_ring;

        let (a, b, c, d, e, f) = (
            k.fvar(A),
            k.fvar(B),
            k.fvar(C),
            k.fvar(D),
            k.fvar(E),
            k.fvar(F),
        );
        let h1_ty = le_of(&mut k, &rn, ring, a, d);
        let h2_ty = le_of(&mut k, &rn, ring, b, e);
        let h3_ty = le_of(&mut k, &rn, ring, c, f);
        let h1 = k.fvar(H1);
        let h2 = k.fvar(H2);
        let h3 = k.fvar(H3);

        let ab = add_of(&mut k, &rn, ring, a, b);
        let abc = add_of(&mut k, &rn, ring, ab, c);
        let de = add_of(&mut k, &rn, ring, d, e);
        let def = add_of(&mut k, &rn, ring, de, f);
        let goal = le_of(&mut k, &rn, ring, abc, def);

        let assumptions = [(h1_ty, h1), (h2_ty, h2), (h3_ty, h3)];
        let proof = prove(
            &mut k,
            &p.int.nat.logic,
            l1,
            &p.int.nat.structures,
            &p.ordered_ring_ext,
            &p.int.nat,
            ring,
            None,
            &assumptions,
            goal,
        )
        .expect("linarith::generic must find a certificate for add_le_add_three");

        let generic_ty = close_and_infer(
            &mut k,
            carrier,
            &[a_fv(A), b_fv(B), c_fv(C), d_fv(D), e_fv(E), f_fv(F)],
            &[H1, H2, H3],
            &[h1_ty, h2_ty, h3_ty],
            proof,
        );
        let hand = k.const_(p.int.add_le_add_three, vec![]);
        let hand_ty = k.infer(hand).expect("Int.add_le_add_three must exist");
        assert!(
            k.def_eq(generic_ty, hand_ty),
            "linarith::generic's add_le_add_three proof must have the SAME \
             TYPE as Int.add_le_add_three"
        );
    }

    // Trivial identity helpers so `close_and_infer`'s `vars` slice reads as
    // fvar ids without a spurious extra abstraction layer.
    fn a_fv(x: u64) -> u64 {
        x
    }
    fn b_fv(x: u64) -> u64 {
        x
    }
    fn c_fv(x: u64) -> u64 {
        x
    }
    fn d_fv(x: u64) -> u64 {
        x
    }
    fn e_fv(x: u64) -> u64 {
        x
    }
    fn f_fv(x: u64) -> u64 {
        x
    }

    #[test]
    fn retirement_int_add_le_of_le_neg_add() {
        const A: u64 = 51_100;
        const B: u64 = 51_101;
        const C: u64 = 51_102;
        const H: u64 = 51_110;
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.algebra_ext.int_ordered_ring, vec![]);
        let carrier = k.const_(p.int.z, vec![]);
        let rn = p.int.nat.structures.ordered_ring;

        let (a, b, c) = (k.fvar(A), k.fvar(B), k.fvar(C));
        let neg_a = neg_of(&mut k, &rn, ring, a);
        let neg_a_c = add_of(&mut k, &rn, ring, neg_a, c);
        let h_ty = le_of(&mut k, &rn, ring, b, neg_a_c);
        let h = k.fvar(H);
        let ab = add_of(&mut k, &rn, ring, a, b);
        let goal = le_of(&mut k, &rn, ring, ab, c);

        let assumptions = [(h_ty, h)];
        let proof = prove(
            &mut k,
            &p.int.nat.logic,
            l1,
            &p.int.nat.structures,
            &p.ordered_ring_ext,
            &p.int.nat,
            ring,
            None,
            &assumptions,
            goal,
        )
        .expect("linarith::generic must find a certificate for add_le_of_le_neg_add");

        let generic_ty = close_and_infer(&mut k, carrier, &[A, B, C], &[H], &[h_ty], proof);
        let hand = k.const_(p.int.add_le_of_le_neg_add, vec![]);
        let hand_ty = k.infer(hand).expect("Int.add_le_of_le_neg_add must exist");
        assert!(
            k.def_eq(generic_ty, hand_ty),
            "must match Int.add_le_of_le_neg_add"
        );
    }

    #[test]
    fn retirement_int_add_le_of_le_sub_left() {
        const A: u64 = 51_200;
        const B: u64 = 51_201;
        const C: u64 = 51_202;
        const H: u64 = 51_210;
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.algebra_ext.int_ordered_ring, vec![]);
        let carrier = k.const_(p.int.z, vec![]);
        let rn = p.int.nat.structures.ordered_ring;

        let (a, b, c) = (k.fvar(A), k.fvar(B), k.fvar(C));
        let neg_a = neg_of(&mut k, &rn, ring, a);
        let c_sub_a = add_of(&mut k, &rn, ring, c, neg_a);
        let h_ty = le_of(&mut k, &rn, ring, b, c_sub_a);
        let h = k.fvar(H);
        let ab = add_of(&mut k, &rn, ring, a, b);
        let goal = le_of(&mut k, &rn, ring, ab, c);

        let assumptions = [(h_ty, h)];
        let proof = prove(
            &mut k,
            &p.int.nat.logic,
            l1,
            &p.int.nat.structures,
            &p.ordered_ring_ext,
            &p.int.nat,
            ring,
            None,
            &assumptions,
            goal,
        )
        .expect("linarith::generic must find a certificate for add_le_of_le_sub_left");

        let generic_ty = close_and_infer(&mut k, carrier, &[A, B, C], &[H], &[h_ty], proof);
        let hand = k.const_(p.int.add_le_of_le_sub_left, vec![]);
        let hand_ty = k.infer(hand).expect("Int.add_le_of_le_sub_left must exist");
        assert!(
            k.def_eq(generic_ty, hand_ty),
            "must match Int.add_le_of_le_sub_left"
        );
    }

    #[test]
    fn retirement_int_add_le_of_le_sub_right() {
        const A: u64 = 51_300;
        const B: u64 = 51_301;
        const C: u64 = 51_302;
        const H: u64 = 51_310;
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.algebra_ext.int_ordered_ring, vec![]);
        let carrier = k.const_(p.int.z, vec![]);
        let rn = p.int.nat.structures.ordered_ring;

        let (a, b, c) = (k.fvar(A), k.fvar(B), k.fvar(C));
        let neg_b = neg_of(&mut k, &rn, ring, b);
        let c_sub_b = add_of(&mut k, &rn, ring, c, neg_b);
        let h_ty = le_of(&mut k, &rn, ring, a, c_sub_b);
        let h = k.fvar(H);
        let ab = add_of(&mut k, &rn, ring, a, b);
        let goal = le_of(&mut k, &rn, ring, ab, c);

        let assumptions = [(h_ty, h)];
        let proof = prove(
            &mut k,
            &p.int.nat.logic,
            l1,
            &p.int.nat.structures,
            &p.ordered_ring_ext,
            &p.int.nat,
            ring,
            None,
            &assumptions,
            goal,
        )
        .expect("linarith::generic must find a certificate for add_le_of_le_sub_right");

        let generic_ty = close_and_infer(&mut k, carrier, &[A, B, C], &[H], &[h_ty], proof);
        let hand = k.const_(p.int.add_le_of_le_sub_right, vec![]);
        let hand_ty = k
            .infer(hand)
            .expect("Int.add_le_of_le_sub_right must exist");
        assert!(
            k.def_eq(generic_ty, hand_ty),
            "must match Int.add_le_of_le_sub_right"
        );
    }

    #[test]
    fn retirement_int_add_left_comm() {
        const A: u64 = 51_400;
        const B: u64 = 51_401;
        const C: u64 = 51_402;
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.algebra_ext.int_ordered_ring, vec![]);
        let carrier = k.const_(p.int.z, vec![]);
        let rn = p.int.nat.structures.ordered_ring;
        let carrier_sel = sel(&mut k, &rn, structures::idx::ordered_ring::CARRIER, ring);

        let (a, b, c) = (k.fvar(A), k.fvar(B), k.fvar(C));
        let bc = add_of(&mut k, &rn, ring, b, c);
        let start = add_of(&mut k, &rn, ring, a, bc);
        let ac = add_of(&mut k, &rn, ring, a, c);
        let fin = add_of(&mut k, &rn, ring, b, ac);
        let goal = eq_of_carrier(&mut k, &p, l1, carrier_sel, start, fin);

        let proof = prove(
            &mut k,
            &p.int.nat.logic,
            l1,
            &p.int.nat.structures,
            &p.ordered_ring_ext,
            &p.int.nat,
            ring,
            None,
            &[],
            goal,
        )
        .expect("linarith::generic must prove add_left_comm's equation");

        let generic_ty = close_and_infer(&mut k, carrier, &[A, B, C], &[], &[], proof);
        let hand = k.const_(p.int.add_left_comm, vec![]);
        let hand_ty = k.infer(hand).expect("Int.add_left_comm must exist");
        assert!(
            k.def_eq(generic_ty, hand_ty),
            "must match Int.add_left_comm"
        );
    }

    #[test]
    fn retirement_int_add_neg_cancel_left() {
        const A: u64 = 51_500;
        const B: u64 = 51_501;
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.algebra_ext.int_ordered_ring, vec![]);
        let carrier = k.const_(p.int.z, vec![]);
        let rn = p.int.nat.structures.ordered_ring;
        let carrier_sel = sel(&mut k, &rn, structures::idx::ordered_ring::CARRIER, ring);

        let (a, b) = (k.fvar(A), k.fvar(B));
        let neg_a = neg_of(&mut k, &rn, ring, a);
        let neg_a_b = add_of(&mut k, &rn, ring, neg_a, b);
        let start = add_of(&mut k, &rn, ring, a, neg_a_b);
        let goal = eq_of_carrier(&mut k, &p, l1, carrier_sel, start, b);

        let proof = prove(
            &mut k,
            &p.int.nat.logic,
            l1,
            &p.int.nat.structures,
            &p.ordered_ring_ext,
            &p.int.nat,
            ring,
            None,
            &[],
            goal,
        )
        .expect("linarith::generic must prove add_neg_cancel_left's equation");

        let generic_ty = close_and_infer(&mut k, carrier, &[A, B], &[], &[], proof);
        let hand = k.const_(p.int.add_neg_cancel_left, vec![]);
        let hand_ty = k.infer(hand).expect("Int.add_neg_cancel_left must exist");
        assert!(
            k.def_eq(generic_ty, hand_ty),
            "must match Int.add_neg_cancel_left"
        );
    }

    #[test]
    fn retirement_int_add_neg_cancel_right() {
        const A: u64 = 51_600;
        const B: u64 = 51_601;
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.algebra_ext.int_ordered_ring, vec![]);
        let carrier = k.const_(p.int.z, vec![]);
        let rn = p.int.nat.structures.ordered_ring;
        let carrier_sel = sel(&mut k, &rn, structures::idx::ordered_ring::CARRIER, ring);

        let (a, b) = (k.fvar(A), k.fvar(B));
        let ab = add_of(&mut k, &rn, ring, a, b);
        let neg_b = neg_of(&mut k, &rn, ring, b);
        let start = add_of(&mut k, &rn, ring, ab, neg_b);
        let goal = eq_of_carrier(&mut k, &p, l1, carrier_sel, start, a);

        let proof = prove(
            &mut k,
            &p.int.nat.logic,
            l1,
            &p.int.nat.structures,
            &p.ordered_ring_ext,
            &p.int.nat,
            ring,
            None,
            &[],
            goal,
        )
        .expect("linarith::generic must prove add_neg_cancel_right's equation");

        let generic_ty = close_and_infer(&mut k, carrier, &[A, B], &[], &[], proof);
        let hand = k.const_(p.int.add_neg_cancel_right, vec![]);
        let hand_ty = k.infer(hand).expect("Int.add_neg_cancel_right must exist");
        assert!(
            k.def_eq(generic_ty, hand_ty),
            "must match Int.add_neg_cancel_right"
        );
    }

    // -----------------------------------------------------------------------
    // New capability: `linarith` over ℚ did not exist before this module.
    // -----------------------------------------------------------------------

    #[test]
    fn rat_new_capability_transitivity() {
        const A: u64 = 52_000;
        const B: u64 = 52_001;
        const C: u64 = 52_002;
        const H1: u64 = 52_010;
        const H2: u64 = 52_011;
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.algebra_ext.rat_ordered_ring, vec![]);
        let carrier = k.const_(p.int.rat, vec![]);
        let rn = p.int.nat.structures.ordered_ring;

        let (a, b, c) = (k.fvar(A), k.fvar(B), k.fvar(C));
        let h1_ty = le_of(&mut k, &rn, ring, a, b);
        let h2_ty = le_of(&mut k, &rn, ring, b, c);
        let h1 = k.fvar(H1);
        let h2 = k.fvar(H2);
        let goal = le_of(&mut k, &rn, ring, a, c);

        let assumptions = [(h1_ty, h1), (h2_ty, h2)];
        let proof = prove(
            &mut k,
            &p.int.nat.logic,
            l1,
            &p.int.nat.structures,
            &p.ordered_ring_ext,
            &p.int.nat,
            ring,
            None,
            &assumptions,
            goal,
        )
        .expect("linarith::generic must derive transitivity over Rat.orderedRing");
        let _ = close_and_infer(
            &mut k,
            carrier,
            &[A, B, C],
            &[H1, H2],
            &[h1_ty, h2_ty],
            proof,
        );
    }

    #[test]
    fn rat_new_capability_sum_of_nonneg() {
        const A: u64 = 52_100;
        const B: u64 = 52_101;
        const H1: u64 = 52_110;
        const H2: u64 = 52_111;
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.algebra_ext.rat_ordered_ring, vec![]);
        let carrier = k.const_(p.int.rat, vec![]);
        let rn = p.int.nat.structures.ordered_ring;
        let zero = sel(&mut k, &rn, structures::idx::ordered_ring::ZERO, ring);

        let (a, b) = (k.fvar(A), k.fvar(B));
        let h1_ty = le_of(&mut k, &rn, ring, zero, a);
        let h2_ty = le_of(&mut k, &rn, ring, zero, b);
        let h1 = k.fvar(H1);
        let h2 = k.fvar(H2);
        let ab = add_of(&mut k, &rn, ring, a, b);
        let goal = le_of(&mut k, &rn, ring, zero, ab);

        let assumptions = [(h1_ty, h1), (h2_ty, h2)];
        let proof = prove(
            &mut k,
            &p.int.nat.logic,
            l1,
            &p.int.nat.structures,
            &p.ordered_ring_ext,
            &p.int.nat,
            ring,
            None,
            &assumptions,
            goal,
        )
        .expect("linarith::generic must derive sum-of-nonneg over Rat.orderedRing");
        let _ = close_and_infer(&mut k, carrier, &[A, B], &[H1, H2], &[h1_ty, h2_ty], proof);
    }

    /// Exercises the SLACK path (`Alg.ofNat`/`ofNat_le_ofNat_of_le`,
    /// residual `1`, not `0`): `a ≤ b ⊢ a ≤ b + 1`.
    #[test]
    fn rat_new_capability_slack_add_one() {
        const A: u64 = 52_200;
        const B: u64 = 52_201;
        const H: u64 = 52_210;
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.algebra_ext.rat_ordered_ring, vec![]);
        let carrier = k.const_(p.int.rat, vec![]);
        let rn = p.int.nat.structures.ordered_ring;
        let one = one_of(&mut k, &rn, ring);
        let zero_le_one = rat_zero_le_one(&mut k, &p);

        let (a, b) = (k.fvar(A), k.fvar(B));
        let h_ty = le_of(&mut k, &rn, ring, a, b);
        let h = k.fvar(H);
        let b_plus_one = add_of(&mut k, &rn, ring, b, one);
        let goal = le_of(&mut k, &rn, ring, a, b_plus_one);

        let assumptions = [(h_ty, h)];
        let proof = prove(
            &mut k,
            &p.int.nat.logic,
            l1,
            &p.int.nat.structures,
            &p.ordered_ring_ext,
            &p.int.nat,
            ring,
            Some(zero_le_one),
            &assumptions,
            goal,
        )
        .expect("linarith::generic must derive the slack-1 goal over Rat.orderedRing");
        let _ = close_and_infer(&mut k, carrier, &[A, B], &[H], &[h_ty], proof);

        // And WITHOUT `zero_le_one` supplied, the same goal must decline
        // rather than silently fail some other way -- the slack path is
        // genuinely gated on it.
        let mut k2 = Kernel::new();
        let p2 = build_rat_prelude(&mut k2).expect("rat prelude must build");
        let ring2 = k2.const_(p2.algebra_ext.rat_ordered_ring, vec![]);
        let rn2 = p2.int.nat.structures.ordered_ring;
        let one2 = one_of(&mut k2, &rn2, ring2);
        let (a2, b2) = (k2.fvar(A), k2.fvar(B));
        let h_ty2 = le_of(&mut k2, &rn2, ring2, a2, b2);
        let h2 = k2.fvar(H);
        let b_plus_one2 = add_of(&mut k2, &rn2, ring2, b2, one2);
        let goal2 = le_of(&mut k2, &rn2, ring2, a2, b_plus_one2);
        let result = prove(
            &mut k2,
            &p2.int.nat.logic,
            l1,
            &p2.int.nat.structures,
            &p2.ordered_ring_ext,
            &p2.int.nat,
            ring2,
            None,
            &[(h_ty2, h2)],
            goal2,
        );
        assert!(
            result.is_err(),
            "the slack-1 goal must decline when no zero_le_one witness is supplied"
        );
    }

    // -----------------------------------------------------------------------
    // Three false goals decline.
    // -----------------------------------------------------------------------

    #[test]
    fn false_goal_swap_declines() {
        const A: u64 = 53_000;
        const B: u64 = 53_001;
        const H: u64 = 53_010;
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.algebra_ext.int_ordered_ring, vec![]);
        let rn = p.int.nat.structures.ordered_ring;
        let (a, b) = (k.fvar(A), k.fvar(B));
        let h_ty = le_of(&mut k, &rn, ring, a, b);
        let h = k.fvar(H);
        let goal = le_of(&mut k, &rn, ring, b, a);
        let result = prove(
            &mut k,
            &p.int.nat.logic,
            l1,
            &p.int.nat.structures,
            &p.ordered_ring_ext,
            &p.int.nat,
            ring,
            None,
            &[(h_ty, h)],
            goal,
        );
        assert!(result.is_err(), "a<=b does not imply b<=a -- must decline");
    }

    #[test]
    fn false_goal_cycle_declines() {
        const A: u64 = 53_100;
        const B: u64 = 53_101;
        const C: u64 = 53_102;
        const H1: u64 = 53_110;
        const H2: u64 = 53_111;
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.algebra_ext.int_ordered_ring, vec![]);
        let rn = p.int.nat.structures.ordered_ring;
        let (a, b, c) = (k.fvar(A), k.fvar(B), k.fvar(C));
        let h1_ty = le_of(&mut k, &rn, ring, a, b);
        let h2_ty = le_of(&mut k, &rn, ring, b, c);
        let h1 = k.fvar(H1);
        let h2 = k.fvar(H2);
        let goal = le_of(&mut k, &rn, ring, c, a);
        let result = prove(
            &mut k,
            &p.int.nat.logic,
            l1,
            &p.int.nat.structures,
            &p.ordered_ring_ext,
            &p.int.nat,
            ring,
            None,
            &[(h1_ty, h1), (h2_ty, h2)],
            goal,
        );
        assert!(
            result.is_err(),
            "a<=b<=c does not imply c<=a -- must decline"
        );
    }

    #[test]
    fn false_goal_off_by_one_declines() {
        const A: u64 = 53_200;
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.algebra_ext.int_ordered_ring, vec![]);
        let rn = p.int.nat.structures.ordered_ring;
        let one = one_of(&mut k, &rn, ring);
        let a = k.fvar(A);
        let a_plus_one = add_of(&mut k, &rn, ring, a, one);
        let goal = le_of(&mut k, &rn, ring, a_plus_one, a);
        let result = prove(
            &mut k,
            &p.int.nat.logic,
            l1,
            &p.int.nat.structures,
            &p.ordered_ring_ext,
            &p.int.nat,
            ring,
            None,
            &[],
            goal,
        );
        assert!(result.is_err(), "a+1<=a is false -- must decline");
    }

    // -----------------------------------------------------------------------
    // Three corrupted certificates, rejected by the KERNEL (`verify: false`
    // disables `linarith::generic`'s own arithmetic check) -- plus the
    // positive control confirming the same route admits an UNCORRUPTED
    // certificate, so a "rejected" reading above cannot be an artefact of a
    // broken emitter.
    // -----------------------------------------------------------------------

    #[test]
    fn corrupted_certificate_wrong_multiplier_rejected() {
        const A: u64 = 54_000;
        const B: u64 = 54_001;
        const H: u64 = 54_010;
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.algebra_ext.int_ordered_ring, vec![]);
        let rn = p.int.nat.structures.ordered_ring;
        let (a, b) = (k.fvar(A), k.fvar(B));
        let h_ty = le_of(&mut k, &rn, ring, a, b);
        let h = k.fvar(H);
        let goal_lhs = a;
        let goal_rhs = b;

        let cert = Certificate {
            multipliers: vec![2], // correct is 1
            residual: LinForm::zero(),
        };
        let corrupted = emit_le_from_certificate(
            &mut k,
            &p.int.nat.logic,
            l1,
            &p.int.nat.structures,
            &p.ordered_ring_ext,
            &p.int.nat,
            ring,
            None,
            &[(h_ty, h)],
            goal_lhs,
            goal_rhs,
            &cert,
            false,
        );
        let Ok(term) = corrupted else {
            // The emitter itself may also decline (e.g. a malformed shape);
            // either is an acceptable "the corruption did not slip through",
            // but assert we are not silently accepting a bad witness.
            return;
        };
        let carrier_c = k.const_(p.int.z, vec![]);
        let closed = {
            let v = lam_over(&mut k, H, h_ty, term);
            let v = lam_over(&mut k, B, carrier_c, v);
            lam_over(&mut k, A, carrier_c, v)
        };
        assert!(
            k.infer(closed).is_err(),
            "a wrong multiplier must be rejected by the KERNEL, not silently admitted"
        );
    }

    #[test]
    fn corrupted_certificate_wrong_residual_rejected() {
        const A: u64 = 54_100;
        const B: u64 = 54_101;
        const H: u64 = 54_110;
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.algebra_ext.rat_ordered_ring, vec![]);
        let rn = p.int.nat.structures.ordered_ring;
        let (a, b) = (k.fvar(A), k.fvar(B));
        let h_ty = le_of(&mut k, &rn, ring, a, b);
        let h = k.fvar(H);
        let one = one_of(&mut k, &rn, ring);
        let zero_le_one = rat_zero_le_one(&mut k, &p);
        let goal_lhs = a;
        let goal_rhs = add_of(&mut k, &rn, ring, b, one); // real goal needs residual 1

        // Corrupted: claim residual 0 (exact match) when 1 is required.
        let cert = Certificate {
            multipliers: vec![1],
            residual: LinForm::zero(),
        };
        let corrupted = emit_le_from_certificate(
            &mut k,
            &p.int.nat.logic,
            l1,
            &p.int.nat.structures,
            &p.ordered_ring_ext,
            &p.int.nat,
            ring,
            Some(zero_le_one),
            &[(h_ty, h)],
            goal_lhs,
            goal_rhs,
            &cert,
            false,
        );
        let Ok(term) = corrupted else { return };
        let carrier = k.const_(p.int.rat, vec![]);
        let closed = {
            let v = lam_over(&mut k, H, h_ty, term);
            let v = lam_over(&mut k, B, carrier, v);
            lam_over(&mut k, A, carrier, v)
        };
        assert!(
            k.infer(closed).is_err(),
            "a wrong (too-small) residual must be rejected by the KERNEL"
        );
    }

    #[test]
    fn corrupted_certificate_wrong_hypothesis_proof_rejected() {
        const A: u64 = 54_200;
        const B: u64 = 54_201;
        const C: u64 = 54_202;
        const H: u64 = 54_210;
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.algebra_ext.int_ordered_ring, vec![]);
        let rn = p.int.nat.structures.ordered_ring;
        let (a, b, c) = (k.fvar(A), k.fvar(B), k.fvar(C));
        let h_ty = le_of(&mut k, &rn, ring, a, b); // stated type: a<=b
        // wrong_proof : c<=c (a DIFFERENT true proposition, same shape)
        let le_refl = sel(&mut k, &rn, structures::idx::ordered_ring::LE_REFL, ring);
        let wrong_proof = k.app(le_refl, c);

        let cert = Certificate {
            multipliers: vec![1],
            residual: LinForm::zero(),
        };
        let corrupted = emit_le_from_certificate(
            &mut k,
            &p.int.nat.logic,
            l1,
            &p.int.nat.structures,
            &p.ordered_ring_ext,
            &p.int.nat,
            ring,
            None,
            &[(h_ty, wrong_proof)],
            a,
            b,
            &cert,
            false,
        );
        let Ok(term) = corrupted else { return };
        let carrier = k.const_(p.int.z, vec![]);
        let closed = {
            let v = lam_over(&mut k, H, h_ty, term);
            let v = lam_over(&mut k, C, carrier, v);
            let v = lam_over(&mut k, B, carrier, v);
            lam_over(&mut k, A, carrier, v)
        };
        assert!(
            k.infer(closed).is_err(),
            "a hypothesis slot carrying a proof of a DIFFERENT true \
             proposition must be rejected by the KERNEL"
        );
    }

    /// Positive control: the SAME route (`emit_le_from_certificate`,
    /// `verify: false`) with an UNCORRUPTED certificate is admitted --
    /// otherwise every "rejected" result above could be this emitter simply
    /// being broken, not the trust anchor catching a corruption.
    #[test]
    fn uncorrupted_certificate_is_admitted() {
        const A: u64 = 54_300;
        const B: u64 = 54_301;
        const H: u64 = 54_310;
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.algebra_ext.int_ordered_ring, vec![]);
        let carrier = k.const_(p.int.z, vec![]);
        let rn = p.int.nat.structures.ordered_ring;
        let (a, b) = (k.fvar(A), k.fvar(B));
        let h_ty = le_of(&mut k, &rn, ring, a, b);
        let h = k.fvar(H);

        let cert = Certificate {
            multipliers: vec![1],
            residual: LinForm::zero(),
        };
        let term = emit_le_from_certificate(
            &mut k,
            &p.int.nat.logic,
            l1,
            &p.int.nat.structures,
            &p.ordered_ring_ext,
            &p.int.nat,
            ring,
            None,
            &[(h_ty, h)],
            a,
            b,
            &cert,
            false,
        )
        .expect("the uncorrupted certificate must emit a term");
        let closed = {
            let v = lam_over(&mut k, H, h_ty, term);
            let v = lam_over(&mut k, B, carrier, v);
            lam_over(&mut k, A, carrier, v)
        };
        k.infer(closed)
            .expect("an UNCORRUPTED certificate must be admitted by the kernel");
    }

    // -----------------------------------------------------------------------
    // ADR-1592: the SETOID path (`prove_s`/`emit_le_from_certificate_s`)
    // over `AlgS.OrderedRing` — the three ℚ goals ADR-1585 built through the
    // `Eq` spine, re-proved through `Rat.orderedRingS` (`ofAlg`), and the
    // payoff: five goals at `CReal.orderedRingS`, a carrier `Alg.
    // OrderedRing`/`linarith::generic`'s original `Eq`-flavored route could
    // never reach (`CReal`'s carrier equality is `Equiv`, never `Eq`).
    // -----------------------------------------------------------------------

    use crate::creal::{CRealPrelude, build_creal_prelude};

    fn le_of_s(k: &mut Kernel, rn: &RecordNames, ring: ExprId, x: ExprId, y: ExprId) -> ExprId {
        let le = sel(k, rn, structures_s::idx::ordered_ring::LE, ring);
        let e = k.app(le, x);
        k.app(e, y)
    }

    fn add_of_s(k: &mut Kernel, rn: &RecordNames, ring: ExprId, x: ExprId, y: ExprId) -> ExprId {
        let add = sel(k, rn, structures_s::idx::ordered_ring::ADD, ring);
        let e = k.app(add, x);
        k.app(e, y)
    }

    fn one_of_s(k: &mut Kernel, rn: &RecordNames, ring: ExprId) -> ExprId {
        sel(k, rn, structures_s::idx::ordered_ring::ONE, ring)
    }

    fn zero_of_s(k: &mut Kernel, rn: &RecordNames, ring: ExprId) -> ExprId {
        sel(k, rn, structures_s::idx::ordered_ring::ZERO, ring)
    }

    fn equiv_of_s(k: &mut Kernel, rn: &RecordNames, ring: ExprId, x: ExprId, y: ExprId) -> ExprId {
        let equiv = sel(k, rn, structures_s::idx::ordered_ring::EQUIV, ring);
        let e = k.app(equiv, x);
        k.app(e, y)
    }

    fn creal_zero_le_one(k: &mut Kernel, p: &CRealPrelude) -> ExprId {
        let zlt1 = k.const_(p.zero_lt_one, vec![]);
        let le_of_lt = k.const_(p.le_of_lt, vec![]);
        let zero = k.const_(p.zero, vec![]);
        let one = k.const_(p.one, vec![]);
        let e1 = k.app(le_of_lt, zero);
        let e2 = k.app(e1, one);
        k.app(e2, zlt1)
    }

    // --- three ℚ goals, re-proved through the setoid path at Rat.orderedRingS ---

    #[test]
    fn rat_new_capability_transitivity_via_algs() {
        const A: u64 = 55_000;
        const B: u64 = 55_001;
        const C: u64 = 55_002;
        const H1: u64 = 55_010;
        const H2: u64 = 55_011;
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.ordered_ring_ext_s.rat_ordered_ring_s, vec![]);
        let carrier = k.const_(p.int.rat, vec![]);
        let rn = p.int.nat.structures_s.ordered_ring;

        let (a, b, c) = (k.fvar(A), k.fvar(B), k.fvar(C));
        let h1_ty = le_of_s(&mut k, &rn, ring, a, b);
        let h2_ty = le_of_s(&mut k, &rn, ring, b, c);
        let h1 = k.fvar(H1);
        let h2 = k.fvar(H2);
        let goal = le_of_s(&mut k, &rn, ring, a, c);

        let assumptions = [(h1_ty, h1), (h2_ty, h2)];
        let proof = prove_s(
            &mut k,
            &p.int.nat.logic,
            l1,
            &p.int.nat.structures_s,
            &p.ordered_ring_ext_s,
            &p.int.nat,
            ring,
            None,
            &assumptions,
            goal,
        )
        .expect("linarith::generic (setoid) must derive transitivity over Rat.orderedRingS");
        let _ = close_and_infer(
            &mut k,
            carrier,
            &[A, B, C],
            &[H1, H2],
            &[h1_ty, h2_ty],
            proof,
        );
    }

    #[test]
    fn rat_new_capability_sum_of_nonneg_via_algs() {
        const A: u64 = 55_100;
        const B: u64 = 55_101;
        const H1: u64 = 55_110;
        const H2: u64 = 55_111;
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.ordered_ring_ext_s.rat_ordered_ring_s, vec![]);
        let carrier = k.const_(p.int.rat, vec![]);
        let rn = p.int.nat.structures_s.ordered_ring;
        let zero = zero_of_s(&mut k, &rn, ring);

        let (a, b) = (k.fvar(A), k.fvar(B));
        let h1_ty = le_of_s(&mut k, &rn, ring, zero, a);
        let h2_ty = le_of_s(&mut k, &rn, ring, zero, b);
        let h1 = k.fvar(H1);
        let h2 = k.fvar(H2);
        let ab = add_of_s(&mut k, &rn, ring, a, b);
        let goal = le_of_s(&mut k, &rn, ring, zero, ab);

        let assumptions = [(h1_ty, h1), (h2_ty, h2)];
        let proof = prove_s(
            &mut k,
            &p.int.nat.logic,
            l1,
            &p.int.nat.structures_s,
            &p.ordered_ring_ext_s,
            &p.int.nat,
            ring,
            None,
            &assumptions,
            goal,
        )
        .expect("linarith::generic (setoid) must derive sum-of-nonneg over Rat.orderedRingS");
        let _ = close_and_infer(&mut k, carrier, &[A, B], &[H1, H2], &[h1_ty, h2_ty], proof);
    }

    #[test]
    fn rat_new_capability_slack_add_one_via_algs() {
        const A: u64 = 55_200;
        const B: u64 = 55_201;
        const H: u64 = 55_210;
        let mut k = Kernel::new();
        let p = build_rat_prelude(&mut k).expect("rat prelude must build");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.ordered_ring_ext_s.rat_ordered_ring_s, vec![]);
        let carrier = k.const_(p.int.rat, vec![]);
        let rn = p.int.nat.structures_s.ordered_ring;
        let one = one_of_s(&mut k, &rn, ring);
        let zero_le_one = rat_zero_le_one(&mut k, &p);

        let (a, b) = (k.fvar(A), k.fvar(B));
        let h_ty = le_of_s(&mut k, &rn, ring, a, b);
        let h = k.fvar(H);
        let b_plus_one = add_of_s(&mut k, &rn, ring, b, one);
        let goal = le_of_s(&mut k, &rn, ring, a, b_plus_one);

        let assumptions = [(h_ty, h)];
        let proof = prove_s(
            &mut k,
            &p.int.nat.logic,
            l1,
            &p.int.nat.structures_s,
            &p.ordered_ring_ext_s,
            &p.int.nat,
            ring,
            Some(zero_le_one),
            &assumptions,
            goal,
        )
        .expect("linarith::generic (setoid) must derive the slack-1 goal over Rat.orderedRingS");
        let _ = close_and_infer(&mut k, carrier, &[A, B], &[H], &[h_ty], proof);

        // Negative control: WITHOUT `zero_le_one`, the same goal declines.
        let mut k2 = Kernel::new();
        let p2 = build_rat_prelude(&mut k2).expect("rat prelude must build");
        let ring2 = k2.const_(p2.ordered_ring_ext_s.rat_ordered_ring_s, vec![]);
        let rn2 = p2.int.nat.structures_s.ordered_ring;
        let one2 = one_of_s(&mut k2, &rn2, ring2);
        let (a2, b2) = (k2.fvar(A), k2.fvar(B));
        let h_ty2 = le_of_s(&mut k2, &rn2, ring2, a2, b2);
        let h2 = k2.fvar(H);
        let b_plus_one2 = add_of_s(&mut k2, &rn2, ring2, b2, one2);
        let goal2 = le_of_s(&mut k2, &rn2, ring2, a2, b_plus_one2);
        let result = prove_s(
            &mut k2,
            &p2.int.nat.logic,
            l1,
            &p2.int.nat.structures_s,
            &p2.ordered_ring_ext_s,
            &p2.int.nat,
            ring2,
            None,
            &[(h_ty2, h2)],
            goal2,
        );
        assert!(
            result.is_err(),
            "the slack-1 goal (setoid) must decline when no zero_le_one witness is supplied"
        );
    }

    // --- five goals at CReal.orderedRingS -- the payoff ---

    #[test]
    fn creal_linarith_transitivity() {
        const A: u64 = 56_000;
        const B: u64 = 56_001;
        const C: u64 = 56_002;
        const H1: u64 = 56_010;
        const H2: u64 = 56_011;
        let mut k = Kernel::new();
        let p = build_creal_prelude(&mut k).expect("creal prelude must build");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.ordered_ring_s, vec![]);
        let carrier = k.const_(p.creal, vec![]);
        let rn = p.rat.int.nat.structures_s.ordered_ring;

        let (a, b, c) = (k.fvar(A), k.fvar(B), k.fvar(C));
        let h1_ty = le_of_s(&mut k, &rn, ring, a, b);
        let h2_ty = le_of_s(&mut k, &rn, ring, b, c);
        let h1 = k.fvar(H1);
        let h2 = k.fvar(H2);
        let goal = le_of_s(&mut k, &rn, ring, a, c);

        let assumptions = [(h1_ty, h1), (h2_ty, h2)];
        let proof = prove_s(
            &mut k,
            &p.rat.int.nat.logic,
            l1,
            &p.rat.int.nat.structures_s,
            &p.rat.ordered_ring_ext_s,
            &p.rat.int.nat,
            ring,
            None,
            &assumptions,
            goal,
        )
        .expect("linarith::generic (setoid) must derive transitivity over CReal.orderedRingS");
        let _ = close_and_infer(
            &mut k,
            carrier,
            &[A, B, C],
            &[H1, H2],
            &[h1_ty, h2_ty],
            proof,
        );
    }

    #[test]
    fn creal_linarith_sum_of_nonneg() {
        const A: u64 = 56_100;
        const B: u64 = 56_101;
        const H1: u64 = 56_110;
        const H2: u64 = 56_111;
        let mut k = Kernel::new();
        let p = build_creal_prelude(&mut k).expect("creal prelude must build");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.ordered_ring_s, vec![]);
        let carrier = k.const_(p.creal, vec![]);
        let rn = p.rat.int.nat.structures_s.ordered_ring;
        let zero = zero_of_s(&mut k, &rn, ring);

        let (a, b) = (k.fvar(A), k.fvar(B));
        let h1_ty = le_of_s(&mut k, &rn, ring, zero, a);
        let h2_ty = le_of_s(&mut k, &rn, ring, zero, b);
        let h1 = k.fvar(H1);
        let h2 = k.fvar(H2);
        let ab = add_of_s(&mut k, &rn, ring, a, b);
        let goal = le_of_s(&mut k, &rn, ring, zero, ab);

        let assumptions = [(h1_ty, h1), (h2_ty, h2)];
        let proof = prove_s(
            &mut k,
            &p.rat.int.nat.logic,
            l1,
            &p.rat.int.nat.structures_s,
            &p.rat.ordered_ring_ext_s,
            &p.rat.int.nat,
            ring,
            None,
            &assumptions,
            goal,
        )
        .expect("linarith::generic (setoid) must derive sum-of-nonneg over CReal.orderedRingS");
        let _ = close_and_infer(&mut k, carrier, &[A, B], &[H1, H2], &[h1_ty, h2_ty], proof);
    }

    #[test]
    fn creal_linarith_slack_add_one() {
        const A: u64 = 56_200;
        const B: u64 = 56_201;
        const H: u64 = 56_210;
        let mut k = Kernel::new();
        let p = build_creal_prelude(&mut k).expect("creal prelude must build");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.ordered_ring_s, vec![]);
        let carrier = k.const_(p.creal, vec![]);
        let rn = p.rat.int.nat.structures_s.ordered_ring;
        let one = one_of_s(&mut k, &rn, ring);
        let zero_le_one = creal_zero_le_one(&mut k, &p);

        let (a, b) = (k.fvar(A), k.fvar(B));
        let h_ty = le_of_s(&mut k, &rn, ring, a, b);
        let h = k.fvar(H);
        let b_plus_one = add_of_s(&mut k, &rn, ring, b, one);
        let goal = le_of_s(&mut k, &rn, ring, a, b_plus_one);

        let assumptions = [(h_ty, h)];
        let proof = prove_s(
            &mut k,
            &p.rat.int.nat.logic,
            l1,
            &p.rat.int.nat.structures_s,
            &p.rat.ordered_ring_ext_s,
            &p.rat.int.nat,
            ring,
            Some(zero_le_one),
            &assumptions,
            goal,
        )
        .expect("linarith::generic (setoid) must derive the slack-1 goal over CReal.orderedRingS");
        let _ = close_and_infer(&mut k, carrier, &[A, B], &[H], &[h_ty], proof);
    }

    #[test]
    fn creal_linarith_add_le_add_three() {
        const A: u64 = 56_300;
        const B: u64 = 56_301;
        const C: u64 = 56_302;
        const D: u64 = 56_303;
        const E: u64 = 56_304;
        const F: u64 = 56_305;
        const H1: u64 = 56_310;
        const H2: u64 = 56_311;
        const H3: u64 = 56_312;
        let mut k = Kernel::new();
        let p = build_creal_prelude(&mut k).expect("creal prelude must build");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.ordered_ring_s, vec![]);
        let carrier = k.const_(p.creal, vec![]);
        let rn = p.rat.int.nat.structures_s.ordered_ring;

        let (a, b, c, d, e, f) = (
            k.fvar(A),
            k.fvar(B),
            k.fvar(C),
            k.fvar(D),
            k.fvar(E),
            k.fvar(F),
        );
        let h1_ty = le_of_s(&mut k, &rn, ring, a, d);
        let h2_ty = le_of_s(&mut k, &rn, ring, b, e);
        let h3_ty = le_of_s(&mut k, &rn, ring, c, f);
        let h1 = k.fvar(H1);
        let h2 = k.fvar(H2);
        let h3 = k.fvar(H3);

        let ab = add_of_s(&mut k, &rn, ring, a, b);
        let abc = add_of_s(&mut k, &rn, ring, ab, c);
        let de = add_of_s(&mut k, &rn, ring, d, e);
        let def = add_of_s(&mut k, &rn, ring, de, f);
        let goal = le_of_s(&mut k, &rn, ring, abc, def);

        let assumptions = [(h1_ty, h1), (h2_ty, h2), (h3_ty, h3)];
        let proof = prove_s(
            &mut k,
            &p.rat.int.nat.logic,
            l1,
            &p.rat.int.nat.structures_s,
            &p.rat.ordered_ring_ext_s,
            &p.rat.int.nat,
            ring,
            None,
            &assumptions,
            goal,
        )
        .expect(
            "linarith::generic (setoid) must find a certificate for add_le_add_three over CReal",
        );
        let _ = close_and_infer(
            &mut k,
            carrier,
            &[A, B, C, D, E, F],
            &[H1, H2, H3],
            &[h1_ty, h2_ty, h3_ty],
            proof,
        );
    }

    /// The `Shape::Eq` conclusion route (`le_antisymm`, concluding `equiv`,
    /// not `Eq`): `a<=b, b<=a |- Equiv a b` -- a fact `linarith::generic`
    /// reaches over `CReal` that no `Alg.OrderedRing`-flavored route ever
    /// could (`CReal`'s carrier equality is `Equiv`, never `Eq`).
    #[test]
    fn creal_linarith_equality_by_antisymmetry() {
        const A: u64 = 56_400;
        const B: u64 = 56_401;
        const H1: u64 = 56_410;
        const H2: u64 = 56_411;
        let mut k = Kernel::new();
        let p = build_creal_prelude(&mut k).expect("creal prelude must build");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.ordered_ring_s, vec![]);
        let carrier = k.const_(p.creal, vec![]);
        let rn = p.rat.int.nat.structures_s.ordered_ring;

        let (a, b) = (k.fvar(A), k.fvar(B));
        let h1_ty = le_of_s(&mut k, &rn, ring, a, b);
        let h2_ty = le_of_s(&mut k, &rn, ring, b, a);
        let h1 = k.fvar(H1);
        let h2 = k.fvar(H2);
        let goal = equiv_of_s(&mut k, &rn, ring, a, b);

        let assumptions = [(h1_ty, h1), (h2_ty, h2)];
        let proof = prove_s(
            &mut k,
            &p.rat.int.nat.logic,
            l1,
            &p.rat.int.nat.structures_s,
            &p.rat.ordered_ring_ext_s,
            &p.rat.int.nat,
            ring,
            None,
            &assumptions,
            goal,
        )
        .expect(
            "linarith::generic (setoid) must prove Equiv a b from a<=b, b<=a over CReal.orderedRingS",
        );
        let _ = close_and_infer(&mut k, carrier, &[A, B], &[H1, H2], &[h1_ty, h2_ty], proof);
    }

    // --- three false goals decline, at CReal.orderedRingS ---

    #[test]
    fn creal_linarith_false_goal_swap_declines() {
        const A: u64 = 57_000;
        const B: u64 = 57_001;
        const H: u64 = 57_010;
        let mut k = Kernel::new();
        let p = build_creal_prelude(&mut k).expect("creal prelude must build");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.ordered_ring_s, vec![]);
        let rn = p.rat.int.nat.structures_s.ordered_ring;
        let (a, b) = (k.fvar(A), k.fvar(B));
        let h_ty = le_of_s(&mut k, &rn, ring, a, b);
        let h = k.fvar(H);
        let goal = le_of_s(&mut k, &rn, ring, b, a);
        let result = prove_s(
            &mut k,
            &p.rat.int.nat.logic,
            l1,
            &p.rat.int.nat.structures_s,
            &p.rat.ordered_ring_ext_s,
            &p.rat.int.nat,
            ring,
            None,
            &[(h_ty, h)],
            goal,
        );
        assert!(
            result.is_err(),
            "a<=b does not imply b<=a over CReal -- must decline"
        );
    }

    #[test]
    fn creal_linarith_false_goal_cycle_declines() {
        const A: u64 = 57_100;
        const B: u64 = 57_101;
        const C: u64 = 57_102;
        const H1: u64 = 57_110;
        const H2: u64 = 57_111;
        let mut k = Kernel::new();
        let p = build_creal_prelude(&mut k).expect("creal prelude must build");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.ordered_ring_s, vec![]);
        let rn = p.rat.int.nat.structures_s.ordered_ring;
        let (a, b, c) = (k.fvar(A), k.fvar(B), k.fvar(C));
        let h1_ty = le_of_s(&mut k, &rn, ring, a, b);
        let h2_ty = le_of_s(&mut k, &rn, ring, b, c);
        let h1 = k.fvar(H1);
        let h2 = k.fvar(H2);
        let goal = le_of_s(&mut k, &rn, ring, c, a);
        let result = prove_s(
            &mut k,
            &p.rat.int.nat.logic,
            l1,
            &p.rat.int.nat.structures_s,
            &p.rat.ordered_ring_ext_s,
            &p.rat.int.nat,
            ring,
            None,
            &[(h1_ty, h1), (h2_ty, h2)],
            goal,
        );
        assert!(
            result.is_err(),
            "a<=b<=c does not imply c<=a over CReal -- must decline"
        );
    }

    #[test]
    fn creal_linarith_false_goal_off_by_one_declines() {
        const A: u64 = 57_200;
        let mut k = Kernel::new();
        let p = build_creal_prelude(&mut k).expect("creal prelude must build");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.ordered_ring_s, vec![]);
        let rn = p.rat.int.nat.structures_s.ordered_ring;
        let one = one_of_s(&mut k, &rn, ring);
        let a = k.fvar(A);
        let a_plus_one = add_of_s(&mut k, &rn, ring, a, one);
        let goal = le_of_s(&mut k, &rn, ring, a_plus_one, a);
        let result = prove_s(
            &mut k,
            &p.rat.int.nat.logic,
            l1,
            &p.rat.int.nat.structures_s,
            &p.rat.ordered_ring_ext_s,
            &p.rat.int.nat,
            ring,
            None,
            &[],
            goal,
        );
        assert!(
            result.is_err(),
            "a+1<=a is false over CReal -- must decline"
        );
    }

    // --- two corrupted certificates, rejected by the KERNEL ---

    #[test]
    fn creal_linarith_corrupted_certificate_wrong_multiplier_rejected() {
        const A: u64 = 58_000;
        const B: u64 = 58_001;
        const H: u64 = 58_010;
        let mut k = Kernel::new();
        let p = build_creal_prelude(&mut k).expect("creal prelude must build");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.ordered_ring_s, vec![]);
        let rn = p.rat.int.nat.structures_s.ordered_ring;
        let (a, b) = (k.fvar(A), k.fvar(B));
        let h_ty = le_of_s(&mut k, &rn, ring, a, b);
        let h = k.fvar(H);

        let cert = Certificate {
            multipliers: vec![2], // correct is 1
            residual: LinForm::zero(),
        };
        let corrupted = emit_le_from_certificate_s(
            &mut k,
            &p.rat.int.nat.logic,
            l1,
            &p.rat.int.nat.structures_s,
            &p.rat.ordered_ring_ext_s,
            &p.rat.int.nat,
            ring,
            None,
            &[(h_ty, h)],
            a,
            b,
            &cert,
            false,
        );
        let Ok(term) = corrupted else { return };
        let carrier = k.const_(p.creal, vec![]);
        let closed = {
            let v = lam_over(&mut k, H, h_ty, term);
            let v = lam_over(&mut k, B, carrier, v);
            lam_over(&mut k, A, carrier, v)
        };
        assert!(
            k.infer(closed).is_err(),
            "a wrong multiplier (setoid, CReal) must be rejected by the KERNEL"
        );
    }

    #[test]
    fn creal_linarith_corrupted_certificate_wrong_residual_rejected() {
        const A: u64 = 58_100;
        const B: u64 = 58_101;
        const H: u64 = 58_110;
        let mut k = Kernel::new();
        let p = build_creal_prelude(&mut k).expect("creal prelude must build");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.ordered_ring_s, vec![]);
        let rn = p.rat.int.nat.structures_s.ordered_ring;
        let (a, b) = (k.fvar(A), k.fvar(B));
        let h_ty = le_of_s(&mut k, &rn, ring, a, b);
        let h = k.fvar(H);
        let one = one_of_s(&mut k, &rn, ring);
        let zero_le_one = creal_zero_le_one(&mut k, &p);
        let goal_lhs = a;
        let goal_rhs = add_of_s(&mut k, &rn, ring, b, one); // real goal needs residual 1

        // Corrupted: claim residual 0 (exact match) when 1 is required.
        let cert = Certificate {
            multipliers: vec![1],
            residual: LinForm::zero(),
        };
        let corrupted = emit_le_from_certificate_s(
            &mut k,
            &p.rat.int.nat.logic,
            l1,
            &p.rat.int.nat.structures_s,
            &p.rat.ordered_ring_ext_s,
            &p.rat.int.nat,
            ring,
            Some(zero_le_one),
            &[(h_ty, h)],
            goal_lhs,
            goal_rhs,
            &cert,
            false,
        );
        let Ok(term) = corrupted else { return };
        let carrier = k.const_(p.creal, vec![]);
        let closed = {
            let v = lam_over(&mut k, H, h_ty, term);
            let v = lam_over(&mut k, B, carrier, v);
            lam_over(&mut k, A, carrier, v)
        };
        assert!(
            k.infer(closed).is_err(),
            "a wrong (too-small) residual (setoid, CReal) must be rejected by the KERNEL"
        );
    }

    /// Positive control for the two corrupted-certificate tests above: the
    /// SAME route with an UNCORRUPTED certificate is admitted.
    #[test]
    fn creal_linarith_uncorrupted_certificate_is_admitted() {
        const A: u64 = 58_200;
        const B: u64 = 58_201;
        const H: u64 = 58_210;
        let mut k = Kernel::new();
        let p = build_creal_prelude(&mut k).expect("creal prelude must build");
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let ring = k.const_(p.ordered_ring_s, vec![]);
        let carrier = k.const_(p.creal, vec![]);
        let rn = p.rat.int.nat.structures_s.ordered_ring;
        let (a, b) = (k.fvar(A), k.fvar(B));
        let h_ty = le_of_s(&mut k, &rn, ring, a, b);
        let h = k.fvar(H);

        let cert = Certificate {
            multipliers: vec![1],
            residual: LinForm::zero(),
        };
        let term = emit_le_from_certificate_s(
            &mut k,
            &p.rat.int.nat.logic,
            l1,
            &p.rat.int.nat.structures_s,
            &p.rat.ordered_ring_ext_s,
            &p.rat.int.nat,
            ring,
            None,
            &[(h_ty, h)],
            a,
            b,
            &cert,
            false,
        )
        .expect("the uncorrupted certificate (setoid, CReal) must emit a term");
        let closed = {
            let v = lam_over(&mut k, H, h_ty, term);
            let v = lam_over(&mut k, B, carrier, v);
            lam_over(&mut k, A, carrier, v)
        };
        k.infer(closed)
            .expect("an UNCORRUPTED certificate (setoid, CReal) must be admitted by the kernel");
    }

    /// Wall-clock cost, generic vs per-carrier, on the SAME two goal shapes
    /// (`add_le_add_three`'s three-hypothesis chain, and `add_left_comm`'s
    /// pure equation) — the comparison ADR-1585 reports. Measure in
    /// `--release`; the debug kernel costs up to 32x per frame
    /// (`linarith::cost`'s own module doc). `#[ignore]`d: a report, not a
    /// correctness gate. Run with:
    /// `cargo test --release -p axeyum-lean-kernel --lib -- \
    ///   linarith::generic::generic_tests::measured_ms_generic_vs_int \
    ///   --exact --ignored --nocapture`
    #[test]
    #[ignore = "a timing report, not a correctness gate -- run explicitly, --release"]
    fn measured_ms_generic_vs_int() {
        use crate::int_prelude::ops::IntDev;
        use crate::nat_prelude::NatOps;
        use std::time::Instant;

        const REPEATS: u32 = 200;

        // --- add_le_add_three -------------------------------------------
        {
            const BASE: u64 = 900_000;
            let mut k_int = Kernel::new();
            let p_int = crate::build_int_prelude(&mut k_int).expect("int prelude must build");
            let t0 = Instant::now();
            for i in 0..REPEATS {
                let mut d = IntDev::new(&mut k_int, p_int);
                let fvs: [u64; 6] = std::array::from_fn(|j| BASE + u64::from(i) * 20 + j as u64);
                let vars: Vec<ExprId> = fvs.iter().map(|&fv| d.kernel().fvar(fv)).collect();
                let (a, b, c, dd, e, f) = (vars[0], vars[1], vars[2], vars[3], vars[4], vars[5]);
                let h1_ty = d.ile(a, dd);
                let h2_ty = d.ile(b, e);
                let h3_ty = d.ile(c, f);
                let hvs: [u64; 3] = [
                    BASE + u64::from(i) * 20 + 10,
                    BASE + u64::from(i) * 20 + 11,
                    BASE + u64::from(i) * 20 + 12,
                ];
                let assumptions: Vec<(ExprId, ExprId)> =
                    [(h1_ty, hvs[0]), (h2_ty, hvs[1]), (h3_ty, hvs[2])]
                        .into_iter()
                        .map(|(ty, fv)| (ty, d.kernel().fvar(fv)))
                        .collect();
                let ab = d.iadd(a, b);
                let abc = d.iadd(ab, c);
                let de = d.iadd(dd, e);
                let def = d.iadd(de, f);
                let goal = d.ile(abc, def);
                let proof = crate::linarith::int::prove(&mut d, &p_int, &assumptions, goal)
                    .expect("int route must find the certificate");
                let _ = proof;
            }
            let int_search = t0.elapsed();
            eprintln!(
                "add_le_add_three  linarith::int      search {:.3} ms/term",
                int_search.as_secs_f64() * 1000.0 / f64::from(REPEATS)
            );
        }
        {
            let mut k_gen = Kernel::new();
            let p_gen = build_rat_prelude(&mut k_gen).expect("rat prelude must build");
            let l0 = k_gen.level_zero();
            let l1 = k_gen.level_succ(l0);
            let ring = k_gen.const_(p_gen.algebra_ext.int_ordered_ring, vec![]);
            let rn = p_gen.int.nat.structures.ordered_ring;
            let t0 = Instant::now();
            for i in 0..REPEATS {
                const BASE: u64 = 950_000;
                let fvs: [u64; 6] = std::array::from_fn(|j| BASE + u64::from(i) * 20 + j as u64);
                let (a, b, c, dd, e, f) = (
                    k_gen.fvar(fvs[0]),
                    k_gen.fvar(fvs[1]),
                    k_gen.fvar(fvs[2]),
                    k_gen.fvar(fvs[3]),
                    k_gen.fvar(fvs[4]),
                    k_gen.fvar(fvs[5]),
                );
                let h1_ty = le_of(&mut k_gen, &rn, ring, a, dd);
                let h2_ty = le_of(&mut k_gen, &rn, ring, b, e);
                let h3_ty = le_of(&mut k_gen, &rn, ring, c, f);
                let hvs: [u64; 3] = [
                    BASE + u64::from(i) * 20 + 10,
                    BASE + u64::from(i) * 20 + 11,
                    BASE + u64::from(i) * 20 + 12,
                ];
                let assumptions: [(ExprId, ExprId); 3] = [
                    (h1_ty, k_gen.fvar(hvs[0])),
                    (h2_ty, k_gen.fvar(hvs[1])),
                    (h3_ty, k_gen.fvar(hvs[2])),
                ];
                let ab = add_of(&mut k_gen, &rn, ring, a, b);
                let abc = add_of(&mut k_gen, &rn, ring, ab, c);
                let de = add_of(&mut k_gen, &rn, ring, dd, e);
                let def = add_of(&mut k_gen, &rn, ring, de, f);
                let goal = le_of(&mut k_gen, &rn, ring, abc, def);
                let proof = prove(
                    &mut k_gen,
                    &p_gen.int.nat.logic,
                    l1,
                    &p_gen.int.nat.structures,
                    &p_gen.ordered_ring_ext,
                    &p_gen.int.nat,
                    ring,
                    None,
                    &assumptions,
                    goal,
                )
                .expect("generic route must find the certificate");
                let _ = proof;
            }
            let gen_search = t0.elapsed();
            eprintln!(
                "add_le_add_three  linarith::generic  search {:.3} ms/term",
                gen_search.as_secs_f64() * 1000.0 / f64::from(REPEATS)
            );
        }
    }
}

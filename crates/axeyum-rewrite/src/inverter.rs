//! The shared **term inverter**: a per-theory plugin registry that answers one
//! question — *given an application `p = op(a₀ … aₙ)` in which the operand at
//! `idx` is unconstrained, what term may replace `p`, and how is every operand
//! it consumes recovered from a model of the replacement?*
//!
//! # Why a registry and not a `match`
//!
//! The occurrence analysis (which variable has one parent) and the inversion
//! rules (what may replace this operator) are independent concerns. Both Z3
//! (`src/ast/converters/expr_inverter.cpp`, a `ptr_vector<iexpr_inverter>`
//! indexed by theory family) and Bitwuzla factored inversion into a separate
//! component with several consumers; ours was a private six-operator `match`
//! inside `elim_unconstrained`. Splitting it means a new theory registers an
//! [`Inverter`] instead of editing a central function, and a second consumer
//! (quantifier destructive equality resolution, an inverse-lemma ladder) can
//! reuse the rules without inheriting this pass's notion of "unconstrained".
//!
//! The "is this unconstrained?" predicate is therefore **injected**
//! ([`InverterCtx::is_unconstrained`]): rules ask, they never compute.
//!
//! # The soundness contract every rule must meet
//!
//! Let `x` be the operand at `idx`, and write `p = op(…, x, …)`. A rule returns
//! [`Inversion`] `{ replacement r, defs [(sᵢ, dᵢ)] }` only if:
//!
//! 1. **Surjectivity.** For every value `v` that `r` can take under some model
//!    of the reduced problem, the definitions `sᵢ := eval(dᵢ)` produce operand
//!    values with `op(…) = v`. Equivalently: replacing `p` by `r` neither adds
//!    nor removes models, up to the eliminated symbols.
//! 2. **Every consumed symbol is defined.** A symbol that the rule removes from
//!    the formula and does not define is left unassigned; the pass defaults
//!    genuinely orphaned operands, but a symbol the rule *relies* on must be in
//!    `defs`.
//! 3. **`defs` may only mention** the fresh replacement symbol, the operands of
//!    `p`, and ground terms — nothing eliminated earlier.
//!
//! Obligation 1 is where wrong-`sat` lives, and every published counterexample
//! involves a **constant** operand: `110·v = 111` is unsat, yet replacing
//! `110·v` by a fresh variable makes it sat (multiplication by an even constant
//! is not surjective); `v <u 000` is unsat, yet `bvult` at the domain boundary
//! is not a free Boolean either. So the rules below either restrict to a
//! genuine bijection (`bvadd`, odd-constant `bvmul`, …), carry the missing
//! range as an explicit **side condition** folded into the replacement
//! (`bvule`, `bvult`), or reproduce the range structurally (the even-constant
//! `bvmul` rule keeps the trailing zeros).
//!
//! # Sort guard
//!
//! [`InverterCtx::mk_diff`] refuses any sort that is not fully interpreted or
//! has a single element — Z3's guard, whose counterexample is
//! `(forall ((x S) (y S)) (= x y)) ∧ (not (= c1 c2))`: `c1` and `c2` each occur
//! once, but the quantifier forces `S` to be a singleton, so `(= c1 c2)` is not
//! a free Boolean.

use std::collections::HashSet;

use axeyum_ir::{
    Assignment, IrError, Op, Rational, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval,
};

/// Which theory owns an operator, and therefore which registered [`Inverter`]
/// is asked to invert it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum Theory {
    /// Boolean connectives, `ite`, and polymorphic equality.
    Core,
    /// Fixed-width bit-vectors.
    Bv,
    /// `Int` and `Real` arithmetic.
    Arith,
    /// Arrays (`select`/`store`/`const`).
    Array,
    /// Algebraic datatypes.
    Datatype,
    /// Sequences and strings.
    Seq,
    /// Floating point.
    Fp,
    /// Uninterpreted function application.
    Uf,
    /// Quantifier binders — never invertible; present so the mapping is total.
    Quant,
    /// Cross-theory coercions (`bv2nat`, `int2bv`, `to_real`, …).
    Coercion,
}

impl Theory {
    /// Dense index used to key the registry.
    const COUNT: usize = 10;

    #[must_use]
    const fn index(self) -> usize {
        match self {
            Theory::Core => 0,
            Theory::Bv => 1,
            Theory::Arith => 2,
            Theory::Array => 3,
            Theory::Datatype => 4,
            Theory::Seq => 5,
            Theory::Fp => 6,
            Theory::Uf => 7,
            Theory::Quant => 8,
            Theory::Coercion => 9,
        }
    }
}

/// The theory that owns `op`.
#[must_use]
pub fn theory_of(op: Op) -> Theory {
    match op {
        Op::BoolNot
        | Op::BoolAnd
        | Op::BoolOr
        | Op::BoolXor
        | Op::BoolImplies
        | Op::Eq
        | Op::Ite => Theory::Core,
        Op::BvNot
        | Op::BvAnd
        | Op::BvOr
        | Op::BvXor
        | Op::BvNand
        | Op::BvNor
        | Op::BvXnor
        | Op::BvNeg
        | Op::BvAdd
        | Op::BvSub
        | Op::BvMul
        | Op::BvUdiv
        | Op::BvUrem
        | Op::BvSdiv
        | Op::BvSrem
        | Op::BvSmod
        | Op::BvShl
        | Op::BvLshr
        | Op::BvAshr
        | Op::BvUlt
        | Op::BvUle
        | Op::BvUgt
        | Op::BvUge
        | Op::BvSlt
        | Op::BvSle
        | Op::BvSgt
        | Op::BvSge
        | Op::BvComp
        | Op::Extract { .. }
        | Op::Concat
        | Op::ZeroExt { .. }
        | Op::SignExt { .. }
        | Op::RotateLeft { .. }
        | Op::RotateRight { .. } => Theory::Bv,
        Op::IntNeg
        | Op::IntAdd
        | Op::IntSub
        | Op::IntMul
        | Op::IntDiv
        | Op::IntMod
        | Op::IntAbs
        | Op::IntPow2
        | Op::IntLt
        | Op::IntLe
        | Op::IntGt
        | Op::IntGe
        | Op::RealNeg
        | Op::RealAdd
        | Op::RealSub
        | Op::RealMul
        | Op::RealDiv
        | Op::RealLt
        | Op::RealLe
        | Op::RealGt
        | Op::RealGe => Theory::Arith,
        Op::Select | Op::Store | Op::ConstArray { .. } => Theory::Array,
        Op::DtConstruct { .. } | Op::DtSelect { .. } | Op::DtTest(_) => Theory::Datatype,
        Op::Apply(_) => Theory::Uf,
        Op::Forall(_) | Op::Exists(_) => Theory::Quant,
        Op::IntToReal | Op::RealToInt | Op::RealIsInt | Op::Bv2Nat | Op::Int2Bv { .. } => {
            Theory::Coercion
        }
        Op::FpFromBits { .. } | Op::RoundingModeFromBits => Theory::Fp,
        // Everything else (sequence/string operators, FP predicates, overflow
        // predicates, …) has no inversion rule; `Seq` is the widest bucket and
        // an unregistered theory is simply never inverted.
        _ => Theory::Seq,
    }
}

/// A successful inversion of one application node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Inversion {
    /// The term that replaces the inverted application in the assertions.
    pub replacement: TermId,
    /// Symbol definitions for the model-reconstruction trail, appended in this
    /// order (the trail replays in reverse, so later entries reconstruct
    /// first).
    pub defs: Vec<(SymbolId, TermId)>,
    /// Stable rule name, used for per-rule instrumentation.
    pub rule: &'static str,
    /// `true` when [`Self::replacement`] is not a bare fresh variable. Such a
    /// replacement cannot be cascaded into within the same round (its operands
    /// re-enter the formula), so the pass ends the cascade at that node and
    /// re-derives the occurrence graph.
    pub compound: bool,
}

/// Everything a rule may do to the term graph, plus the injected
/// unconstrained-ness predicate.
pub struct InverterCtx<'a> {
    arena: &'a mut TermArena,
    is_unconstrained: &'a dyn Fn(TermId) -> bool,
    next_fresh: &'a mut u64,
}

impl std::fmt::Debug for InverterCtx<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("InverterCtx")
            .field("next_fresh", &self.next_fresh)
            .finish_non_exhaustive()
    }
}

impl<'a> InverterCtx<'a> {
    /// Builds a context over `arena` with an injected unconstrained-ness
    /// predicate and a fresh-variable counter.
    pub fn new(
        arena: &'a mut TermArena,
        is_unconstrained: &'a dyn Fn(TermId) -> bool,
        next_fresh: &'a mut u64,
    ) -> Self {
        Self {
            arena,
            is_unconstrained,
            next_fresh,
        }
    }

    /// Mutable access to the term arena.
    pub fn arena(&mut self) -> &mut TermArena {
        self.arena
    }

    /// Shared access to the term arena.
    #[must_use]
    pub fn arena_ref(&self) -> &TermArena {
        self.arena
    }

    /// The injected predicate: is `term` an unconstrained variable?
    #[must_use]
    pub fn is_unconstrained(&self, term: TermId) -> bool {
        (self.is_unconstrained)(term)
    }

    /// The symbol behind `term`, if it is a bare variable.
    #[must_use]
    pub fn symbol(&self, term: TermId) -> Option<SymbolId> {
        match self.arena.node(term) {
            TermNode::Symbol(s) => Some(*s),
            _ => None,
        }
    }

    /// Mints a fresh internal variable of `sort` (`!unconstr!N`, outside the
    /// SMT-LIB user identifier space) and returns its term.
    ///
    /// # Errors
    ///
    /// Propagates [`IrError`] from the declaration (a malformed sort).
    pub fn fresh(&mut self, sort: Sort) -> Result<TermId, IrError> {
        let name = format!("!unconstr!{}", self.next_fresh);
        *self.next_fresh += 1;
        let sym = self.arena.declare_internal(&name, sort)?;
        Ok(self.arena.var(sym))
    }

    /// A term guaranteed to denote a value **different** from `t`, or `None`
    /// when the sort cannot supply one.
    ///
    /// The guard is Z3's: refuse a sort that is not fully interpreted (an
    /// uninterpreted carrier, an array, a datatype, a sequence) or that could
    /// have a single element. `Bool` has two elements, `BitVec(w)` has
    /// `2^w ≥ 2`, and `Int`/`Real` are infinite, so `not`, `bvnot` and `+1` are
    /// each total and fixed-point-free on their sort.
    ///
    /// # Errors
    ///
    /// Propagates [`IrError`] from term construction.
    pub fn mk_diff(&mut self, t: TermId) -> Result<Option<TermId>, IrError> {
        Ok(match self.arena.sort_of(t) {
            Sort::Bool => Some(self.arena.not(t)?),
            Sort::BitVec(_) => Some(self.arena.bv_not(t)?),
            Sort::Int => {
                let one = self.arena.int_const(1);
                Some(self.arena.int_add(t, one)?)
            }
            Sort::Real => {
                let one = self.arena.real_const(Rational::new(1, 1));
                Some(self.arena.real_add(t, one)?)
            }
            _ => None,
        })
    }

    /// A ground term of `sort` used to default an operand the rewrite orphaned,
    /// or `None` when this module cannot name one.
    ///
    /// # Errors
    ///
    /// Propagates [`IrError`] from term construction.
    pub fn default_value(&mut self, sort: Sort) -> Result<Option<TermId>, IrError> {
        Ok(match sort {
            Sort::Bool => Some(self.arena.bool_const(false)),
            Sort::BitVec(w) => Some(self.arena.bv_const(w, 0)?),
            Sort::Int => Some(self.arena.int_const(0)),
            Sort::Real => Some(self.arena.real_const(Rational::zero())),
            _ => None,
        })
    }
}

/// Whether this module can name a default value for `sort`. The pass refuses to
/// invert an application any of whose operand sorts fails this, so an orphaned
/// operand always has a value to fall back on.
#[must_use]
pub fn is_defaultable_sort(sort: Sort) -> bool {
    matches!(sort, Sort::Bool | Sort::BitVec(_) | Sort::Int | Sort::Real)
}

/// A per-theory set of inversion rules.
pub trait Inverter: std::fmt::Debug {
    /// The theory whose operators this plugin inverts.
    fn theory(&self) -> Theory;

    /// Attempts to invert `op(args…)` for the operand at `idx`, which the
    /// caller has already established is unconstrained.
    ///
    /// Returns `Ok(None)` when no rule applies — the overwhelmingly common
    /// case, and never an error.
    ///
    /// # Errors
    ///
    /// Propagates [`IrError`] from term construction.
    fn invert(
        &self,
        ctx: &mut InverterCtx<'_>,
        op: Op,
        args: &[TermId],
        idx: usize,
        result_sort: Sort,
    ) -> Result<Option<Inversion>, IrError>;
}

/// The registry: one [`Inverter`] per theory, dispatched on the operator's
/// theory. A theory with no registered plugin is simply never inverted.
#[derive(Debug)]
pub struct InverterRegistry {
    plugins: Vec<Option<Box<dyn Inverter>>>,
}

impl Default for InverterRegistry {
    fn default() -> Self {
        Self::new()
    }
}

impl InverterRegistry {
    /// An empty registry — nothing is invertible.
    #[must_use]
    pub fn new() -> Self {
        let mut plugins = Vec::with_capacity(Theory::COUNT);
        plugins.resize_with(Theory::COUNT, || None);
        Self { plugins }
    }

    /// The registry the preprocessing pipeline uses: core, bit-vector and
    /// arithmetic rules.
    #[must_use]
    pub fn with_defaults() -> Self {
        let mut registry = Self::new();
        registry.register(Box::new(CoreInverter));
        registry.register(Box::new(BvInverter));
        registry.register(Box::new(ArithInverter));
        registry
    }

    /// Registers `plugin`, replacing any plugin already registered for its
    /// theory.
    pub fn register(&mut self, plugin: Box<dyn Inverter>) {
        let index = plugin.theory().index();
        self.plugins[index] = Some(plugin);
    }

    /// Whether a plugin is registered for `theory`.
    #[must_use]
    pub fn has(&self, theory: Theory) -> bool {
        self.plugins[theory.index()].is_some()
    }

    /// Dispatches `op` to its theory's plugin.
    ///
    /// # Errors
    ///
    /// Propagates [`IrError`] from term construction inside a rule.
    pub fn invert(
        &self,
        ctx: &mut InverterCtx<'_>,
        op: Op,
        args: &[TermId],
        idx: usize,
        result_sort: Sort,
    ) -> Result<Option<Inversion>, IrError> {
        match &self.plugins[theory_of(op).index()] {
            Some(plugin) => plugin.invert(ctx, op, args, idx, result_sort),
            None => Ok(None),
        }
    }
}

/// Builds a plain `Inversion` replacing the node by a fresh variable.
fn fresh_replacement(
    ctx: &mut InverterCtx<'_>,
    sort: Sort,
    rule: &'static str,
) -> Result<(TermId, Inversion), IrError> {
    let u = ctx.fresh(sort)?;
    Ok((
        u,
        Inversion {
            replacement: u,
            defs: Vec::new(),
            rule,
            compound: false,
        },
    ))
}

/// The operands of `args` other than the one at `idx`.
fn others(args: &[TermId], idx: usize) -> Vec<TermId> {
    args.iter()
        .enumerate()
        .filter_map(|(i, &a)| (i != idx).then_some(a))
        .collect()
}

/// Whether **every** operand is an unconstrained variable (Z3's `uncnstr(num,
/// args)` — the side condition of the `bvand`/`bvor`/`*`/`concat` rules).
fn all_unconstrained(ctx: &InverterCtx<'_>, args: &[TermId]) -> bool {
    args.iter().all(|&a| ctx.is_unconstrained(a))
}

/// Collects the symbols of `args` when every one is a bare variable.
fn symbols_of(ctx: &InverterCtx<'_>, args: &[TermId]) -> Option<Vec<SymbolId>> {
    args.iter().map(|&a| ctx.symbol(a)).collect()
}

// ---------------------------------------------------------------------------
// Core: Boolean connectives, `ite`, equality
// ---------------------------------------------------------------------------

/// Booleans, `ite` and polymorphic equality.
#[derive(Debug, Clone, Copy)]
pub struct CoreInverter;

impl Inverter for CoreInverter {
    fn theory(&self) -> Theory {
        Theory::Core
    }

    fn invert(
        &self,
        ctx: &mut InverterCtx<'_>,
        op: Op,
        args: &[TermId],
        idx: usize,
        _result_sort: Sort,
    ) -> Result<Option<Inversion>, IrError> {
        let Some(x) = ctx.symbol(args[idx]) else {
            return Ok(None);
        };
        match op {
            // `(not x) => u`, `x := not u`. A bijection on `Bool`.
            Op::BoolNot if args.len() == 1 => {
                let (u, mut inv) = fresh_replacement(ctx, Sort::Bool, "core/not")?;
                let def = ctx.arena().not(u)?;
                inv.defs.push((x, def));
                Ok(Some(inv))
            }
            // `(xor x t…) => u`, `x := u xor (xor rest)`. Self-inverse, so a
            // bijection in each operand.
            Op::BoolXor if args.len() >= 2 => {
                let rest = others(args, idx);
                let (u, mut inv) = fresh_replacement(ctx, Sort::Bool, "core/xor")?;
                let mut acc = rest[0];
                for &o in &rest[1..] {
                    acc = ctx.arena().xor(acc, o)?;
                }
                let def = ctx.arena().xor(u, acc)?;
                inv.defs.push((x, def));
                Ok(Some(inv))
            }
            // `(and x₁…xₙ) => u` with **every** operand unconstrained:
            // `x_idx := u`, the rest `:= true`. `(or …)` dually.
            Op::BoolAnd | Op::BoolOr if args.len() >= 2 && all_unconstrained(ctx, args) => {
                let Some(syms) = symbols_of(ctx, args) else {
                    return Ok(None);
                };
                let rule = if op == Op::BoolAnd {
                    "core/and-all"
                } else {
                    "core/or-all"
                };
                let (u, mut inv) = fresh_replacement(ctx, Sort::Bool, rule)?;
                let identity = ctx.arena().bool_const(op == Op::BoolAnd);
                for (i, sym) in syms.into_iter().enumerate() {
                    inv.defs.push((sym, if i == idx { u } else { identity }));
                }
                Ok(Some(inv))
            }
            // `(ite c x x') => u` with both branches unconstrained: `x := u`,
            // `x' := u` (the condition is then irrelevant and may be dropped).
            // `(ite x x' e) => u` with condition and *then* branch
            // unconstrained: `x := true`, `x' := u`; dually for the else side.
            Op::Ite if args.len() == 3 => invert_ite(ctx, args, idx),
            // `(= x t) => u`, `x := ite(u, t, diff(t))`: with `x` free the
            // equality is a free Boolean, witnessed by "make them equal, else
            // make them differ". `mk_diff` carries the singleton-sort guard.
            Op::Eq if args.len() == 2 => {
                let t = args[1 - idx];
                let Some(diff) = ctx.mk_diff(t)? else {
                    return Ok(None);
                };
                let (u, mut inv) = fresh_replacement(ctx, Sort::Bool, "core/eq-diff")?;
                let def = ctx.arena().ite(u, t, diff)?;
                inv.defs.push((x, def));
                Ok(Some(inv))
            }
            _ => Ok(None),
        }
    }
}

/// The three `ite` rules, split out to keep [`CoreInverter::invert`] flat.
fn invert_ite(
    ctx: &mut InverterCtx<'_>,
    args: &[TermId],
    idx: usize,
) -> Result<Option<Inversion>, IrError> {
    let (cond, then_branch, else_branch) = (args[0], args[1], args[2]);
    let branch_sort = ctx.arena_ref().sort_of(then_branch);
    if idx == 0 {
        // The condition is unconstrained; pin it so one branch is selected and
        // that branch must itself be unconstrained.
        let Some(cond_sym) = ctx.symbol(cond) else {
            return Ok(None);
        };
        for (branch, take, rule) in [
            (then_branch, true, "core/ite-cond-then"),
            (else_branch, false, "core/ite-cond-else"),
        ] {
            if !ctx.is_unconstrained(branch) {
                continue;
            }
            let Some(branch_sym) = ctx.symbol(branch) else {
                continue;
            };
            let (u, mut inv) = fresh_replacement(ctx, branch_sort, rule)?;
            let pin = ctx.arena().bool_const(take);
            inv.defs.push((cond_sym, pin));
            inv.defs.push((branch_sym, u));
            return Ok(Some(inv));
        }
        return Ok(None);
    }
    // A branch is unconstrained; the rule needs *both* branches free, so the
    // replacement is reachable whichever way the condition falls.
    if !ctx.is_unconstrained(then_branch) || !ctx.is_unconstrained(else_branch) {
        return Ok(None);
    }
    let (Some(then_sym), Some(else_sym)) = (ctx.symbol(then_branch), ctx.symbol(else_branch))
    else {
        return Ok(None);
    };
    let (u, mut inv) = fresh_replacement(ctx, branch_sort, "core/ite-branches")?;
    inv.defs.push((then_sym, u));
    inv.defs.push((else_sym, u));
    Ok(Some(inv))
}

// ---------------------------------------------------------------------------
// Arithmetic: Int and Real
// ---------------------------------------------------------------------------

/// `Int`/`Real` arithmetic — the rules that fire in `QF_LIA`, `QF_LRA`,
/// `QF_IDL`, `QF_NIA` and `QF_NRA`, where this pass previously did nothing at
/// all.
#[derive(Debug, Clone, Copy)]
pub struct ArithInverter;

/// Which of the two arithmetic sorts an operator works over.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ArithSort {
    Int,
    Real,
}

impl ArithInverter {
    fn sort_of_op(op: Op) -> Option<(ArithSort, Sort)> {
        match op {
            Op::IntNeg
            | Op::IntAdd
            | Op::IntSub
            | Op::IntMul
            | Op::IntLt
            | Op::IntLe
            | Op::IntGt
            | Op::IntGe => Some((ArithSort::Int, Sort::Int)),
            Op::RealNeg
            | Op::RealAdd
            | Op::RealSub
            | Op::RealMul
            | Op::RealLt
            | Op::RealLe
            | Op::RealGt
            | Op::RealGe => Some((ArithSort::Real, Sort::Real)),
            _ => None,
        }
    }
}

/// `a + b` in the given arithmetic sort.
fn arith_add(
    ctx: &mut InverterCtx<'_>,
    s: ArithSort,
    a: TermId,
    b: TermId,
) -> Result<TermId, IrError> {
    match s {
        ArithSort::Int => ctx.arena().int_add(a, b),
        ArithSort::Real => ctx.arena().real_add(a, b),
    }
}

/// `a - b` in the given arithmetic sort.
fn arith_sub(
    ctx: &mut InverterCtx<'_>,
    s: ArithSort,
    a: TermId,
    b: TermId,
) -> Result<TermId, IrError> {
    match s {
        ArithSort::Int => ctx.arena().int_sub(a, b),
        ArithSort::Real => ctx.arena().real_sub(a, b),
    }
}

/// The literal `1` of the given arithmetic sort.
fn arith_one(ctx: &mut InverterCtx<'_>, s: ArithSort) -> TermId {
    match s {
        ArithSort::Int => ctx.arena().int_const(1),
        ArithSort::Real => ctx.arena().real_const(Rational::new(1, 1)),
    }
}

impl Inverter for ArithInverter {
    fn theory(&self) -> Theory {
        Theory::Arith
    }

    fn invert(
        &self,
        ctx: &mut InverterCtx<'_>,
        op: Op,
        args: &[TermId],
        idx: usize,
        _result_sort: Sort,
    ) -> Result<Option<Inversion>, IrError> {
        let Some(x) = ctx.symbol(args[idx]) else {
            return Ok(None);
        };
        let Some((asort, sort)) = ArithInverter::sort_of_op(op) else {
            return Ok(None);
        };
        match op {
            // `(- x) => u`, `x := -u`. A bijection.
            Op::IntNeg | Op::RealNeg if args.len() == 1 => {
                let (u, mut inv) = fresh_replacement(ctx, sort, "arith/neg")?;
                let def = match asort {
                    ArithSort::Int => ctx.arena().int_neg(u)?,
                    ArithSort::Real => ctx.arena().real_neg(u)?,
                };
                inv.defs.push((x, def));
                Ok(Some(inv))
            }
            // `(+ t₁ … x … tₙ) => u`, `x := u − Σ_{j≠i} tⱼ`. **Any one**
            // unconstrained operand suffices — the highest-yield rule in the
            // arithmetic table.
            Op::IntAdd | Op::RealAdd if args.len() >= 2 => {
                let rest = others(args, idx);
                let (u, mut inv) = fresh_replacement(ctx, sort, "arith/add")?;
                let mut sum = rest[0];
                for &o in &rest[1..] {
                    sum = arith_add(ctx, asort, sum, o)?;
                }
                let def = arith_sub(ctx, asort, u, sum)?;
                inv.defs.push((x, def));
                Ok(Some(inv))
            }
            // `(- a b)`: a bijection in either operand.
            Op::IntSub | Op::RealSub if args.len() == 2 => {
                let (u, mut inv) = fresh_replacement(ctx, sort, "arith/sub")?;
                let def = if idx == 0 {
                    arith_add(ctx, asort, u, args[1])?
                } else {
                    arith_sub(ctx, asort, args[0], u)?
                };
                inv.defs.push((x, def));
                Ok(Some(inv))
            }
            Op::IntMul | Op::RealMul if args.len() == 2 => {
                invert_arith_mul(ctx, asort, sort, args, idx)
            }
            Op::IntMul | Op::RealMul if args.len() > 2 => {
                invert_mul_all(ctx, asort, sort, args, idx, "arith/mul-all")
            }
            // Order comparisons. `Int` and `Real` are unbounded, so a free
            // operand makes the atom a free Boolean with **no** side condition
            // — unlike the bit-vector versions below.
            Op::IntLt
            | Op::RealLt
            | Op::IntLe
            | Op::RealLe
            | Op::IntGt
            | Op::RealGt
            | Op::IntGe
            | Op::RealGe
                if args.len() == 2 =>
            {
                invert_arith_cmp(ctx, asort, op, args, idx, x)
            }
            _ => Ok(None),
        }
    }
}

/// `(* x₁ … xₙ) => u` with every operand unconstrained: `x_idx := u`, the rest
/// `:= 1`. Shared by `Int`/`Real` multiplication.
fn invert_mul_all(
    ctx: &mut InverterCtx<'_>,
    asort: ArithSort,
    sort: Sort,
    args: &[TermId],
    idx: usize,
    rule: &'static str,
) -> Result<Option<Inversion>, IrError> {
    if !all_unconstrained(ctx, args) {
        return Ok(None);
    }
    let Some(syms) = symbols_of(ctx, args) else {
        return Ok(None);
    };
    let (u, mut inv) = fresh_replacement(ctx, sort, rule)?;
    let one = arith_one(ctx, asort);
    for (i, sym) in syms.into_iter().enumerate() {
        inv.defs.push((sym, if i == idx { u } else { one }));
    }
    Ok(Some(inv))
}

/// Binary `*`: the all-unconstrained rule, or — **reals only** — division by a
/// non-zero numeral. `c·x` over `Int` does not range over every integer, which
/// is why Z3 guards that rule with `!is_int`; the bit-vector analogue is the
/// odd-constant rule below, and both exist for the same reason.
fn invert_arith_mul(
    ctx: &mut InverterCtx<'_>,
    asort: ArithSort,
    sort: Sort,
    args: &[TermId],
    idx: usize,
) -> Result<Option<Inversion>, IrError> {
    if let Some(inv) = invert_mul_all(ctx, asort, sort, args, idx, "arith/mul-all")? {
        return Ok(Some(inv));
    }
    if asort != ArithSort::Real {
        return Ok(None);
    }
    let Some(x) = ctx.symbol(args[idx]) else {
        return Ok(None);
    };
    let coefficient = args[1 - idx];
    let Ok(Value::Real(c)) = eval(ctx.arena_ref(), coefficient, &Assignment::new()) else {
        return Ok(None);
    };
    if c.is_zero() {
        return Ok(None);
    }
    let (u, mut inv) = fresh_replacement(ctx, sort, "arith/mul-real-const")?;
    let recip = ctx.arena().real_const(c.recip());
    let def = ctx.arena().real_mul(recip, u)?;
    inv.defs.push((x, def));
    Ok(Some(inv))
}

/// The eight arithmetic order atoms. With `x` free, the atom is a free Boolean:
/// pick the boundary value when the fresh bit says "true", and step one past it
/// when it says "false". `Int` and `Real` are both unbounded, so the step never
/// leaves the sort.
fn invert_arith_cmp(
    ctx: &mut InverterCtx<'_>,
    asort: ArithSort,
    op: Op,
    args: &[TermId],
    idx: usize,
    x: SymbolId,
) -> Result<Option<Inversion>, IrError> {
    let t = args[1 - idx];
    // `strict` distinguishes `<`/`>` from `<=`/`>=`; `x_is_lower` says whether
    // the unconstrained operand sits on the smaller side of the relation.
    let (strict, x_is_lower) = match (op, idx) {
        (Op::IntLt | Op::RealLt, 0) | (Op::IntGt | Op::RealGt, 1) => (true, true),
        (Op::IntLt | Op::RealLt, 1) | (Op::IntGt | Op::RealGt, 0) => (true, false),
        (Op::IntLe | Op::RealLe, 0) | (Op::IntGe | Op::RealGe, 1) => (false, true),
        (Op::IntLe | Op::RealLe, 1) | (Op::IntGe | Op::RealGe, 0) => (false, false),
        _ => return Ok(None),
    };
    let rule = match (strict, x_is_lower) {
        (true, true) => "arith/lt-lhs",
        (true, false) => "arith/lt-rhs",
        (false, true) => "arith/le-lhs",
        (false, false) => "arith/le-rhs",
    };
    let (u, mut inv) = fresh_replacement(ctx, Sort::Bool, rule)?;
    let one = arith_one(ctx, asort);
    // `x_is_lower` and `strict` decide which of `t-1`, `t`, `t+1` makes the atom
    // true and which makes it false:
    //   x <  t : true at t-1, false at t
    //   x <= t : true at t,   false at t+1
    //   t <  x : true at t+1, false at t
    //   t <= x : true at t,   false at t-1
    let (when_true, when_false) = match (x_is_lower, strict) {
        (true, true) => (arith_sub(ctx, asort, t, one)?, t),
        (true, false) => (t, arith_add(ctx, asort, t, one)?),
        (false, true) => (arith_add(ctx, asort, t, one)?, t),
        (false, false) => (t, arith_sub(ctx, asort, t, one)?),
    };
    let def = ctx.arena().ite(u, when_true, when_false)?;
    inv.defs.push((x, def));
    Ok(Some(inv))
}

// ---------------------------------------------------------------------------
// Bit-vectors
// ---------------------------------------------------------------------------

/// Bit-vector rules. The six that predate the registry (`bvnot`, `bvneg`,
/// `bvadd`, `bvxor`, `bvsub`, odd-constant `bvmul`) are here unchanged; the
/// rest follow Z3's `bv_expr_inverter`.
#[derive(Debug, Clone, Copy)]
pub struct BvInverter;

/// Bit-vector constants above 128 bits need the wide representation, which
/// several of the boundary rules below do not construct; they are simply not
/// applied at those widths.
const MAX_NARROW_BV_WIDTH: u32 = 128;

axeyum_ir::cap_lever! {
    /// The effective value of [`MAX_NARROW_BV_WIDTH`]: the compiled default, or
    /// `AXEYUM_MAX_NARROW_BV_WIDTH` when that variable is set.
    ///
    /// A measurement lever, not a tuning knob. With the variable unset this is
    /// exactly `MAX_NARROW_BV_WIDTH`, so the shipped binary is unchanged; a malformed
    /// value is refused rather than silently defaulted. See
    /// [`axeyum_ir::config_lever`] for the contract.
    fn max_narrow_bv_width() -> u32 = "AXEYUM_MAX_NARROW_BV_WIDTH" or MAX_NARROW_BV_WIDTH;
}

impl Inverter for BvInverter {
    fn theory(&self) -> Theory {
        Theory::Bv
    }

    fn invert(
        &self,
        ctx: &mut InverterCtx<'_>,
        op: Op,
        args: &[TermId],
        idx: usize,
        result_sort: Sort,
    ) -> Result<Option<Inversion>, IrError> {
        let Some(x) = ctx.symbol(args[idx]) else {
            return Ok(None);
        };
        match op {
            // ---- bijections in the unconstrained operand -------------------
            Op::BvNot if args.len() == 1 => {
                let (u, mut inv) = fresh_replacement(ctx, result_sort, "bv/not")?;
                let def = ctx.arena().bv_not(u)?;
                inv.defs.push((x, def));
                Ok(Some(inv))
            }
            Op::BvNeg if args.len() == 1 => {
                let (u, mut inv) = fresh_replacement(ctx, result_sort, "bv/neg")?;
                let def = ctx.arena().bv_neg(u)?;
                inv.defs.push((x, def));
                Ok(Some(inv))
            }
            Op::RotateLeft { by } | Op::RotateRight { by } if args.len() == 1 => {
                let (u, mut inv) = fresh_replacement(ctx, result_sort, "bv/rotate")?;
                let def = if matches!(op, Op::RotateLeft { .. }) {
                    ctx.arena().rotate_right(by, u)?
                } else {
                    ctx.arena().rotate_left(by, u)?
                };
                inv.defs.push((x, def));
                Ok(Some(inv))
            }
            Op::BvAdd if args.len() >= 2 => {
                let rest = others(args, idx);
                let (u, mut inv) = fresh_replacement(ctx, result_sort, "bv/add")?;
                let mut sum = rest[0];
                for &o in &rest[1..] {
                    sum = ctx.arena().bv_add(sum, o)?;
                }
                let def = ctx.arena().bv_sub(u, sum)?;
                inv.defs.push((x, def));
                Ok(Some(inv))
            }
            Op::BvXor if args.len() >= 2 => {
                let rest = others(args, idx);
                let (u, mut inv) = fresh_replacement(ctx, result_sort, "bv/xor")?;
                let mut acc = rest[0];
                for &o in &rest[1..] {
                    acc = ctx.arena().bv_xor(acc, o)?;
                }
                let def = ctx.arena().bv_xor(u, acc)?;
                inv.defs.push((x, def));
                Ok(Some(inv))
            }
            // `xnor` is `xor` complemented, and complementing is its own
            // inverse, so the same peel works with one extra `bvnot`.
            Op::BvXnor if args.len() == 2 => {
                let other = args[1 - idx];
                let (u, mut inv) = fresh_replacement(ctx, result_sort, "bv/xnor")?;
                let base = ctx.arena().bv_not(u)?;
                let def = ctx.arena().bv_xor(base, other)?;
                inv.defs.push((x, def));
                Ok(Some(inv))
            }
            Op::BvSub if args.len() == 2 => {
                let (u, mut inv) = fresh_replacement(ctx, result_sort, "bv/sub")?;
                let def = if idx == 0 {
                    ctx.arena().bv_add(u, args[1])?
                } else {
                    ctx.arena().bv_sub(args[0], u)?
                };
                inv.defs.push((x, def));
                Ok(Some(inv))
            }
            // ---- structural ------------------------------------------------
            Op::Extract { hi, lo } if args.len() == 1 => invert_extract(ctx, args[0], hi, lo, x),
            Op::Concat if args.len() >= 2 => invert_concat(ctx, args, result_sort),
            // ---- identity-operand rules (all operands unconstrained) -------
            Op::BvAnd | Op::BvOr | Op::BvMul if args.len() >= 2 => {
                invert_bv_identity(ctx, op, args, idx, result_sort)
            }
            Op::BvShl | Op::BvLshr | Op::BvAshr | Op::BvUdiv | Op::BvSdiv if args.len() == 2 => {
                invert_bv_binary_both(ctx, op, args, result_sort)
            }
            // ---- comparisons ----------------------------------------------
            Op::BvComp if args.len() == 2 => {
                let t = args[1 - idx];
                let Some(diff) = ctx.mk_diff(t)? else {
                    return Ok(None);
                };
                let (u, mut inv) = fresh_replacement(ctx, result_sort, "bv/comp")?;
                let one = ctx.arena().bv_const(1, 1)?;
                let cond = ctx.arena().eq(u, one)?;
                let def = ctx.arena().ite(cond, t, diff)?;
                inv.defs.push((x, def));
                Ok(Some(inv))
            }
            Op::BvUlt
            | Op::BvUle
            | Op::BvUgt
            | Op::BvUge
            | Op::BvSlt
            | Op::BvSle
            | Op::BvSgt
            | Op::BvSge
                if args.len() == 2 =>
            {
                invert_bv_cmp(ctx, op, args, idx, x)
            }
            _ => Ok(None),
        }
    }
}

/// `x[hi:lo] => u`. As `x` ranges over its sort the slice ranges over all of
/// `BitVec(hi-lo+1)`, so the extract is unconstrained; the recovered `x` puts
/// `u` back in place and zeroes the bits the slice discarded.
fn invert_extract(
    ctx: &mut InverterCtx<'_>,
    operand: TermId,
    hi: u32,
    lo: u32,
    x: SymbolId,
) -> Result<Option<Inversion>, IrError> {
    let Sort::BitVec(width) = ctx.arena_ref().sort_of(operand) else {
        return Ok(None);
    };
    let slice_width = hi - lo + 1;
    let (u, mut inv) = fresh_replacement(
        ctx,
        Sort::BitVec(slice_width),
        if slice_width == width {
            "bv/extract-full"
        } else {
            "bv/extract-slice"
        },
    )?;
    // `x := 0^{width-1-hi} ++ u ++ 0^{lo}`, omitting empty blocks.
    let mut def = u;
    if lo > 0 {
        let low = ctx.arena().bv_const(lo, 0)?;
        def = ctx.arena().concat(def, low)?;
    }
    if hi + 1 < width {
        let high = ctx.arena().bv_const(width - hi - 1, 0)?;
        def = ctx.arena().concat(high, def)?;
    }
    inv.defs.push((x, def));
    Ok(Some(inv))
}

/// `(concat x₁ … xₙ) => u` with **every** operand unconstrained: each `xᵢ` is
/// the corresponding slice of `u`. Walks from the least significant end, which
/// is the last argument (the first argument supplies the high bits).
fn invert_concat(
    ctx: &mut InverterCtx<'_>,
    args: &[TermId],
    result_sort: Sort,
) -> Result<Option<Inversion>, IrError> {
    if !all_unconstrained(ctx, args) {
        return Ok(None);
    }
    let Some(syms) = symbols_of(ctx, args) else {
        return Ok(None);
    };
    let (u, mut inv) = fresh_replacement(ctx, result_sort, "bv/concat-all")?;
    let mut low = 0u32;
    for (arg, sym) in args.iter().rev().zip(syms.into_iter().rev()) {
        let Sort::BitVec(w) = ctx.arena_ref().sort_of(*arg) else {
            return Ok(None);
        };
        let slice = ctx.arena().extract(low + w - 1, low, u)?;
        inv.defs.push((sym, slice));
        low += w;
    }
    Ok(Some(inv))
}

/// `bvand`/`bvor`/`bvmul` with **every** operand unconstrained: one operand
/// takes the fresh value and the others take the operator's identity
/// (`ones`/`0`/`1`). A single free operand is *not* enough — `bvand` and
/// `bvmul` are not surjective in one argument.
fn invert_bv_identity(
    ctx: &mut InverterCtx<'_>,
    op: Op,
    args: &[TermId],
    idx: usize,
    result_sort: Sort,
) -> Result<Option<Inversion>, IrError> {
    if op == Op::BvMul && args.len() == 2 && !all_unconstrained(ctx, args) {
        return invert_bv_mul_const(ctx, args, idx, result_sort);
    }
    if !all_unconstrained(ctx, args) {
        return Ok(None);
    }
    let Some(syms) = symbols_of(ctx, args) else {
        return Ok(None);
    };
    let Sort::BitVec(width) = result_sort else {
        return Ok(None);
    };
    let rule = match op {
        Op::BvAnd => "bv/and-all",
        Op::BvOr => "bv/or-all",
        _ => "bv/mul-all",
    };
    let (u, mut inv) = fresh_replacement(ctx, result_sort, rule)?;
    let identity = match op {
        // `bvand`'s identity is all-ones, which needs the wide constant path
        // above 128 bits; `bvnot 0` builds it at any width.
        Op::BvAnd => {
            let zero = ctx.arena().bv_const(width, 0)?;
            ctx.arena().bv_not(zero)?
        }
        Op::BvOr => ctx.arena().bv_const(width, 0)?,
        _ => ctx.arena().bv_const(width, 1)?,
    };
    for (i, sym) in syms.into_iter().enumerate() {
        inv.defs.push((sym, if i == idx { u } else { identity }));
    }
    Ok(Some(inv))
}

/// `bvmul` by a ground constant.
///
/// **This is the wrong-`sat` corner.** `110 · v = 111` is unsat, and replacing
/// `110 · v` by a fresh variable makes it sat: multiplication by an even
/// constant is not surjective. Two rules, and no third:
///
/// * `c` **odd**: `c` is a unit mod `2^w`, so `c·x` is a bijection —
///   `x := c⁻¹·u`.
/// * `K > 0` **even**: write `K = 2^sh · J` with `J` odd. Then `K·x` ranges over
///   exactly the multiples of `2^sh`, so the replacement must keep those `sh`
///   trailing zeros: `u[w-sh-1:0] ++ 0^sh`, with `x := J⁻¹·u`. Verifying:
///   `K·x = 2^sh·J·J⁻¹·u = 2^sh·u`, which is `u` shifted left by `sh` — the
///   replacement term exactly.
/// * `c = 0`: `0·x` is the constant `0`, not unconstrained at all. No rule.
fn invert_bv_mul_const(
    ctx: &mut InverterCtx<'_>,
    args: &[TermId],
    idx: usize,
    result_sort: Sort,
) -> Result<Option<Inversion>, IrError> {
    let Sort::BitVec(width) = result_sort else {
        return Ok(None);
    };
    let Some(x) = ctx.symbol(args[idx]) else {
        return Ok(None);
    };
    let coefficient = args[1 - idx];
    let Ok(Value::Bv { width: w, value }) = eval(ctx.arena_ref(), coefficient, &Assignment::new())
    else {
        return Ok(None);
    };
    if w != width || value == 0 {
        return Ok(None);
    }
    if value & 1 == 1 {
        let inverse = mod_inverse_pow2(value, width);
        let (u, mut inv) = fresh_replacement(ctx, result_sort, "bv/mul-odd-const")?;
        let inv_const = ctx.arena().bv_const(width, inverse)?;
        let def = ctx.arena().bv_mul(inv_const, u)?;
        inv.defs.push((x, def));
        return Ok(Some(inv));
    }
    // Even, non-zero. `sh < width` because `0 < value < 2^width`.
    let shift = value.trailing_zeros();
    let odd_part = value >> shift;
    let inverse = mod_inverse_pow2(odd_part, width);
    let (u, mut inv) = fresh_replacement(ctx, result_sort, "bv/mul-even-const")?;
    let kept = ctx.arena().extract(width - shift - 1, 0, u)?;
    let zeros = ctx.arena().bv_const(shift, 0)?;
    inv.replacement = ctx.arena().concat(kept, zeros)?;
    inv.compound = true;
    let inv_const = ctx.arena().bv_const(width, inverse)?;
    let def = ctx.arena().bv_mul(inv_const, u)?;
    inv.defs.push((x, def));
    Ok(Some(inv))
}

/// Shifts and divisions with **both** operands unconstrained: pin the second to
/// the operator's neutral value (`0` for a shift, `1` for a division) so the
/// first passes through. One free operand is not enough — neither operator is
/// surjective in its first argument alone.
fn invert_bv_binary_both(
    ctx: &mut InverterCtx<'_>,
    op: Op,
    args: &[TermId],
    result_sort: Sort,
) -> Result<Option<Inversion>, IrError> {
    if !all_unconstrained(ctx, args) {
        return Ok(None);
    }
    let Some(syms) = symbols_of(ctx, args) else {
        return Ok(None);
    };
    let Sort::BitVec(width) = result_sort else {
        return Ok(None);
    };
    let (rule, neutral) = match op {
        Op::BvUdiv | Op::BvSdiv => ("bv/div-both", 1u128),
        _ => ("bv/shift-both", 0u128),
    };
    let (u, mut inv) = fresh_replacement(ctx, result_sort, rule)?;
    let neutral = ctx.arena().bv_const(width, neutral)?;
    inv.defs.push((syms[0], u));
    inv.defs.push((syms[1], neutral));
    Ok(Some(inv))
}

/// The eight bit-vector order atoms.
///
/// **This is the second wrong-`sat` corner.** `v <u 000` is unsat, yet a naive
/// rule would replace it by a fresh Boolean and report sat: unlike `Int`, a
/// bit-vector order is bounded, so a free operand does **not** make the atom a
/// free Boolean at the domain boundary. Every rule therefore folds the missing
/// case into the replacement as an explicit side condition:
///
/// | atom | replacement | recovered `x` |
/// |---|---|---|
/// | `x <  t` | `u ∧ t ≠ MIN` | `ite(r, MIN, t)` |
/// | `x <= t` | `u ∨ t = MAX` | `ite(r, t, t+1)` |
/// | `t <  x` | `u ∧ t ≠ MAX` | `ite(r, MAX, t)` |
/// | `t <= x` | `u ∨ t = MIN` | `ite(r, t, t−1)` |
///
/// where `r` is the whole replacement term, `MIN`/`MAX` are the bounds of the
/// relevant (unsigned or signed) order, and the `t±1` branches are reached only
/// when the side condition ruled out the wrapping case.
fn invert_bv_cmp(
    ctx: &mut InverterCtx<'_>,
    op: Op,
    args: &[TermId],
    idx: usize,
    x: SymbolId,
) -> Result<Option<Inversion>, IrError> {
    let Sort::BitVec(width) = ctx.arena_ref().sort_of(args[idx]) else {
        return Ok(None);
    };
    if width > max_narrow_bv_width() {
        return Ok(None);
    }
    let signed = matches!(op, Op::BvSlt | Op::BvSle | Op::BvSgt | Op::BvSge);
    let (strict, x_is_lower) = match (op, idx) {
        (Op::BvUlt | Op::BvSlt, 0) | (Op::BvUgt | Op::BvSgt, 1) => (true, true),
        (Op::BvUlt | Op::BvSlt, 1) | (Op::BvUgt | Op::BvSgt, 0) => (true, false),
        (Op::BvUle | Op::BvSle, 0) | (Op::BvUge | Op::BvSge, 1) => (false, true),
        (Op::BvUle | Op::BvSle, 1) | (Op::BvUge | Op::BvSge, 0) => (false, false),
        _ => return Ok(None),
    };
    let t = args[1 - idx];
    let (min_value, max_value) = bv_bounds(width, signed);
    let rule = match (strict, x_is_lower, signed) {
        (true, true, false) => "bv/ult-lhs",
        (true, false, false) => "bv/ult-rhs",
        (false, true, false) => "bv/ule-lhs",
        (false, false, false) => "bv/ule-rhs",
        (true, true, true) => "bv/slt-lhs",
        (true, false, true) => "bv/slt-rhs",
        (false, true, true) => "bv/sle-lhs",
        (false, false, true) => "bv/sle-rhs",
    };
    let (u, mut inv) = fresh_replacement(ctx, Sort::Bool, rule)?;
    let min_term = ctx.arena().bv_const(width, min_value)?;
    let max_term = ctx.arena().bv_const(width, max_value)?;
    // The extreme the atom must avoid, and the replacement's side condition.
    let (replacement, when_true, when_false) = if strict {
        // `x < t` needs `t != MIN`; `t < x` needs `t != MAX`.
        let bound = if x_is_lower { min_term } else { max_term };
        let eq_bound = ctx.arena().eq(t, bound)?;
        let ne_bound = ctx.arena().not(eq_bound)?;
        let r = ctx.arena().and(u, ne_bound)?;
        (r, bound, t)
    } else {
        // `x <= t` is unconditionally true when `t == MAX`; `t <= x` when
        // `t == MIN`.
        let bound = if x_is_lower { max_term } else { min_term };
        let eq_bound = ctx.arena().eq(t, bound)?;
        let r = ctx.arena().or(u, eq_bound)?;
        let one = ctx.arena().bv_const(width, 1)?;
        let stepped = if x_is_lower {
            ctx.arena().bv_add(t, one)?
        } else {
            ctx.arena().bv_sub(t, one)?
        };
        (r, t, stepped)
    };
    let def = ctx.arena().ite(replacement, when_true, when_false)?;
    inv.replacement = replacement;
    inv.compound = true;
    inv.defs.push((x, def));
    Ok(Some(inv))
}

/// The least and greatest values of the unsigned or signed `width`-bit order,
/// as unsigned bit patterns. `width <= 128` is a precondition.
fn bv_bounds(width: u32, signed: bool) -> (u128, u128) {
    let mask = if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    };
    if signed {
        // MIN is `100…0`, MAX is `011…1`.
        let sign_bit = 1u128 << (width - 1);
        (sign_bit & mask, (sign_bit - 1) & mask)
    } else {
        (0, mask)
    }
}

/// The multiplicative inverse of an odd `c` modulo `2^width` (`width ≤ 128`), by
/// 2-adic Newton iteration `x ← x·(2 − c·x)`: each step doubles the number of
/// correct low bits, and `x₀ = c` is already correct mod 8, so seven steps cover
/// 128 bits.
#[must_use]
pub fn mod_inverse_pow2(c: u128, width: u32) -> u128 {
    let m = if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    };
    let c = c & m;
    let mut inv = c;
    for _ in 0..7 {
        inv = inv.wrapping_mul(2u128.wrapping_sub(c.wrapping_mul(inv))) & m;
    }
    inv & m
}

/// Collects the symbols occurring free in `term` (memoized so a shared DAG is
/// walked once).
///
/// The walk is an explicit worklist, not native recursion: its depth would
/// otherwise be the term DAG's *depth*, so a deep operand chain — e.g. a
/// left-associated `(+ (+ (+ x 1) 1) 1)` spine, which SMT-LIB sources produce
/// routinely — aborted the process with a stack overflow instead of letting the
/// solver report a first-class `unknown` (compare `fcc8760d`). `seen` keeps the
/// walk linear in DAG size either way.
pub(crate) fn free_symbols(
    arena: &TermArena,
    term: TermId,
    out: &mut HashSet<SymbolId>,
    seen: &mut HashSet<TermId>,
) {
    let mut work = vec![term];
    while let Some(t) = work.pop() {
        if !seen.insert(t) {
            continue;
        }
        match arena.node(t) {
            TermNode::Symbol(s) => {
                out.insert(*s);
            }
            TermNode::App { args, .. } => {
                work.extend(args.iter().copied());
            }
            _ => {}
        }
    }
}

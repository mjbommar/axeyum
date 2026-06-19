//! Real relaxation of an integer query (G3): the integers are a subset of the
//! reals, so an integer query has **no model** whenever its *real relaxation* —
//! every `Int` variable / constant / operator faithfully reinterpreted over the
//! reals — has no model. This makes integer-nonlinear goals that are unsat for
//! sign reasons (e.g. `x*x < 0`, `x*x + 1 <= 0`) refutable through the NRA sign
//! rules, which the bounded integer bit-blaster only ever reports as `unknown`.
//!
//! The translation is a *faithful* reinterpretation (integer solutions ⊆ real
//! solutions): each `Int` symbol maps to a fresh `Real` symbol (the **same** int
//! symbol to the **same** real symbol, deterministically by declaration index),
//! `int_const(n)` to `real_const(n)`, and the integer linear/comparison operators
//! to their real counterparts; Boolean connectives, `Eq`, and `Ite` recurse
//! unchanged. Any integer construct with no clean real analogue
//! (`div`/`mod`/`abs`/`divisible`/`bv2nat`/`int2bv`/`to_int`/`is_int`) or any
//! non-arithmetic subterm (bit-vector, array, uninterpreted function, datatype,
//! quantifier) **aborts the whole relaxation** — it is never guessed — so the
//! caller proceeds on the original query unchanged.
//!
//! Because a real model need not be integral, this path is used **only** to
//! derive `unsat`: real-unsat ⇒ int-unsat is sound; real-sat says nothing about
//! the integer query. The relaxation is built on a clone of the caller's arena,
//! so no fresh symbol or rewritten term leaks back.

use std::collections::HashMap;

use axeyum_ir::{Op, Rational, Sort, SymbolId, TermArena, TermId, TermNode};

use crate::backend::{CheckResult, SolverConfig, SolverError};

/// Tries to refute an integer query by its **real relaxation**: build the
/// faithful real reinterpretation of every assertion and run [`crate::check_with_nra`]
/// on it. Returns `Ok(true)` only when the relaxation is **provably** `unsat`
/// (which transfers soundly to the original integer query, integers ⊆ reals);
/// `Ok(false)` when the relaxation could not be built (a construct with no clean
/// real analogue) or did not refute.
///
/// Soundness: only `Unsat` of the relaxation ever yields `true`. A real model is
/// never returned (and need not be integral), so this can never produce a wrong
/// `sat` and never strengthens a currently-decided result — it only turns a prior
/// `unknown` into `unsat` for the real-refutable integer cases.
///
/// The relaxation declares fresh `!relax.*` real symbols and is only used to
/// derive `unsat`, so it runs on an isolated **clone** of the arena: nothing
/// leaks back into the caller's arena or any model.
///
/// # Errors
///
/// Returns [`SolverError`] from the underlying NRA engine.
pub fn refute_int_via_real_relaxation(
    arena: &TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<bool, SolverError> {
    let mut scratch = arena.clone();
    let mut relax = Relax::default();
    let mut relaxed = Vec::with_capacity(assertions.len());
    for &a in assertions {
        match relax.translate(&mut scratch, a)? {
            Some(t) => relaxed.push(t),
            // An assertion has no clean real analogue: abort the whole relaxation.
            None => return Ok(false),
        }
    }
    // The relaxation must mention at least one relaxed integer construct to be
    // worth the NRA call; a purely-real query is already on its native path.
    if relax.int_to_real.is_empty() {
        return Ok(false);
    }
    Ok(matches!(
        crate::nra::check_with_nra(&mut scratch, &relaxed, config)?,
        CheckResult::Unsat
    ))
}

/// Orders the two operands of a commutative operator by interned `TermId` index so
/// that `op(a, b)` and `op(b, a)` build the *same* node. Deterministic (a `TermId`
/// index is stable within an arena) and sound for `+`/`*` over the reals, which
/// genuinely commute.
fn sort_commutative(a: TermId, b: TermId) -> (TermId, TermId) {
    if a.index() <= b.index() {
        (a, b)
    } else {
        (b, a)
    }
}

/// Carries the deterministic `Int` symbol → fresh `Real` symbol mapping and a
/// memo of translated terms.
#[derive(Default)]
struct Relax {
    /// Original integer symbol → fresh real symbol (same int symbol → same real
    /// symbol, so a contradiction on the *same* integer value is preserved).
    int_to_real: HashMap<SymbolId, SymbolId>,
    /// Translated-term memo over the scratch arena.
    memo: HashMap<TermId, Option<TermId>>,
}

impl Relax {
    /// The fresh real symbol standing for `int_sym` (created on first use).
    fn real_of_int(
        &mut self,
        arena: &mut TermArena,
        int_sym: SymbolId,
    ) -> Result<TermId, SolverError> {
        if let Some(&r) = self.int_to_real.get(&int_sym) {
            return Ok(arena.var(r));
        }
        let name = format!("!relax.{}", int_sym.index());
        let r = arena
            .declare(&name, Sort::Real)
            .map_err(|e| SolverError::Backend(e.to_string()))?;
        self.int_to_real.insert(int_sym, r);
        Ok(arena.var(r))
    }

    /// Translates `t` to its faithful real analogue, or `None` if `t` contains a
    /// construct with no clean real reinterpretation (the caller then aborts the
    /// whole relaxation).
    fn translate(
        &mut self,
        arena: &mut TermArena,
        t: TermId,
    ) -> Result<Option<TermId>, SolverError> {
        if let Some(&cached) = self.memo.get(&t) {
            return Ok(cached);
        }
        let out = self.translate_uncached(arena, t)?;
        self.memo.insert(t, out);
        Ok(out)
    }

    fn translate_uncached(
        &mut self,
        arena: &mut TermArena,
        t: TermId,
    ) -> Result<Option<TermId>, SolverError> {
        let err = |e: axeyum_ir::IrError| SolverError::Backend(e.to_string());
        let node = arena.node(t).clone();
        let out = match node {
            // Boolean and real constants pass through unchanged; a real subterm of
            // a mixed real/int query stays real.
            TermNode::BoolConst(_) | TermNode::RealConst(_) => t,
            // An integer constant `n` reinterprets as the real number `n`.
            TermNode::IntConst(n) => arena.real_const(Rational::integer(n)),
            // Bit-vector constants have no real analogue: abort.
            TermNode::BvConst { .. } | TermNode::WideBvConst(_) => return Ok(None),
            TermNode::Symbol(s) => match arena.sort_of(t) {
                // An integer symbol becomes its fresh real surrogate.
                Sort::Int => self.real_of_int(arena, s)?,
                // Real and Bool symbols carry through unchanged.
                Sort::Real | Sort::Bool => t,
                // Bit-vector / array / datatype symbols: no real analogue.
                _ => return Ok(None),
            },
            TermNode::App { op, args } => {
                // Translate the operands first; any abort propagates.
                let mut low = Vec::with_capacity(args.len());
                for &a in &args {
                    match self.translate(arena, a)? {
                        Some(t) => low.push(t),
                        None => return Ok(None),
                    }
                }
                match op {
                    // Integer linear operators → their real counterparts (a faithful
                    // reinterpretation over the reals).
                    Op::IntNeg => arena.real_neg(low[0]).map_err(err)?,
                    // `+` and `*` are commutative over the reals, so canonicalize the
                    // operand order (by interned `TermId` index — deterministic and
                    // stable in the scratch arena) before building the real node. This
                    // makes `a+b`/`b+a` and `a*b`/`b*a` translate to the **same** real
                    // term, so a commutativity disequality `a*b ≠ b*a` relaxes to
                    // `p ≠ p` ≡ `false` and is refuted by the NRA layer. Sound: real
                    // `+`/`*` genuinely commute, so the canonicalized term denotes the
                    // same real value in every model.
                    Op::IntAdd => {
                        let (l, r) = sort_commutative(low[0], low[1]);
                        arena.real_add(l, r).map_err(err)?
                    }
                    Op::IntSub => arena.real_sub(low[0], low[1]).map_err(err)?,
                    Op::IntMul => {
                        let (l, r) = sort_commutative(low[0], low[1]);
                        arena.real_mul(l, r).map_err(err)?
                    }
                    Op::IntLt => arena.real_lt(low[0], low[1]).map_err(err)?,
                    Op::IntLe => arena.real_le(low[0], low[1]).map_err(err)?,
                    Op::IntGt => arena.real_gt(low[0], low[1]).map_err(err)?,
                    Op::IntGe => arena.real_ge(low[0], low[1]).map_err(err)?,
                    // Real operators and the sort-polymorphic Boolean structure
                    // (`Eq`/`Ite` over already-translated operands, the connectives)
                    // rebuild over the translated operands unchanged.
                    Op::Eq
                    | Op::Ite
                    | Op::BoolAnd
                    | Op::BoolOr
                    | Op::BoolNot
                    | Op::BoolXor
                    | Op::BoolImplies
                    | Op::RealNeg
                    | Op::RealAdd
                    | Op::RealSub
                    | Op::RealMul
                    | Op::RealLt
                    | Op::RealLe
                    | Op::RealGt
                    | Op::RealGe => axeyum_rewrite::build_app(arena, op, &low).map_err(err)?,
                    // Everything else has no clean / order-faithful real analogue:
                    // integer div/mod/abs (and `divisible`, encoded via mod),
                    // int↔real/bv coercions, bit-vectors, arrays, uninterpreted
                    // functions, datatypes, quantifiers. Abort the relaxation.
                    _ => return Ok(None),
                }
            }
        };
        Ok(Some(out))
    }
}

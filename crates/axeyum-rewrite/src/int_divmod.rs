//! Eliminate integer Euclidean `div`/`mod` (by a **constant** divisor) and `abs`
//! into linear constraints, so the *complete* `QF_LIA` simplex/DPLL path decides
//! them (sound for both `sat` and `unsat`) — not only the bounded, sat-only
//! integer bit-blaster.
//!
//! For `q = (div a c)` and `r = (mod a c)` with `c ≠ 0` a constant, the
//! Euclidean pair is the unique `(q, r)` with `a = c·q + r` and `0 ≤ r < |c|`.
//! Replacing the terms with fresh variables `q, r` and adding those linear
//! constraints is therefore an **exact, equisatisfiable** encoding (not a
//! relaxation): a simplex `unsat` transfers soundly to the original. `c = 0`
//! uses the in-tree convention (`div a 0 = 0`, `mod a 0 = a`). `abs a` becomes a
//! fresh `v` with `v ≥ a ∧ v ≥ −a ∧ (v = a ∨ v = −a)` (i.e. `v = |a|`); the
//! disjunction needs the Boolean-structured (DPLL) integer path.

use std::collections::HashMap;

use axeyum_ir::{IrError, Op, Sort, TermArena, TermId, TermNode};

use crate::replace_subterms;

/// Rewrites every `div`/`mod`-by-constant and `abs` in `assertions` into fresh
/// variables plus their defining linear constraints, returning the linearized
/// assertion list (the originals with the terms substituted, followed by the new
/// constraints). If none are present, the input is returned unchanged.
///
/// # Errors
///
/// Returns [`IrError`] from the IR builders (e.g. a fresh-symbol conflict).
pub fn eliminate_int_divmod(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<Vec<TermId>, IrError> {
    let mut collector = Collector::default();
    for &a in assertions {
        collector.scan(arena, a);
    }
    if collector.divmod.is_empty() && collector.abs.is_empty() {
        return Ok(assertions.to_vec());
    }

    let mut map: HashMap<TermId, TermId> = HashMap::new();
    let mut constraints: Vec<TermId> = Vec::new();
    let mut fresh = 0u32;

    // div/mod groups, keyed by (dividend, constant divisor).
    for ((dividend, divisor), terms) in collector.divmod {
        if divisor == 0 {
            // SMT-LIB leaves `div`/`mod` by zero UNDERSPECIFIED (any total-function
            // value). Folding to a fixed convention (`div a 0 = 0`, `mod a 0 = a`)
            // is sound for a *witness* but produces a WRONG UNSAT — a solver could
            // refute a formula that is satisfiable by some *other* choice of the
            // free value (e.g. `775 < mod(0,0)` is sat, not `775 < 0`). So each
            // div/mod-by-zero term becomes a FRESH UNCONSTRAINED variable: no
            // constraint forces its value, so it can never be the pivot of an
            // unsat, and a `sat` model whose free value disagrees with the
            // evaluator convention is caught by the ground-evaluator replay
            // (declined to `unknown`, never a wrong verdict).
            for t in terms.div.into_iter().chain(terms.mod_) {
                let v = fresh_int(arena, &mut fresh)?;
                map.insert(t, v);
            }
            continue;
        }
        let q = fresh_int(arena, &mut fresh)?;
        let r = fresh_int(arena, &mut fresh)?;
        for t in terms.div {
            map.insert(t, q);
        }
        for t in terms.mod_ {
            map.insert(t, r);
        }
        // a = c·q + r
        let c_const = arena.int_const(divisor);
        let cq = arena.int_mul(c_const, q)?;
        let cq_r = arena.int_add(cq, r)?;
        constraints.push(arena.eq(dividend, cq_r)?);
        // 0 ≤ r ≤ |c| − 1
        let zero = arena.int_const(0);
        constraints.push(arena.int_le(zero, r)?);
        let hi = arena.int_const(divisor.abs() - 1);
        constraints.push(arena.int_le(r, hi)?);
    }

    // abs groups, keyed by the operand.
    for (operand, terms) in collector.abs {
        let v = fresh_int(arena, &mut fresh)?;
        for t in terms {
            map.insert(t, v);
        }
        let neg = arena.int_neg(operand)?;
        constraints.push(arena.int_ge(v, operand)?); // v ≥ a
        constraints.push(arena.int_ge(v, neg)?); // v ≥ −a
        let v_eq_a = arena.eq(v, operand)?;
        let v_eq_neg = arena.eq(v, neg)?;
        constraints.push(arena.or(v_eq_a, v_eq_neg)?); // v = a ∨ v = −a
    }

    // Substitute the eliminated terms throughout the assertions and constraints
    // (nested div/mod inside a dividend or constraint are handled too).
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    let mut out = Vec::with_capacity(assertions.len() + constraints.len());
    for &a in assertions {
        out.push(replace_subterms(arena, a, &map, &mut memo)?);
    }
    for c in constraints {
        out.push(replace_subterms(arena, c, &map, &mut memo)?);
    }
    Ok(out)
}

fn fresh_int(arena: &mut TermArena, counter: &mut u32) -> Result<TermId, IrError> {
    let name = format!("!divmod_{counter}");
    *counter += 1;
    let sym = arena.declare(&name, Sort::Int)?;
    Ok(arena.var(sym))
}

#[derive(Default)]
struct DivModTerms {
    div: Vec<TermId>,
    mod_: Vec<TermId>,
}

#[derive(Default)]
struct Collector {
    seen: std::collections::HashSet<TermId>,
    divmod: HashMap<(TermId, i128), DivModTerms>,
    abs: HashMap<TermId, Vec<TermId>>,
}

impl Collector {
    fn scan(&mut self, arena: &TermArena, term: TermId) {
        if !self.seen.insert(term) {
            return;
        }
        let TermNode::App { op, args } = arena.node(term) else {
            return;
        };
        let (op, args) = (*op, args.clone());
        match op {
            Op::IntDiv | Op::IntMod => {
                if let TermNode::IntConst(c) = arena.node(args[1]) {
                    let entry = self.divmod.entry((args[0], *c)).or_default();
                    if op == Op::IntDiv {
                        entry.div.push(term);
                    } else {
                        entry.mod_.push(term);
                    }
                }
            }
            Op::IntAbs => self.abs.entry(args[0]).or_default().push(term),
            _ => {}
        }
        for arg in args {
            self.scan(arena, arg);
        }
    }
}

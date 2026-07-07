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
//! (div/mod by a constant zero) is **UNDERSPECIFIED** in SMT-LIB — any
//! total-function value — so it maps to a **fresh unconstrained variable**,
//! never a fixed convention: committing to `div a 0 = 0` would be a valid
//! *witness* but an unsound *unsat* (a formula sat under a different free value
//! would be wrongly refuted — the P0 regressed by `a946f925`, fixed by
//! `52f3b1d1`). `abs a` becomes a
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
    // Zero-divisor groups retained for the pairwise Ackermann congruence pass.
    let mut zero_groups: Vec<ZeroGroup> = Vec::new();

    // div/mod groups, keyed by (dividend, constant divisor).
    for ((dividend, divisor), terms) in collector.divmod {
        if divisor == 0 {
            // SMT-LIB leaves `div`/`mod` by zero UNDERSPECIFIED (any total-function
            // value). Folding to a fixed convention (`div a 0 = 0`, `mod a 0 = a`)
            // is sound for a *witness* but produces a WRONG UNSAT — a solver could
            // refute a formula that is satisfiable by some *other* choice of the
            // free value (e.g. `775 < mod(0,0)` is sat, not `775 < 0`). So each
            // div/mod-by-zero *group* (keyed by dividend) becomes a fresh
            // unconstrained variable — the underspecified free value.
            //
            // The free values are nevertheless kept **congruent** across groups
            // (see the pairwise pass after this loop): `div`/`mod` are total binary
            // functions, so `div a 0` and `div b 0` must be EQUAL when `a = b`, for
            // whatever the underspecified zero-divisor value is. Without that, the
            // fresh-per-group relaxation is unsound for *sat*: two zero-divisor
            // terms whose dividends are provably equal could be assigned different
            // values, yielding a model that is not a real SMT model (a WRONG SAT —
            // the `div (mod (2x) 3) 0 ≠ div (mod (3−x) 3) 0` shape, unsat because
            // `2x ≡ 3−x (mod 3)`). One fresh var per group (not per term) already
            // shares within a group; the congruence lemmas share across groups.
            let has_div = !terms.div.is_empty();
            let has_mod = !terms.mod_.is_empty();
            let q0 = if has_div {
                let v = fresh_int(arena, &mut fresh)?;
                for t in terms.div {
                    map.insert(t, v);
                }
                Some(v)
            } else {
                None
            };
            let r0 = if has_mod {
                let v = fresh_int(arena, &mut fresh)?;
                for t in terms.mod_ {
                    map.insert(t, v);
                }
                Some(v)
            } else {
                None
            };
            zero_groups.push(ZeroGroup {
                dividend,
                q: q0,
                r: r0,
            });
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

    // Pairwise Ackermann congruence over the zero-divisor groups. `div`/`mod` are
    // total binary functions and the divisor is the constant `0` in every group, so
    // for groups `(a, 0)` and `(c, 0)` the lemma `a = c → v_a = v_c` (the div
    // quotients, and separately the mod remainders) is a valid consequence for
    // whatever the underspecified `_/0` value is. This makes the fresh-per-group
    // relaxation sound for *sat* (a satisfying assignment now induces a consistent
    // total `_/0` function — no wrong sat) while remaining monotone (the true model
    // satisfies every lemma, so no wrong unsat, and a lone `mod(0,0)` with no
    // congruence partner stays free — the P0 `775 < mod(0,0)` is still not refuted).
    // Bounded by `MAX_CONGRUENCE_GROUPS` to keep the pass `O(k²)` small.
    if zero_groups.len() <= MAX_CONGRUENCE_GROUPS {
        for i in 0..zero_groups.len() {
            for j in (i + 1)..zero_groups.len() {
                let (gi, gj) = (&zero_groups[i], &zero_groups[j]);
                let same_dividend = arena.eq(gi.dividend, gj.dividend)?;
                if let (Some(qi), Some(qj)) = (gi.q, gj.q) {
                    let q_eq = arena.eq(qi, qj)?;
                    constraints.push(arena.implies(same_dividend, q_eq)?);
                }
                if let (Some(ri), Some(rj)) = (gi.r, gj.r) {
                    let r_eq = arena.eq(ri, rj)?;
                    constraints.push(arena.implies(same_dividend, r_eq)?);
                }
            }
        }
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

/// A zero-divisor `div`/`mod` group: the (shared) dividend and the fresh
/// quotient / remainder variables (each `None` when the group has no such term).
/// Retained for the pairwise Ackermann congruence pass over `_/0` terms.
struct ZeroGroup {
    dividend: TermId,
    q: Option<TermId>,
    r: Option<TermId>,
}

/// Upper bound on the number of *distinct zero-divisor dividends* over which the
/// `O(k²)` eager Ackermann congruence lemmas are emitted. Below it (every realistic
/// shape — a formula with >48 syntactically-distinct `_/0` dividends is
/// pathological) the relaxation is fully congruence-closed, so a relaxation `sat`
/// is a genuine model. This is a strict soundness improvement over the prior
/// fresh-per-term relaxation (which was *not* congruence-closed at any size and
/// could report a wrong `sat`); the follow-up to make it unconditional is to route
/// `_/0` through the lazy-CEGAR UF congruence path. `unsat` transfers soundly at
/// every size (the relaxation only enlarges the model space).
const MAX_CONGRUENCE_GROUPS: usize = 48;

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

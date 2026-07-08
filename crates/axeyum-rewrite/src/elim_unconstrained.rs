//! Unconstrained-variable elimination (Track 1, P1.2 / T1.2.4).
//!
//! A variable that occurs **exactly once** in the whole assertion forest is
//! *unconstrained*: nothing else pins it, so as it ranges over all values, any
//! invertible operation applied to it ranges over all values too. So if `x`
//! occurs once and its sole parent is an invertible bit-vector op
//! `p = op(x, w…)` (`bvadd`/`bvsub`/`bvxor`/`bvnot`/`bvneg`, or `bvmul` by an odd
//! constant — invertible mod `2^w`), then `p` itself is
//! unconstrained: replace it everywhere by a single fresh variable `u` and drop
//! the operation. This is Z3's `elim_unconstr` tactic — it peels expensive
//! operator layers off single-use variables before bit-blasting.
//!
//! **Model-sound** via the [`ModelReconstructionTrail`]. For each elimination we
//! record `x := op⁻¹(u, w…)`: given the reduced model's value for `u`, evaluating
//! the inverse reproduces an `x` with `op(x, w…) = u`, so every original
//! assertion that mentioned `p` is satisfied exactly as the reduced one was. An
//! operand `w` that survives nowhere in the reduced problem (it only fed into the
//! eliminated `p`) is genuinely unconstrained; we default it to `0` — `x` is
//! computed against that value, so the inverse identity still holds. Reverse
//! replay (defaults appended last ⇒ reconstructed first) resolves every
//! dependency, exactly as for [`crate::solve_eqs`].
//!
//! **Terminating:** each elimination replaces an operator node `p` in the
//! assertions with a leaf `u`, strictly reducing the assertion operator count;
//! the inverse term lives in the trail, never re-entering the assertions.
//! Peeling can chain (`u`'s parent may now be a single-use invertible op).
//!
//! Scope: the invertible operators above. `bvmul` fires only when the other
//! factor is an odd constant (then it has a 2-adic inverse); `bvmul` by an even
//! or non-constant factor, and the non-injective `bvand`/`bvor`/`bvudiv`/…, are
//! left alone — refining them is not sound by simple inversion.

use std::collections::{HashMap, HashSet};

use axeyum_ir::{
    Assignment, IrError, Op, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval,
};

use crate::canonical::replace_subterms;
use crate::reconstruct::ModelReconstructionTrail;

/// The result of [`elim_unconstrained`]: the operator-reduced assertions plus the
/// trail that rebuilds the eliminated (and incidentally-orphaned) variables.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnconstrainedElimination {
    assertions: Vec<TermId>,
    trail: ModelReconstructionTrail,
    eliminated: usize,
}

impl UnconstrainedElimination {
    /// The reduced assertions (single-use invertible-op layers replaced by fresh
    /// unconstrained variables).
    #[must_use]
    pub fn assertions(&self) -> &[TermId] {
        &self.assertions
    }

    /// The model-reconstruction trail for the eliminated/orphaned variables.
    #[must_use]
    pub fn trail(&self) -> &ModelReconstructionTrail {
        &self.trail
    }

    /// Number of unconstrained operator layers eliminated (excludes the default
    /// assignments appended for orphaned operands).
    #[must_use]
    pub fn eliminated(&self) -> usize {
        self.eliminated
    }

    /// Consumes into `(reduced assertions, trail)`.
    #[must_use]
    pub fn into_parts(self) -> (Vec<TermId>, ModelReconstructionTrail) {
        (self.assertions, self.trail)
    }
}

/// Reference counts and the unique parent (node + argument index) of every term
/// reachable from `roots`. A term referenced exactly once has a single,
/// well-defined parent recorded here.
struct Occurrences {
    refs: HashMap<TermId, usize>,
    parent: HashMap<TermId, (TermId, usize)>,
}

/// Walks the shared DAG from the roots once, counting how many argument slots
/// reference each node and remembering the parent edge of single-use nodes.
fn occurrences(arena: &TermArena, roots: &[TermId]) -> Occurrences {
    let mut refs: HashMap<TermId, usize> = HashMap::new();
    let mut parent: HashMap<TermId, (TermId, usize)> = HashMap::new();
    let mut visited: HashSet<TermId> = HashSet::new();
    let mut stack: Vec<TermId> = Vec::new();

    for &root in roots {
        // Count the root reference itself, so a term that is *also* a top-level
        // assertion is never treated as single-occurrence.
        *refs.entry(root).or_insert(0) += 1;
        if visited.insert(root) {
            stack.push(root);
        }
    }
    while let Some(term) = stack.pop() {
        if let TermNode::App { args, .. } = arena.node(term) {
            let args = args.clone();
            for (i, arg) in args.iter().enumerate() {
                *refs.entry(*arg).or_insert(0) += 1;
                parent.insert(*arg, (term, i));
                if visited.insert(*arg) {
                    stack.push(*arg);
                }
            }
        }
    }
    Occurrences { refs, parent }
}

/// Collects the symbols occurring free in `term` (memoized so a shared DAG is
/// walked once).
fn free_symbols(
    arena: &TermArena,
    term: TermId,
    out: &mut HashSet<SymbolId>,
    seen: &mut HashSet<TermId>,
) {
    if !seen.insert(term) {
        return;
    }
    match arena.node(term) {
        TermNode::Symbol(s) => {
            out.insert(*s);
        }
        TermNode::App { args, .. } => {
            let args = args.clone();
            for a in args {
                free_symbols(arena, a, out, seen);
            }
        }
        _ => {}
    }
}

/// Whether `op` (with `arity` arguments, `x` at `idx`) is invertible for the
/// `x` operand by [`invert`].
fn invertible(op: Op, arity: usize, idx: usize) -> bool {
    match op {
        Op::BvNot | Op::BvNeg => arity == 1,
        Op::BvAdd | Op::BvXor => arity >= 2,
        Op::BvSub => arity == 2 && (idx == 0 || idx == 1),
        _ => false,
    }
}

/// Builds `op⁻¹(u, others…)` solving `p = op(args…)` for the operand at `idx`,
/// where `u` stands for the (now fresh) value of `p`. Assumes
/// [`invertible`]`(op, args.len(), idx)`.
fn invert(
    arena: &mut TermArena,
    op: Op,
    args: &[TermId],
    idx: usize,
    u: TermId,
) -> Result<TermId, IrError> {
    let others: Vec<TermId> = args
        .iter()
        .enumerate()
        .filter_map(|(i, &a)| (i != idx).then_some(a))
        .collect();
    let inverse = match op {
        // p = ~x  ⇒  x = ~u ;  p = -x  ⇒  x = -u
        Op::BvNot => arena.bv_not(u)?,
        Op::BvNeg => arena.bv_neg(u)?,
        // p = Σ args  ⇒  x = u - Σ others   (bvadd associative/commutative)
        Op::BvAdd => {
            let mut sum = others[0];
            for &o in &others[1..] {
                sum = arena.bv_add(sum, o)?;
            }
            arena.bv_sub(u, sum)?
        }
        // p = ⊕ args  ⇒  x = u ⊕ (⊕ others)   (bvxor self-inverse)
        Op::BvXor => {
            let mut acc = others[0];
            for &o in &others[1..] {
                acc = arena.bv_xor(acc, o)?;
            }
            arena.bv_xor(u, acc)?
        }
        // p = a - b: solve for whichever side is x.
        Op::BvSub if idx == 0 => arena.bv_add(u, args[1])?, // u = x - b ⇒ x = u + b
        Op::BvSub => arena.bv_sub(args[0], u)?,             // u = a - x ⇒ x = a - u
        _ => unreachable!("invert called on a non-invertible op"),
    };
    Ok(inverse)
}

/// A single eliminable layer: the single-use variable `sym`, its sole parent
/// operator node `parent`, the fresh replacement `u`, and the inverse term
/// recovering `sym` from `u`.
struct Elimination {
    sym: SymbolId,
    parent: TermId,
    u: TermId,
    inverse: TermId,
}

/// Finds the lowest-`TermId` single-occurrence bit-vector variable whose sole
/// parent is an invertible operator, mints its fresh replacement `u`
/// (`!unconstr!N`, outside the SMT-LIB user identifier space), and builds the
/// inverse.
fn find_elimination(
    arena: &mut TermArena,
    occ: &Occurrences,
    next_fresh: &mut u64,
) -> Result<Option<Elimination>, IrError> {
    // Deterministic: single-occurrence variable nodes, ordered by TermId.
    let mut single_use: Vec<TermId> = occ
        .refs
        .iter()
        .filter_map(|(&t, &n)| {
            (n == 1 && matches!(arena.node(t), TermNode::Symbol(_))).then_some(t)
        })
        .collect();
    single_use.sort_by_key(|t| t.index());

    for var in single_use {
        let TermNode::Symbol(sym) = *arena.node(var) else {
            continue;
        };
        if !matches!(arena.sort_of(var), Sort::BitVec(_)) {
            continue;
        }
        let Some(&(parent, idx)) = occ.parent.get(&var) else {
            continue;
        };
        let TermNode::App { op, args } = arena.node(parent) else {
            continue;
        };
        let (op, args) = (*op, args.clone());
        let Sort::BitVec(width) = arena.sort_of(parent) else {
            continue;
        };

        // `bvmul` by an odd ground constant is invertible: `p = c·x ⇒ x = c⁻¹·u`,
        // with `c⁻¹` the 2-adic inverse mod `2^width`. This peels a multiplier
        // layer off a single-use variable when the other factor is an odd
        // constant — the exact shape that otherwise bit-blasts to a large CNF.
        if op == Op::BvMul && args.len() == 2 {
            if let Some(inv_value) = odd_factor_inverse(arena, args[1 - idx], width) {
                let u = mint_fresh(arena, width, next_fresh)?;
                let inv_const = arena.bv_const(width, inv_value)?;
                let inverse = arena.bv_mul(inv_const, u)?;
                return Ok(Some(Elimination {
                    sym,
                    parent,
                    u,
                    inverse,
                }));
            }
            continue;
        }

        if !invertible(op, args.len(), idx) {
            continue;
        }
        let u = mint_fresh(arena, width, next_fresh)?;
        let inverse = invert(arena, op, &args, idx, u)?;
        return Ok(Some(Elimination {
            sym,
            parent,
            u,
            inverse,
        }));
    }
    Ok(None)
}

/// Mints a fresh `width`-bit replacement variable (`!unconstr!N`, outside the
/// SMT-LIB user identifier space).
fn mint_fresh(arena: &mut TermArena, width: u32, next_fresh: &mut u64) -> Result<TermId, IrError> {
    let name = format!("!unconstr!{next_fresh}");
    *next_fresh += 1;
    let sym = arena.declare_internal(&name, Sort::BitVec(width))?;
    Ok(arena.var(sym))
}

/// If `term` is an odd ground bit-vector constant of `width` bits, returns its
/// multiplicative inverse mod `2^width`; otherwise `None` (a non-ground operand,
/// a wider value, or an even constant — none invertible by this rule).
fn odd_factor_inverse(arena: &TermArena, term: TermId, width: u32) -> Option<u128> {
    match eval(arena, term, &Assignment::new()) {
        Ok(Value::Bv { width: w, value }) if w == width && value & 1 == 1 => {
            Some(mod_inverse_pow2(value, width))
        }
        _ => None,
    }
}

/// The multiplicative inverse of an odd `c` modulo `2^width` (`width ≤ 128`), by
/// 2-adic Newton iteration `x ← x·(2 − c·x)`: each step doubles the number of
/// correct low bits, and `x₀ = c` is already correct mod 8, so seven steps cover
/// 128 bits.
fn mod_inverse_pow2(c: u128, width: u32) -> u128 {
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

/// Eliminates unconstrained single-use invertible-operator layers (see module
/// docs).
///
/// # Errors
///
/// Returns [`IrError`] only if rebuilding an inverse or substituted term fails
/// sort checking, which cannot happen here (every rewrite preserves the operand
/// width).
pub fn elim_unconstrained(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<UnconstrainedElimination, IrError> {
    let mut current: Vec<TermId> = assertions.to_vec();
    let mut trail = ModelReconstructionTrail::new();
    let mut next_fresh: u64 = 0;
    let mut eliminated = 0usize;
    // Locally tracked so we can default any operand orphaned by the rewrites.
    let mut defined: HashSet<SymbolId> = HashSet::new();
    let mut inverse_terms: Vec<TermId> = Vec::new();

    loop {
        let occ = occurrences(arena, &current);
        let Some(elim) = find_elimination(arena, &occ, &mut next_fresh)? else {
            break;
        };
        // Record x := op⁻¹(u, w…), then replace the parent operator node by the
        // fresh unconstrained variable everywhere it occurs.
        trail.define(elim.sym, elim.inverse);
        defined.insert(elim.sym);
        inverse_terms.push(elim.inverse);
        eliminated += 1;
        let replacements = HashMap::from([(elim.parent, elim.u)]);
        let mut memo: HashMap<TermId, TermId> = HashMap::new();
        for a in &mut current {
            *a = replace_subterms(arena, *a, &replacements, &mut memo)?;
        }
    }

    // Default any operand that fed only into an eliminated layer: it survives
    // nowhere in the reduced problem and is not itself an eliminated variable, so
    // it is genuinely unconstrained and the inverse identity holds for any value.
    let mut survivors: HashSet<SymbolId> = HashSet::new();
    let mut seen = HashSet::new();
    for &a in &current {
        free_symbols(arena, a, &mut survivors, &mut seen);
    }
    let mut needed: HashSet<SymbolId> = HashSet::new();
    let mut def_seen = HashSet::new();
    for &def in &inverse_terms {
        free_symbols(arena, def, &mut needed, &mut def_seen);
    }
    let mut orphans: Vec<SymbolId> = needed
        .into_iter()
        .filter(|s| !survivors.contains(s) && !defined.contains(s))
        .collect();
    orphans.sort_by_key(|s| s.index());
    for sym in orphans {
        let var = arena.var(sym);
        let Sort::BitVec(w) = arena.sort_of(var) else {
            continue;
        };
        let zero = arena.bv_const(w, 0)?;
        trail.define(sym, zero);
    }

    Ok(UnconstrainedElimination {
        assertions: current,
        trail,
        eliminated,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_ir::{Assignment, Value, eval};

    fn bv8(v: u128) -> Value {
        Value::Bv { width: 8, value: v }
    }

    fn assert_satisfies(arena: &TermArena, originals: &[TermId], model: &Assignment) {
        for &a in originals {
            assert_eq!(
                eval(arena, a, model).unwrap(),
                Value::Bool(true),
                "reconstructed model must satisfy original assertion #{}",
                a.index()
            );
        }
    }

    /// Free symbols of the reduced assertions (the survivors a backend models).
    fn survivors(arena: &TermArena, assertions: &[TermId]) -> Vec<SymbolId> {
        let mut out = HashSet::new();
        let mut seen = HashSet::new();
        for &a in assertions {
            free_symbols(arena, a, &mut out, &mut seen);
        }
        let mut v: Vec<_> = out.into_iter().collect();
        v.sort_by_key(|s| s.index());
        v
    }

    #[test]
    fn eliminates_single_use_under_add_and_reconstructs() {
        // (bvult (bvadd x y) 200) ∧ (bvugt y 1): x occurs once (inside the add),
        // y survives in the second assertion. The add is unconstrained ⇒ replaced
        // by a fresh u; x := u - y.
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::BitVec(8)).unwrap();
        let y = arena.declare("y", Sort::BitVec(8)).unwrap();
        let (xv, yv) = (arena.var(x), arena.var(y));
        let sum = arena.bv_add(xv, yv).unwrap();
        let c = arena.bv_const(8, 200).unwrap();
        let a1 = arena.bv_ult(sum, c).unwrap();
        let one = arena.bv_const(8, 1).unwrap();
        let a2 = arena.bv_ugt(yv, one).unwrap();
        let originals = [a1, a2];

        let out = elim_unconstrained(&mut arena, &originals).unwrap();
        assert_eq!(out.eliminated(), 1);
        assert!(
            !survivors(&arena, out.assertions()).contains(&x),
            "x is eliminated"
        );

        let u = arena.find_internal_symbol("!unconstr!0").unwrap();
        let mut reduced = Assignment::new();
        reduced.set(u, bv8(10));
        reduced.set(y, bv8(3));
        for &a in out.assertions() {
            assert_eq!(eval(&arena, a, &reduced).unwrap(), Value::Bool(true));
        }
        let full = out.trail().reconstruct(&arena, &reduced).unwrap();
        assert_eq!(full.get(x), Some(bv8(7))); // u - y = 10 - 3
        assert_satisfies(&arena, &originals, &full);
    }

    #[test]
    fn orphaned_operand_is_defaulted_and_reconstructs() {
        // (bvult (bvadd x y) 200): BOTH x and y occur once, so the add is
        // unconstrained and y survives nowhere after the rewrite — it must be
        // defaulted (to 0) so x := u - y still reconstructs.
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::BitVec(8)).unwrap();
        let y = arena.declare("y", Sort::BitVec(8)).unwrap();
        let (xv, yv) = (arena.var(x), arena.var(y));
        let sum = arena.bv_add(xv, yv).unwrap();
        let c = arena.bv_const(8, 200).unwrap();
        let a1 = arena.bv_ult(sum, c).unwrap();
        let originals = [a1];

        let out = elim_unconstrained(&mut arena, &originals).unwrap();
        assert_eq!(out.eliminated(), 1);
        let surv = survivors(&arena, out.assertions());
        assert!(
            !surv.contains(&x) && !surv.contains(&y),
            "both eliminated/orphaned"
        );

        let u = arena.find_internal_symbol("!unconstr!0").unwrap();
        let mut reduced = Assignment::new();
        reduced.set(u, bv8(10));
        let full = out.trail().reconstruct(&arena, &reduced).unwrap();
        assert_eq!(full.get(y), Some(bv8(0)), "orphan operand defaulted to 0");
        assert_eq!(full.get(x), Some(bv8(10))); // u - y = 10 - 0
        assert_satisfies(&arena, &originals, &full);
    }

    #[test]
    fn does_not_fire_on_a_twice_used_variable() {
        // (bvult x (bvadd x 1)): x occurs twice, so it is not unconstrained.
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::BitVec(8)).unwrap();
        let xv = arena.var(x);
        let one = arena.bv_const(8, 1).unwrap();
        let sum = arena.bv_add(xv, one).unwrap();
        let a1 = arena.bv_ult(xv, sum).unwrap();

        let out = elim_unconstrained(&mut arena, &[a1]).unwrap();
        assert_eq!(out.eliminated(), 0);
        assert_eq!(out.assertions(), &[a1]);
    }

    #[test]
    fn does_not_fire_under_a_non_invertible_op() {
        // (bvult (bvmul x y) 200) ∧ (bvugt y 1): x is single-use but bvmul is not
        // invertible by this pass, so nothing is eliminated.
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::BitVec(8)).unwrap();
        let y = arena.declare("y", Sort::BitVec(8)).unwrap();
        let (xv, yv) = (arena.var(x), arena.var(y));
        let prod = arena.bv_mul(xv, yv).unwrap();
        let c = arena.bv_const(8, 200).unwrap();
        let a1 = arena.bv_ult(prod, c).unwrap();
        let one = arena.bv_const(8, 1).unwrap();
        let a2 = arena.bv_ugt(yv, one).unwrap();

        let out = elim_unconstrained(&mut arena, &[a1, a2]).unwrap();
        assert_eq!(out.eliminated(), 0);
    }

    #[test]
    fn peels_a_nested_invertible_stack() {
        // (bvult (bvadd (bvneg x) 5) 200): x single-use under bvneg, whose result
        // is single-use under bvadd — both layers peel.
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::BitVec(8)).unwrap();
        let xv = arena.var(x);
        let negx = arena.bv_neg(xv).unwrap();
        let five = arena.bv_const(8, 5).unwrap();
        let inner = arena.bv_add(negx, five).unwrap();
        let c = arena.bv_const(8, 200).unwrap();
        let a1 = arena.bv_ult(inner, c).unwrap();
        let originals = [a1];

        let out = elim_unconstrained(&mut arena, &originals).unwrap();
        assert_eq!(out.eliminated(), 2, "both invertible layers peel");
        let surv = survivors(&arena, out.assertions());
        assert_eq!(surv.len(), 1, "reduced to a single fresh variable");

        let u = surv[0];
        let mut reduced = Assignment::new();
        reduced.set(u, bv8(40)); // 40 < 200
        let full = out.trail().reconstruct(&arena, &reduced).unwrap();
        assert_satisfies(&arena, &originals, &full);
    }

    #[test]
    fn eliminates_single_use_under_odd_constant_multiply() {
        // (bvult (bvmul 3 x) 100): x single-use, 3 odd ⇒ x := 3⁻¹·u (3⁻¹ = 171
        // mod 256). The multiplier layer is peeled with no bit-blasting.
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::BitVec(8)).unwrap();
        let xv = arena.var(x);
        let three = arena.bv_const(8, 3).unwrap();
        let prod = arena.bv_mul(three, xv).unwrap();
        let hundred = arena.bv_const(8, 100).unwrap();
        let a1 = arena.bv_ult(prod, hundred).unwrap();
        let originals = [a1];

        let out = elim_unconstrained(&mut arena, &originals).unwrap();
        assert_eq!(out.eliminated(), 1);
        let u = arena.find_internal_symbol("!unconstr!0").unwrap();
        let mut reduced = Assignment::new();
        reduced.set(u, bv8(30)); // 30 < 100
        let full = out.trail().reconstruct(&arena, &reduced).unwrap();
        // 3⁻¹·30 = 171·30 mod 256 = 10, and 3·10 = 30 ✓.
        assert_eq!(full.get(x), Some(bv8(10)));
        assert_satisfies(&arena, &originals, &full);
    }

    #[test]
    fn does_not_fire_on_even_constant_multiply() {
        // (bvult (bvmul 4 x) 100): 4 is even ⇒ not invertible mod 2^w, no
        // elimination.
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::BitVec(8)).unwrap();
        let xv = arena.var(x);
        let four = arena.bv_const(8, 4).unwrap();
        let prod = arena.bv_mul(four, xv).unwrap();
        let hundred = arena.bv_const(8, 100).unwrap();
        let a1 = arena.bv_ult(prod, hundred).unwrap();

        let out = elim_unconstrained(&mut arena, &[a1]).unwrap();
        assert_eq!(out.eliminated(), 0);
    }

    /// Deterministic xorshift PRNG (no clock/RNG service).
    fn xorshift(state: &mut u64) -> u64 {
        let mut v = *state;
        v ^= v << 13;
        v ^= v >> 7;
        v ^= v << 17;
        *state = v;
        v
    }

    #[test]
    fn random_invertible_stacks_reconstruct_to_satisfy_originals() {
        // Bury a single-use `x` under a random stack of invertible ops with
        // constant operands, anchored by `(= stack k)`. The whole stack collapses
        // to one fresh variable forced to `k`; reconstruction must peel back to an
        // `x` satisfying the original equality.
        let mut state = 0x1357_9BDF_2468_ACE0u64;
        for trial in 0..300 {
            let mut arena = TermArena::new();
            let x = arena.declare("x", Sort::BitVec(8)).unwrap();
            let mut cur = arena.var(x);
            let depth = 1 + (xorshift(&mut state) % 4) as usize; // 1..=4 layers
            for _ in 0..depth {
                let c = u128::from(xorshift(&mut state) % 256);
                cur = match xorshift(&mut state) % 6 {
                    0 => arena.bv_neg(cur).unwrap(),
                    1 => arena.bv_not(cur).unwrap(),
                    2 => {
                        let k = arena.bv_const(8, c).unwrap();
                        arena.bv_add(cur, k).unwrap()
                    }
                    3 => {
                        let k = arena.bv_const(8, c).unwrap();
                        arena.bv_sub(cur, k).unwrap()
                    }
                    4 => {
                        let k = arena.bv_const(8, c).unwrap();
                        arena.bv_xor(cur, k).unwrap()
                    }
                    _ => {
                        // Force an odd factor so the multiply is invertible.
                        let k = arena.bv_const(8, c | 1).unwrap();
                        arena.bv_mul(k, cur).unwrap()
                    }
                };
            }
            let k = u128::from(xorshift(&mut state) % 256);
            let kc = arena.bv_const(8, k).unwrap();
            let eqk = arena.eq(cur, kc).unwrap();
            let originals = [eqk];

            let out = elim_unconstrained(&mut arena, &originals).unwrap();
            assert_eq!(out.eliminated(), depth, "trial {trial}: every layer peels");
            let surv = survivors(&arena, out.assertions());
            assert_eq!(surv.len(), 1, "trial {trial}: one surviving variable");

            // The reduced problem is `(= u k)`, forcing u = k.
            let mut reduced = Assignment::new();
            reduced.set(surv[0], bv8(k));
            assert_eq!(
                eval(&arena, out.assertions()[0], &reduced).unwrap(),
                Value::Bool(true),
                "trial {trial}: reduced model satisfies the reduced equality"
            );
            let full = out.trail().reconstruct(&arena, &reduced).unwrap();
            assert_satisfies(&arena, &originals, &full);
        }
    }
}

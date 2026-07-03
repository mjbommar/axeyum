//! Independent re-checker for T-B.3 [`Conflict`] records (slice T-B.7) — the
//! trusted small check that gates word-level `unsat`.
//!
//! The T-B.3 [`infer`](crate::infer) fixpoint is the *untrusted search*: it walks
//! the class substrate and may emit a [`Conflict`] claiming a premise subset is
//! jointly unsatisfiable. Per ADR-0053 word-level `unsat` may only ship "through a
//! re-checkable derivation". [`check_conflict`] is that check: it re-verifies a
//! recorded conflict **from the cited premises alone**, trusting nothing in the
//! record beyond using it as a *hint script*, and returns `false` at the first
//! step that fails to re-derive. A `false` is always safe — it merely declines the
//! `unsat` to `unknown`.
//!
//! # Independence — why this is a real check, not a rubber stamp
//!
//! This module shares **no reasoning code** with [`infer`](crate::infer): it does
//! not call its alignment walker, its cycle detector, or its class machinery. It
//! re-derives the contradiction with its own minimal tools:
//!
//! 1. **premise-index bounds** — every cited index must address a real equality;
//! 2. **its own union-find** ([`MiniUf`]) over *only the cited premises*, to
//!    confirm `member_a ≈ member_b` is entailed by them (a wrong or insufficient
//!    premise set fails here);
//! 3. **T-B.1 [`normalize`]** (the denotation-preserving rewrite, a shared
//!    *representation* primitive, not a reasoning one) to recover each member's
//!    component vector, then **its own left-to-right aligned walk** that advances
//!    only over provably-equal-length prefix cells and confirms the recorded
//!    constant clash is a genuine, self-evident contradiction (equal-length blocks
//!    that differ, or length-incompatible blocks whose overlap disagrees).
//!
//! The soundness of an accepted conflict rests on (2) + the clash check alone:
//! `member_a ≈ member_b` (same sequence) with an aligned equal-length prefix
//! forces the two clashing constant blocks to occupy the *same* absolute offsets,
//! so two different constants there is a contradiction under any assignment. The
//! recorded positions / constants are cross-checked against the independent walk
//! (catching a corrupted record) but are never *trusted*.
//!
//! # What `check_conflict` certifies — and what stays `unknown`
//!
//! Only conflicts whose two members are connected by the cited premises through a
//! **direct** equality chain (no intervening derived fact) and whose contradiction
//! is a **constant clash at an equal-length-aligned position** are certified.
//! Loops (`x ≈ a ++ x`), parity/length arguments (`x ≈ x ++ x ∧ x ≠ ε`), and
//! conflicts that only arise *after* an inference step are certified by the
//! **slice-2** additions below rather than `check_conflict`.
//!
//! # Slice 2 — checked inference-dependent derivations
//!
//! [`check_fact`] independently re-verifies a T-B.3 [`Fact`] (a *derived*
//! equality) from its cited premises alone, with the same independence discipline
//! as [`check_conflict`] (its own [`MiniUf`] and its own aligned walkers; no
//! reasoning code is shared with [`infer`](crate::infer)). It certifies four
//! shapes, each by a self-evident length/offset argument:
//!
//! * **cycle-ε** ([`Rule::CycleEpsilon`]): `target ≈ ε` when a self-loop endpoint
//!   `w` re-normalizes to a component vector containing a continuation component
//!   `c_p ≈ w` and an off-cycle occurrence of `target`. Then `|w| = Σ|cᵢ|` and
//!   `|c_p| = |w|` force every off-cycle length to `0`, so `target ≈ ε`. A `target`
//!   that is a **nonempty constant** is *not* an ε fact — it is a contradiction,
//!   certified separately by [`check_cycle_constant_conflict`];
//! * **endpoint-emp** ([`Rule::InferEndpointEmp`]): `target ≈ ε` when two
//!   provably-equal members align on an equal-length prefix that **exhausts** the
//!   shorter, forcing the longer's tail (which contains `target`) to `ε`;
//! * **endpoint-eq** ([`Rule::InferEndpointEq`]): `c ≈ d` when an equal-length
//!   prefix leaves exactly one component on each side — equal-length suffixes of
//!   equal sequences are equal;
//! * **unify** ([`Rule::InferUnify`]): `c ≈ d` at an equal-length aligned interior
//!   position of two equal members.
//!
//! [`check_cycle_constant_conflict`] certifies **`unsat`** for the
//! `x ≈ "a" ++ x` family: the same self-loop length argument that would force an
//! off-cycle component to `ε`, applied to a component that is a nonempty constant
//! (length ≥ 1), is a contradiction (`0 = Σ ≥ 1`). Multi-node containment cycles
//! (`x ≈ y ++ "a"`, `y ≈ x ++ "b"`) have no single self-loop endpoint witness and
//! are conservatively **declined**.
//!
//! A shape that is not one of the above — or whose cited premises do not
//! independently re-derive it — is simply **not certified** (`false`), a safe
//! decline to `unknown`.

use std::collections::{BTreeMap, BTreeSet};

use axeyum_ir::{Assignment, Op, TermArena, TermId, TermNode, Value, eval};

use crate::infer::{Conflict, Fact, Rule};
use crate::normal_form::{concat_components, normalize};

/// Re-verifies a T-B.3 [`Conflict`] from the cited premises alone.
///
/// Returns `true` only when, using **only** the equalities named by
/// `conflict.premises` (indices into `equalities`), the two clashing members can
/// be independently shown jointly unsatisfiable: they are in one equivalence
/// class under the cited premises, and after an aligned equal-length prefix they
/// force two clashing constant blocks at the recorded position. Any failure —
/// an out-of-range index, members not provably equal, positions that do not line
/// up, or constants that do not actually clash — yields `false` (a safe decline
/// to `unknown`).
#[must_use]
pub fn check_conflict(
    arena: &mut TermArena,
    equalities: &[(TermId, TermId)],
    conflict: &Conflict,
) -> bool {
    // (1) Every cited premise index must address a real equality.
    if conflict.premises.iter().any(|&p| p >= equalities.len()) {
        return false;
    }

    let reason = &conflict.reason;

    // (2) member_a ≈ member_b must be entailed by the cited premises alone. Build
    // an independent union-find over ONLY those premises and require the two
    // members to share a representative. (A wrong / insufficient premise set, the
    // corrupted-premises negative case, fails right here.)
    let mut uf = MiniUf::default();
    for &p in &conflict.premises {
        let (a, b) = equalities[p];
        uf.union(a, b);
    }
    if uf.find(reason.member_a) != uf.find(reason.member_b) {
        return false;
    }

    // (3) Re-normalize both members (T-B.1) and independently walk their component
    // vectors to the first divergence, advancing only over provably-equal-length
    // prefix cells.
    let norm_a = normalize(arena, reason.member_a);
    let atoms_a = concat_components(arena, norm_a);
    let norm_b = normalize(arena, reason.member_b);
    let atoms_b = concat_components(arena, norm_b);

    let Some((i, j)) = first_divergence(arena, &uf, &atoms_a, &atoms_b) else {
        // No both-constant divergence reachable by an equal-length-aligned walk:
        // nothing to certify (loops, parity, endpoint tails all land here).
        return false;
    };

    // (4) Cross-check the independent divergence against the recorded hint: same
    // aligned positions and same clashing constant terms. This is a consistency
    // gate on the record, not a source of trust — the walk found (i, j) itself.
    if i != reason.position_a || j != reason.position_b {
        return false;
    }
    let (ca, cb) = (atoms_a[i], atoms_b[j]);
    if ca != reason.const_a || cb != reason.const_b {
        return false;
    }

    // (5) The self-evident contradiction: two constant blocks at the same aligned
    // offset that cannot be equal (equal length but different, or length
    // incompatible with a disagreeing overlap).
    constants_clash(arena, ca, cb)
}

/// Re-verifies that the cited premises entail `a ≈ b` by direct equality chaining.
///
/// Used by the disequality-driven refutation arm: given a disequality `a ≠ b` and
/// a candidate sufficient premise set `cited` (indices into `equalities`), this
/// confirms — with an independent union-find over only those premises — that they
/// place `a` and `b` in one class. Returns `false` on any out-of-range index or if
/// the premises do not actually connect the two terms.
#[must_use]
pub fn check_equality(
    equalities: &[(TermId, TermId)],
    cited: &BTreeSet<usize>,
    a: TermId,
    b: TermId,
) -> bool {
    if cited.iter().any(|&p| p >= equalities.len()) {
        return false;
    }
    let mut uf = MiniUf::default();
    for &p in cited {
        let (x, y) = equalities[p];
        uf.union(x, y);
    }
    uf.find(a) == uf.find(b)
}

// ----- fact re-checking (slice 2) --------------------------------------------

/// Re-verifies a T-B.3 [`Fact`] — a *derived* equality — from its cited premises
/// alone, sharing no reasoning code with [`infer`](crate::infer).
///
/// Returns `true` only when the fact's equality can be independently re-derived
/// from the equalities named by `fact.premises` by the self-evident length/offset
/// argument for its [`Rule`] (see the module docs). Any shape it cannot re-derive
/// — an out-of-range premise, a rule it does not cover, a multi-node cycle, a
/// cited-premise set insufficient to entail the equality — yields `false`, a safe
/// decline. A `false` never asserts the fact is wrong, only that this checker
/// declines to certify it.
#[must_use]
pub fn check_fact(arena: &mut TermArena, equalities: &[(TermId, TermId)], fact: &Fact) -> bool {
    if fact.premises.iter().any(|&p| p >= equalities.len()) {
        return false;
    }
    match fact.rule {
        Rule::CycleEpsilon => check_cycle_epsilon_fact(arena, equalities, fact),
        Rule::InferEndpointEmp => check_endpoint_emp_fact(arena, equalities, fact),
        Rule::InferEndpointEq => check_endpoint_eq_fact(arena, equalities, fact),
        Rule::InferUnify => check_unify_fact(arena, equalities, fact),
    }
}

/// Certifies **`unsat`** for a self-loop that forces a nonempty constant to `ε`
/// (the `x ≈ "a" ++ x` family), from a T-B.3 [`Rule::CycleEpsilon`] `fact` whose
/// `target` is a nonempty constant.
///
/// The cited premises exhibit a self-loop endpoint `w` whose re-normalized
/// component vector contains a continuation `c_p ≈ w` and an off-cycle occurrence
/// of the constant `target`. The length identity `Σ_{i≠p}|cᵢ| = 0` then clashes
/// with `|target| ≥ 1`, so the premises are jointly unsatisfiable. Returns `false`
/// (declines) unless the fact is a `CycleEpsilon` fact with a nonempty-constant
/// target and the self-loop witness re-derives from the cited premises.
#[must_use]
pub fn check_cycle_constant_conflict(
    arena: &mut TermArena,
    equalities: &[(TermId, TermId)],
    fact: &Fact,
) -> bool {
    if fact.rule != Rule::CycleEpsilon || fact.premises.iter().any(|&p| p >= equalities.len()) {
        return false;
    }
    let Some(target) = epsilon_fact_target(arena, fact.equality) else {
        return false;
    };
    // The contradiction shape: an off-cycle component with a known length ≥ 1.
    match known_len(arena, target) {
        Some(l) if l >= 1 => {}
        _ => return false,
    }
    let uf = mini_uf(equalities, &fact.premises);
    cycle_self_loop_witness(arena, equalities, &fact.premises, &uf, target)
}

/// `CycleEpsilon` fact `target ≈ ε`: certified when a self-loop endpoint witness
/// forces the (variable / possibly-empty) `target` off-cycle component to `ε`. A
/// nonempty-constant target is declined here (it is a contradiction, not an ε
/// fact — see [`check_cycle_constant_conflict`]).
fn check_cycle_epsilon_fact(
    arena: &mut TermArena,
    equalities: &[(TermId, TermId)],
    fact: &Fact,
) -> bool {
    let Some(target) = epsilon_fact_target(arena, fact.equality) else {
        return false;
    };
    // A target with a known length ≥ 1 cannot be ε: decline (the contradiction is
    // certified by `check_cycle_constant_conflict`, not as a forward ε fact).
    if matches!(known_len(arena, target), Some(l) if l >= 1) {
        return false;
    }
    let uf = mini_uf(equalities, &fact.premises);
    cycle_self_loop_witness(arena, equalities, &fact.premises, &uf, target)
}

/// The shared self-loop length witness: some endpoint `w` of a cited equality
/// re-normalizes to a component vector `[c₀…c_{k-1}]` (`k ≥ 2`) containing a
/// continuation index `p` with `c_p ≈ w` (so `|c_p| = |w| = Σ|cᵢ|`, forcing every
/// off-cycle `|cᵢ| = 0`) and a **distinct** off-cycle occurrence `c_t ≈ target`.
/// Independent of [`infer`](crate::infer)'s cycle detector.
fn cycle_self_loop_witness(
    arena: &mut TermArena,
    equalities: &[(TermId, TermId)],
    premises: &BTreeSet<usize>,
    uf: &MiniUf,
    target: TermId,
) -> bool {
    for w in endpoints_of(equalities, premises) {
        let comps = normalized_components(arena, w);
        if comps.len() < 2 {
            continue;
        }
        // The continuation: a component equal (under the cited premises) to the
        // whole endpoint `w`.
        let Some(p) = comps.iter().position(|&c| uf.find(c) == uf.find(w)) else {
            continue;
        };
        // A distinct off-cycle occurrence of `target`.
        let hits_target = comps
            .iter()
            .enumerate()
            .any(|(t, &c)| t != p && (c == target || uf.find(c) == uf.find(target)));
        if hits_target {
            return true;
        }
    }
    false
}

/// `InferEndpointEmp` fact `target ≈ ε`: certified when two provably-equal members
/// align on an equal-length prefix that exhausts the shorter, forcing the longer's
/// remaining tail (which contains `target`) to `ε`.
fn check_endpoint_emp_fact(
    arena: &mut TermArena,
    equalities: &[(TermId, TermId)],
    fact: &Fact,
) -> bool {
    let Some(target) = epsilon_fact_target(arena, fact.equality) else {
        return false;
    };
    if matches!(known_len(arena, target), Some(l) if l >= 1) {
        return false;
    }
    let uf = mini_uf(equalities, &fact.premises);
    let eps = endpoints_of(equalities, &fact.premises);
    for &l in &eps {
        for &r in &eps {
            if l == r || uf.find(l) != uf.find(r) {
                continue;
            }
            let na = normalized_components(arena, l);
            let nb = normalized_components(arena, r);
            let i = consume_equal_prefix(arena, &uf, &na, &nb);
            // `r` fully consumed, `l` has a non-empty tail whose length is forced 0.
            if i == nb.len()
                && i < na.len()
                && na[i..]
                    .iter()
                    .any(|&c| c == target || uf.find(c) == uf.find(target))
            {
                return true;
            }
        }
    }
    false
}

/// `InferEndpointEq` fact `c ≈ d`: certified when an equal-length prefix leaves
/// exactly one component on each side simultaneously — equal-length suffixes of
/// equal sequences are equal.
fn check_endpoint_eq_fact(
    arena: &mut TermArena,
    equalities: &[(TermId, TermId)],
    fact: &Fact,
) -> bool {
    let (c, d) = fact.equality;
    let uf = mini_uf(equalities, &fact.premises);
    let eps = endpoints_of(equalities, &fact.premises);
    for &l in &eps {
        for &r in &eps {
            if l == r || uf.find(l) != uf.find(r) {
                continue;
            }
            let na = normalized_components(arena, l);
            let nb = normalized_components(arena, r);
            if na.is_empty() || nb.is_empty() {
                continue;
            }
            let i = consume_equal_prefix(arena, &uf, &na, &nb);
            if i == na.len() - 1 && i == nb.len() - 1 && matches_pair(&uf, na[i], nb[i], c, d) {
                return true;
            }
        }
    }
    false
}

/// `InferUnify` fact `c ≈ d`: certified at an equal-length aligned position of two
/// equal members (equal length + equal starting offset ⇒ the two blocks are equal).
fn check_unify_fact(arena: &mut TermArena, equalities: &[(TermId, TermId)], fact: &Fact) -> bool {
    let (c, d) = fact.equality;
    let uf = mini_uf(equalities, &fact.premises);
    let eps = endpoints_of(equalities, &fact.premises);
    for &l in &eps {
        for &r in &eps {
            if l == r || uf.find(l) != uf.find(r) {
                continue;
            }
            let na = normalized_components(arena, l);
            let nb = normalized_components(arena, r);
            let mut i = 0;
            while i < na.len() && i < nb.len() {
                // Prefix stays offset-aligned only across equal-length cells.
                if !pair_equal_length(arena, &uf, na[i], nb[i]) {
                    break;
                }
                if matches_pair(&uf, na[i], nb[i], c, d) {
                    return true;
                }
                i += 1;
            }
        }
    }
    false
}

// ----- fact-checking helpers (own copies — no `infer` reasoning code) ----------

/// A [`MiniUf`] over exactly the cited premise equalities.
fn mini_uf(equalities: &[(TermId, TermId)], premises: &BTreeSet<usize>) -> MiniUf {
    let mut uf = MiniUf::default();
    for &p in premises {
        if let Some(&(a, b)) = equalities.get(p) {
            uf.union(a, b);
        }
    }
    uf
}

/// The distinct endpoint terms (both sides) of the cited premise equalities,
/// sorted — the candidate `w` / `L` / `R` terms for the witnesses.
fn endpoints_of(equalities: &[(TermId, TermId)], premises: &BTreeSet<usize>) -> Vec<TermId> {
    let mut s: BTreeSet<TermId> = BTreeSet::new();
    for &p in premises {
        if let Some(&(a, b)) = equalities.get(p) {
            s.insert(a);
            s.insert(b);
        }
    }
    s.into_iter().collect()
}

/// The [`normalize`]d, ε-dropped component vector of `t` — the same representation
/// primitive [`check_conflict`] uses.
fn normalized_components(arena: &mut TermArena, t: TermId) -> Vec<TermId> {
    let n = normalize(arena, t);
    concat_components(arena, n)
}

/// The non-ε side of a `(a, b)` equality when exactly one side is the empty
/// sequence, i.e. the `target` of an `target ≈ ε` fact; `None` otherwise.
fn epsilon_fact_target(arena: &TermArena, equality: (TermId, TermId)) -> Option<TermId> {
    let (a, b) = equality;
    match (is_epsilon_term(arena, a), is_epsilon_term(arena, b)) {
        (true, false) => Some(b),
        (false, true) => Some(a),
        _ => None,
    }
}

/// Whether `t` is (syntactically or by value) the empty sequence.
fn is_epsilon_term(arena: &TermArena, t: TermId) -> bool {
    matches!(
        arena.node(t),
        TermNode::App {
            op: Op::SeqEmpty(_),
            ..
        }
    ) || matches!(seq_value(arena, t), Some(v) if v.is_empty())
}

/// Whether `a` and `b` are provably **equal length** under the cited premises:
/// identical handle, one class (equal sequences), or two structurally-known equal
/// lengths.
fn pair_equal_length(arena: &TermArena, uf: &MiniUf, a: TermId, b: TermId) -> bool {
    if a == b || uf.find(a) == uf.find(b) {
        return true;
    }
    match (known_len(arena, a), known_len(arena, b)) {
        (Some(la), Some(lb)) => la == lb,
        _ => false,
    }
}

/// Consumes the longest **one-to-one, provably-equal-length** prefix of two
/// component vectors, returning the number of cells consumed on each side. Each
/// consumed pair contributes equal length, so the total consumed length stays
/// equal on both sides — the invariant every fact witness relies on.
fn consume_equal_prefix(arena: &TermArena, uf: &MiniUf, a: &[TermId], b: &[TermId]) -> usize {
    let mut i = 0;
    while i < a.len() && i < b.len() && pair_equal_length(arena, uf, a[i], b[i]) {
        i += 1;
    }
    i
}

/// Whether the unordered pair `{x, y}` matches the unordered pair `{c, d}` up to
/// provable equality under the cited premises (identical handle or one class).
fn matches_pair(uf: &MiniUf, x: TermId, y: TermId, c: TermId, d: TermId) -> bool {
    let eq = |p: TermId, q: TermId| p == q || uf.find(p) == uf.find(q);
    (eq(x, c) && eq(y, d)) || (eq(x, d) && eq(y, c))
}

// ----- independent aligned walk ----------------------------------------------

/// Walks two component vectors left to right, consuming any provably-equal-length
/// prefix, and returns the `(i, j)` index of the first **both-constant**
/// divergence — the only shape this checker certifies. Returns `None` if the walk
/// hits a divergence it cannot certify (a variable facing a constant, two
/// different-class variables) or exhausts a side without a both-constant clash.
fn first_divergence(
    arena: &TermArena,
    uf: &MiniUf,
    atoms_a: &[TermId],
    atoms_b: &[TermId],
) -> Option<(usize, usize)> {
    let (mut i, mut j) = (0usize, 0usize);
    while i < atoms_a.len() && j < atoms_b.len() {
        let ca = atoms_a[i];
        let cb = atoms_b[j];

        // Constants are handled FIRST, before the same-class consume: the clashing
        // atoms may themselves be the two members the premises assert equal (the
        // direct `"a" = "b"` shape), in which case they *are* in one class — that
        // is precisely the contradiction, not a reason to consume them.
        if let (Some(va), Some(vb)) = (seq_value(arena, ca), seq_value(arena, cb)) {
            if va == vb {
                // Equal constant blocks: aligned, consume.
                i += 1;
                j += 1;
                continue;
            }
            // Two distinct constant blocks at this position: the clash front.
            return Some((i, j));
        }

        // At least one non-constant cell. Provably-equal sequences (identical
        // handle or same class under the cited premises) contribute equal length:
        // consume.
        if ca == cb || uf.find(ca) == uf.find(cb) {
            i += 1;
            j += 1;
            continue;
        }

        // Otherwise, we may still advance if both cells have a *known equal
        // length* (equal length keeps later offsets aligned even without knowing
        // the contents) — this is what lets a `seq.unit` prefix be skipped. Any
        // other divergence (unknown length on a side) is an arrangement front
        // this checker does not certify.
        match (known_len(arena, ca), known_len(arena, cb)) {
            (Some(la), Some(lb)) if la == lb => {
                i += 1;
                j += 1;
            }
            _ => return None,
        }
    }
    None
}

/// Whether two constant sequence blocks cannot be equal at the same absolute
/// offset: equal length but different contents, or different length whose
/// overlapping prefix already disagrees. `false` (not a clash) if either does not
/// evaluate closed, or the shorter is a genuine prefix of the longer (a splittable
/// case, not a contradiction).
fn constants_clash(arena: &TermArena, a: TermId, b: TermId) -> bool {
    let (Some(va), Some(vb)) = (seq_value(arena, a), seq_value(arena, b)) else {
        return false;
    };
    if va.len() == vb.len() {
        return va != vb;
    }
    let (short, long) = if va.len() <= vb.len() {
        (&va, &vb)
    } else {
        (&vb, &va)
    };
    // A clash iff the shorter is NOT a prefix of the longer.
    !short.iter().zip(long.iter()).all(|(x, y)| x == y)
}

// ----- structural helpers (own copies — no `infer` reasoning code) ------------

/// The closed sequence value of `t`, or `None` if it does not evaluate closed.
fn seq_value(arena: &TermArena, t: TermId) -> Option<Vec<Value>> {
    match eval(arena, t, &Assignment::new()) {
        Ok(Value::Seq(v)) => Some(v),
        _ => None,
    }
}

/// A structurally-determined length for `t`, or `None` when it depends on an
/// opaque sequence. Mirrors the structure-only length reasoning the T-B.3 rules
/// use, computed here independently.
fn known_len(arena: &TermArena, t: TermId) -> Option<u128> {
    if let Ok(Value::Seq(v)) = eval(arena, t, &Assignment::new()) {
        return u128::try_from(v.len()).ok();
    }
    match arena.node(t) {
        TermNode::App {
            op: Op::SeqUnit, ..
        } => Some(1),
        TermNode::App {
            op: Op::SeqEmpty(_),
            ..
        } => Some(0),
        TermNode::App {
            op: Op::SeqConcat,
            args,
        } => {
            let la = known_len(arena, args[0])?;
            let lb = known_len(arena, args[1])?;
            la.checked_add(lb)
        }
        _ => None,
    }
}

// ----- minimal union-find -----------------------------------------------------

/// A tiny, self-contained union-find over [`TermId`]s, keyed by value. Union by
/// minimum id (so the representative is deterministic); path-free `find` walks the
/// parent chain. Deliberately independent of [`crate::classes::Classes`] — the
/// point of this module is to re-derive with its own machinery.
#[derive(Default)]
struct MiniUf {
    parent: BTreeMap<TermId, TermId>,
}

impl MiniUf {
    fn find(&self, mut t: TermId) -> TermId {
        while let Some(&p) = self.parent.get(&t) {
            if p == t {
                break;
            }
            t = p;
        }
        t
    }

    fn union(&mut self, a: TermId, b: TermId) {
        self.parent.entry(a).or_insert(a);
        self.parent.entry(b).or_insert(b);
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb {
            return;
        }
        // Union by minimum id: the smaller id becomes the root.
        let (root, child) = if ra < rb { (ra, rb) } else { (rb, ra) };
        self.parent.insert(child, root);
    }
}

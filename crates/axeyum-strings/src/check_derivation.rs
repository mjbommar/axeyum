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
//! # What this slice certifies — and what stays `unknown`
//!
//! Only conflicts whose two members are connected by the cited premises through a
//! **direct** equality chain (no intervening derived fact) and whose contradiction
//! is a **constant clash at an equal-length-aligned position** are certified.
//! Loops (`x ≈ a ++ x`), parity/length arguments (`x ≈ x ++ x ∧ x ≠ ε`), and
//! conflicts that only arise *after* an inference step (e.g. a cycle-ε fact that
//! sets up the alignment) are conservatively **rejected** — they stay `unknown`
//! until a later slice adds an independent `check_fact` for the derived-equality
//! premises.

use std::collections::{BTreeMap, BTreeSet};

use axeyum_ir::{Assignment, Op, TermArena, TermId, TermNode, Value, eval};

use crate::infer::Conflict;
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

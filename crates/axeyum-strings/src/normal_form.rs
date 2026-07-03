//! The Phase-B **normalization invariant** (slice T-B.1).
//!
//! A confluent, terminating, denotation-preserving rewrite over `Sort::Seq`
//! terms, applied before any word-level reasoning. It is the precondition for
//! flat/normal-form computation: it makes two syntactically different but equal
//! concatenations comparable.
//!
//! # The rules
//!
//! Applied to a fixpoint over every subterm (recursing through `Bool`/arithmetic
//! structure too — a `str.len` can sit under an `Int` `+`):
//!
//! 1. **flatten** a nested `str.++` tree into a canonical **right-associated**
//!    spine — `((a ++ b) ++ c)` and `(a ++ (b ++ c))` both become
//!    `a ++ (b ++ c)`;
//! 2. **drop** `seq.empty` (ε) components of a concatenation;
//! 3. **fuse** a maximal run of adjacent *constant* components (a component the
//!    ground evaluator evaluates closed) into one canonical **constant block**;
//! 4. **push `str.len`** through concatenation and constants:
//!    `len(x ++ y) → len(x) + len(y)`, `len(const) → Int`,
//!    `len(seq.unit e) → 1`, `len(seq.empty) → 0`.
//!
//! # Constant fusion in this IR — a documented adaptation, not a guess
//!
//! cvc5 fuses `"a" ++ "b"` into the single string literal `"ab"`. The Axeyum IR
//! (ADR-0051) has **no atomic multi-element sequence literal**: the only
//! sequence-constant terms are `seq.empty`, `seq.unit(c)` over a scalar constant
//! `c`, and their concatenation, and
//! [`axeyum_ir`]'s `value_to_term` deliberately declines `Value::Seq`. So a run
//! of `k ≥ 2` adjacent constants cannot collapse to one node. Rule 3 is
//! therefore realized as: a maximal constant run is emitted as a single
//! **right-associated `seq.unit` block** that [`concat_components`] treats as one
//! opaque constant component. This preserves the observable invariant — *no two
//! adjacent components of a normalized concatenation are both constant* — without
//! inventing a literal the IR cannot evaluate. Adding an atomic literal is an IR
//! change out of scope for this slice; per the ADR-0053 discipline we adapt the
//! representation rather than guess one.
//!
//! Every rule is denotation-preserving; the whole pass is idempotent
//! ([`normalize`]`(`[`normalize`]`(t)) == `[`normalize`]`(t)` as interned
//! [`TermId`]s). A builder error on any rewrite is a **decline**: the node is
//! rebuilt with its normalized children unchanged, never dropped and never
//! guessed.

use std::collections::HashMap;

use axeyum_ir::{
    ArraySortKey, Assignment, IrError, Op, Sort, TermArena, TermId, TermNode, Value, eval,
};

/// Normalizes `term` under the T-B.1 rules, returning the rewritten (interned)
/// term. Denotation-preserving, terminating, and idempotent.
///
/// Every `Seq`-sorted subterm — including those reached only through `Bool` or
/// arithmetic structure (e.g. a `str.len` under an `Int` `+`) — is normalized.
/// The result is deterministic (no hash-map iteration order escapes into the
/// output structure).
#[must_use]
pub fn normalize(arena: &mut TermArena, term: TermId) -> TermId {
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    norm(arena, term, &mut memo)
}

/// The flattened, ε-dropped, constant-fused component view of `term`.
///
/// Descends through *non-constant* `str.++` nodes, keeps any fully-constant
/// concatenation subtree whole as a single constant component, and drops
/// `seq.empty` components. On a [`normalize`]d term this returns exactly the
/// canonical component vector the flat/normal-form slices (T-B.2+) consume; the
/// empty sequence yields an empty vector.
#[must_use]
pub fn concat_components(arena: &TermArena, term: TermId) -> Vec<TermId> {
    let mut out = Vec::new();
    collect_components(arena, term, &mut out);
    out
}

// ----- core recursion ---------------------------------------------------------

fn norm(arena: &mut TermArena, term: TermId, memo: &mut HashMap<TermId, TermId>) -> TermId {
    if let Some(&cached) = memo.get(&term) {
        return cached;
    }
    let result = norm_uncached(arena, term, memo);
    memo.insert(term, result);
    result
}

fn norm_uncached(
    arena: &mut TermArena,
    term: TermId,
    memo: &mut HashMap<TermId, TermId>,
) -> TermId {
    // Extract the operator and children with a scoped immutable borrow so the
    // arena is free to mutate below.
    let (op, args): (Op, Vec<TermId>) = match arena.node(term) {
        TermNode::App { op, args } => (*op, args.to_vec()),
        _ => return term,
    };

    // Normalize children first (post-order), so every rule sees normalized
    // operands.
    let new_args: Vec<TermId> = args.iter().map(|&a| norm(arena, a, memo)).collect();

    match op {
        // Rules 1–3: flatten / drop-ε / fuse over the concatenation spine.
        Op::SeqConcat => match normalize_concat(arena, term, new_args[0], new_args[1]) {
            Ok(t) => t,
            // Decline: keep normalized children, do not guess.
            Err(_) => arena.rebuild_with_args(term, &new_args),
        },
        // Rule 4: push `str.len` through `++` and constants.
        Op::SeqLen => match push_len(arena, new_args[0]) {
            Ok(t) => t,
            Err(_) => arena.rebuild_with_args(term, &new_args),
        },
        // Everything else (Bool/arith/Eq/seq.unit/seq.empty/…) rebuilds with its
        // normalized children — this is how a `str.len` under arithmetic is
        // reached.
        _ => arena.rebuild_with_args(term, &new_args),
    }
}

// ----- rules 1–3: the concatenation spine ------------------------------------

/// Normalizes `a ++ b` (both operands already normalized): flatten into atoms,
/// drop ε, fuse constant runs, rebuild right-associated.
fn normalize_concat(
    arena: &mut TermArena,
    term: TermId,
    a: TermId,
    b: TermId,
) -> Result<TermId, IrError> {
    let key = element_key(arena, term)?;
    let mut atoms = Vec::new();
    flatten_atoms(arena, a, &mut atoms);
    flatten_atoms(arena, b, &mut atoms);
    let components = fuse_constant_runs(arena, &atoms)?;
    right_assoc_concat(arena, &components, key)
}

/// Collects the flat sequence of non-`++`, non-ε atoms of `term` (descending
/// through every `str.++`, dropping `seq.empty`).
fn flatten_atoms(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    if let TermNode::App { op, args } = arena.node(term) {
        match op {
            Op::SeqConcat => {
                let left = args[0];
                let right = args[1];
                flatten_atoms(arena, left, out);
                flatten_atoms(arena, right, out);
                return;
            }
            // Drop ε.
            Op::SeqEmpty(_) => return,
            _ => {}
        }
    }
    out.push(term);
}

/// Fuses each maximal run of adjacent constant atoms into one right-associated
/// constant block; non-constant atoms and singleton constants pass through.
fn fuse_constant_runs(arena: &mut TermArena, atoms: &[TermId]) -> Result<Vec<TermId>, IrError> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < atoms.len() {
        if is_constant(arena, atoms[i]) {
            let start = i;
            while i < atoms.len() && is_constant(arena, atoms[i]) {
                i += 1;
            }
            let run = &atoms[start..i];
            if run.len() == 1 {
                out.push(run[0]);
            } else {
                // A ≥2 constant run becomes one canonical constant block.
                out.push(fold_right_assoc(arena, run)?);
            }
        } else {
            out.push(atoms[i]);
            i += 1;
        }
    }
    Ok(out)
}

/// Right-associated `str.++` of `components`, or `seq.empty` when empty.
fn right_assoc_concat(
    arena: &mut TermArena,
    components: &[TermId],
    key: ArraySortKey,
) -> Result<TermId, IrError> {
    if components.is_empty() {
        return Ok(arena.seq_empty(key));
    }
    fold_right_assoc(arena, components)
}

/// Folds a **non-empty** slice into a right-associated `str.++`
/// (`c0 ++ (c1 ++ (… ++ cₙ))`); a single element is returned unchanged.
fn fold_right_assoc(arena: &mut TermArena, parts: &[TermId]) -> Result<TermId, IrError> {
    let mut acc = *parts.last().expect("fold_right_assoc on non-empty slice");
    for &part in parts[..parts.len() - 1].iter().rev() {
        acc = arena.seq_concat(part, acc)?;
    }
    Ok(acc)
}

// ----- rule 4: push `str.len` -------------------------------------------------

/// The structural shape of a sequence for length-pushing.
enum Shape {
    /// A concatenation `a ++ b` — length distributes.
    Concat(TermId, TermId),
    /// A `seq.unit` — length is `1`.
    Unit,
    /// A symbol or otherwise-opaque sequence — keep `str.len`.
    Opaque,
}

/// The length shape for `s` (already normalized): a constant collapses to an
/// `Int` constant, a concatenation distributes into `len(a) + len(b)`, a unit is
/// `1`, and anything opaque keeps `str.len`.
fn push_len(arena: &mut TermArena, s: TermId) -> Result<TermId, IrError> {
    // `len(const) → Int` — covers `seq.empty → 0`, `seq.unit(const) → 1`, and a
    // fused constant block → its exact length.
    if is_constant(arena, s)
        && let Value::Seq(elements) = eval(arena, s, &Assignment::new())?
    {
        let n = i128::try_from(elements.len())
            .map_err(|_| IrError::ArithmeticOverflow { op: "seq_len" })?;
        return Ok(arena.int_const(n));
    }

    let shape = match arena.node(s) {
        TermNode::App {
            op: Op::SeqConcat,
            args,
        } => Shape::Concat(args[0], args[1]),
        TermNode::App {
            op: Op::SeqUnit, ..
        } => Shape::Unit,
        _ => Shape::Opaque,
    };

    match shape {
        Shape::Concat(a, b) => {
            let la = push_len(arena, a)?;
            let lb = push_len(arena, b)?;
            arena.int_add(la, lb)
        }
        // `len(seq.unit e) = 1` for any element `e`.
        Shape::Unit => Ok(arena.int_const(1)),
        // A symbol or otherwise-opaque sequence: keep `str.len`.
        Shape::Opaque => arena.seq_len(s),
    }
}

// ----- `concat_components` ----------------------------------------------------

fn collect_components(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    if let TermNode::App {
        op: Op::SeqConcat,
        args,
    } = arena.node(term)
    {
        // A fully-constant concatenation is a canonical constant block — one
        // component; descend only through non-constant spines.
        if !is_constant(arena, term) {
            let left = args[0];
            let right = args[1];
            collect_components(arena, left, out);
            collect_components(arena, right, out);
            return;
        }
    } else if matches!(
        arena.node(term),
        TermNode::App {
            op: Op::SeqEmpty(_),
            ..
        }
    ) {
        // Drop ε.
        return;
    }
    out.push(term);
}

// ----- helpers ----------------------------------------------------------------

/// Whether `term` evaluates closed (no free symbols / unbound functions) under
/// the ground evaluator — the constancy test of rule 3 and rule 4. A term that
/// declines to evaluate (open, or e.g. an overflow) is treated as non-constant,
/// so fusion is conservative.
fn is_constant(arena: &TermArena, term: TermId) -> bool {
    eval(arena, term, &Assignment::new()).is_ok()
}

/// The element key of a `Sort::Seq` term.
fn element_key(arena: &TermArena, term: TermId) -> Result<ArraySortKey, IrError> {
    match arena.sort_of(term) {
        Sort::Seq(key) => Ok(key),
        found => Err(IrError::SortMismatch {
            expected: "Seq",
            found,
        }),
    }
}

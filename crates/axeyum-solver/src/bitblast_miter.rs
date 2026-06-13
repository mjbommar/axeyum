//! Certified bit-blasting by an independent-reference miter (track a, path B).
//!
//! [`certify_bitblast_by_miter`] proves, with a DRAT-checked refutation, that the
//! production bit-blasting (`axeyum-bv`) agrees with a **separately coded
//! reference** bit-blaster on **every** input — i.e. the reduction faithfully
//! computes the term. It builds one AIG holding *both* encodings over shared
//! symbol-bit inputs, forms the miter `OR over output bits (fast_bit XOR
//! ref_bit)`, Tseitin-encodes it, and refutes it with the proof-producing SAT
//! core; an `unsat` miter means the two never disagree (exhaustive, not sampled),
//! and a `sat` miter is a faithfulness bug with a witness.
//!
//! This upgrades the sampled [`crate::check_qf_bv_faithfulness`] to a real
//! certificate, for the operator fragment the reference covers (Boolean
//! connectives, bit-vector bitwise ops, `eq`, `ite`). It is sound *modulo trust
//! in the reference*, which is independent of the production code (so production
//! code bugs surface as miter `sat`) — the project's two-independent-procedures
//! pattern applied to bit-blasting. Operators the reference does not yet cover
//! (arithmetic, shifts, concat/extract) return [`BitblastMiterOutcome::NotCertifiable`].

use std::collections::HashMap;

use axeyum_aig::{Aig, AigInputId, AigLit, AigNode};
use axeyum_bv::{first_unsupported_op, first_unsupported_sort, lower_terms};
use axeyum_cnf::{
    ProofSolveOutcome, check_drat, solve_with_drat_proof, tseitin_encode, write_drat,
};
use axeyum_ir::{Op, Sort, SymbolId, TermArena, TermId, TermNode};

use crate::backend::SolverError;

/// The outcome of [`certify_bitblast_by_miter`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BitblastMiterOutcome {
    /// The production and reference bit-blastings provably agree on **all**
    /// inputs: the miter is unsatisfiable with a DRAT-checked refutation. Carries
    /// the auditable certificate (the miter CNF in DIMACS and its DRAT proof).
    Certified {
        /// The miter CNF in DIMACS format.
        dimacs: String,
        /// The DRAT refutation, verified by `check_drat`.
        drat: String,
    },
    /// The two bit-blastings disagree on some input — a faithfulness bug.
    Diverged,
    /// The proof core exhausted its conflict budget without deciding.
    Inconclusive,
    /// The query uses an operator or sort the reference bit-blaster does not
    /// cover, so no miter was built.
    NotCertifiable,
}

/// Certifies the production bit-blasting of `roots` faithful via an
/// independent-reference miter.
///
/// # Errors
///
/// Returns [`SolverError::Backend`] on an internal encoding failure or a proof
/// that fails to check (a soundness alarm). Unsupported operators/sorts yield
/// [`BitblastMiterOutcome::NotCertifiable`], not an error.
pub fn certify_bitblast_by_miter(
    arena: &TermArena,
    roots: &[TermId],
) -> Result<BitblastMiterOutcome, SolverError> {
    // Anything the production bit-blaster cannot lower is out of scope.
    if first_unsupported_sort(arena, roots).is_some()
        || first_unsupported_op(arena, roots).is_some()
    {
        return Ok(BitblastMiterOutcome::NotCertifiable);
    }
    let Ok(lowering) = lower_terms(arena, roots) else {
        return Ok(BitblastMiterOutcome::NotCertifiable);
    };

    // One combined AIG holds both encodings; shared inputs are created per
    // symbol bit, mapped both by the production AIG's input id (for copying) and
    // by (symbol, bit) (for the reference).
    let mut aig = Aig::new();
    let mut input_to_shared: HashMap<AigInputId, AigLit> = HashMap::new();
    let mut symbol_bit_to_shared: HashMap<(SymbolId, u32), AigLit> = HashMap::new();
    for binding in lowering.symbol_inputs() {
        let lit = aig.input(format!("{}#{}", binding.symbol_name, binding.bit_index));
        input_to_shared.insert(binding.input, lit);
        symbol_bit_to_shared.insert((binding.symbol, binding.bit_index), lit);
    }

    // Copy the production AIG into the combined AIG, remapping its inputs.
    let fast_map = copy_aig(&mut aig, lowering.aig(), &input_to_shared);

    // Reference-encode each root over the same shared inputs and miter against
    // the (copied) production bits.
    let mut memo: HashMap<TermId, Vec<AigLit>> = HashMap::new();
    let mut miter = AigLit::FALSE;
    for (k, &root) in roots.iter().enumerate() {
        let Some(reference_bits) =
            reference_bits(arena, root, &symbol_bit_to_shared, &mut aig, &mut memo)
        else {
            return Ok(BitblastMiterOutcome::NotCertifiable);
        };
        let production_bits: Vec<AigLit> = lowering.roots()[k]
            .bits()
            .iter()
            .map(|&lit| map_lit(&fast_map, lit))
            .collect();
        if production_bits.len() != reference_bits.len() {
            // A width disagreement is itself a faithfulness divergence.
            return Ok(BitblastMiterOutcome::Diverged);
        }
        for (fast, refb) in production_bits.into_iter().zip(reference_bits) {
            let differ = aig.xor(fast, refb);
            miter = aig.or(miter, differ);
        }
    }

    let encoding = tseitin_encode(&aig, &[miter])
        .map_err(|error| SolverError::Backend(format!("miter CNF encoding failed: {error}")))?;
    let formula = encoding.formula();
    match solve_with_drat_proof(formula) {
        ProofSolveOutcome::Sat(_) => Ok(BitblastMiterOutcome::Diverged),
        ProofSolveOutcome::ResourceOut => Ok(BitblastMiterOutcome::Inconclusive),
        ProofSolveOutcome::Unsat(proof) => match check_drat(formula, &proof) {
            Ok(true) => Ok(BitblastMiterOutcome::Certified {
                dimacs: formula.to_dimacs(),
                drat: write_drat(&proof),
            }),
            Ok(false) => Err(SolverError::Backend(
                "bit-blast miter proof did not derive the empty clause".to_owned(),
            )),
            Err(error) => Err(SolverError::Backend(format!(
                "bit-blast miter proof failed to check: {error}"
            ))),
        },
    }
}

/// Copies every node of `src` into `dst`, remapping inputs through `input_map`,
/// and returns a map from each `src` node id to the corresponding `dst` literal.
fn copy_aig(dst: &mut Aig, src: &Aig, input_map: &HashMap<AigInputId, AigLit>) -> Vec<AigLit> {
    let mut map = vec![AigLit::FALSE; src.node_count()];
    for (id, node) in src.nodes() {
        let lit = match node {
            AigNode::ConstFalse => AigLit::FALSE,
            AigNode::Input(input_id) => *input_map
                .get(&input_id)
                .expect("every production AIG input is a known symbol bit"),
            AigNode::And(a, b) => {
                let la = lit_in(&map, a);
                let lb = lit_in(&map, b);
                dst.and(la, lb)
            }
        };
        map[id.index()] = lit;
    }
    map
}

/// Resolves a `src` literal to its `dst` literal via the node map, preserving
/// polarity.
fn lit_in(map: &[AigLit], lit: AigLit) -> AigLit {
    let base = map[lit.node().index()];
    if lit.is_inverted() {
        base.negated()
    } else {
        base
    }
}

/// Alias for clarity at the call site.
fn map_lit(map: &[AigLit], lit: AigLit) -> AigLit {
    lit_in(map, lit)
}

/// The bit width of a term's sort (`Bool` is one bit).
fn term_width(arena: &TermArena, term: TermId) -> Option<u32> {
    match arena.sort_of(term) {
        Sort::Bool => Some(1),
        Sort::BitVec(width) => Some(width),
        _ => None,
    }
}

/// Independently bit-blasts `term` (LSB-first) over the shared symbol inputs, for
/// the covered operator fragment. Returns `None` for any uncovered operator/sort.
fn reference_bits(
    arena: &TermArena,
    term: TermId,
    shared: &HashMap<(SymbolId, u32), AigLit>,
    aig: &mut Aig,
    memo: &mut HashMap<TermId, Vec<AigLit>>,
) -> Option<Vec<AigLit>> {
    if let Some(bits) = memo.get(&term) {
        return Some(bits.clone());
    }
    let bits = match arena.node(term).clone() {
        TermNode::BoolConst(value) => vec![bool_lit(value)],
        TermNode::BvConst { width, value } => (0..width)
            .map(|i| bool_lit((value >> i) & 1 == 1))
            .collect(),
        TermNode::Symbol(symbol) => {
            let width = term_width(arena, term)?;
            (0..width)
                .map(|i| shared.get(&(symbol, i)).copied())
                .collect::<Option<Vec<_>>>()?
        }
        TermNode::App { op, args } => {
            // Reference-encode every argument first.
            let mut arg_bits = Vec::with_capacity(args.len());
            for &arg in &args {
                arg_bits.push(reference_bits(arena, arg, shared, aig, memo)?);
            }
            reference_op(op, &arg_bits, aig)?
        }
        // Integer/real constants never reach the bit-blaster.
        TermNode::IntConst(_) | TermNode::RealConst(_) => return None,
    };
    memo.insert(term, bits.clone());
    Some(bits)
}

/// Applies the reference gadget for `op` to its arguments' bit vectors.
fn reference_op(op: Op, args: &[Vec<AigLit>], aig: &mut Aig) -> Option<Vec<AigLit>> {
    let bits = match op {
        Op::BoolNot => vec![args[0][0].negated()],
        Op::BoolAnd => vec![aig.and(args[0][0], args[1][0])],
        Op::BoolOr => vec![aig.or(args[0][0], args[1][0])],
        Op::BoolXor => vec![aig.xor(args[0][0], args[1][0])],
        Op::BoolImplies => {
            let lhs = args[0][0].negated();
            vec![aig.or(lhs, args[1][0])]
        }
        Op::BvNot => args[0].iter().map(|&b| b.negated()).collect(),
        Op::BvAnd => zip_map(&args[0], &args[1], |a, b| aig.and(a, b))?,
        Op::BvOr => zip_map(&args[0], &args[1], |a, b| aig.or(a, b))?,
        Op::BvXor => zip_map(&args[0], &args[1], |a, b| aig.xor(a, b))?,
        Op::BvNand => zip_map(&args[0], &args[1], |a, b| aig.and(a, b).negated())?,
        Op::BvNor => zip_map(&args[0], &args[1], |a, b| aig.or(a, b).negated())?,
        Op::BvXnor => zip_map(&args[0], &args[1], |a, b| aig.xor(a, b).negated())?,
        // Equality over any covered sort: AND of bitwise xnor; result is one bit.
        Op::Eq => {
            if args[0].len() != args[1].len() {
                return None;
            }
            let mut acc = AigLit::TRUE;
            for (&a, &b) in args[0].iter().zip(&args[1]) {
                let same = aig.xor(a, b).negated();
                acc = aig.and(acc, same);
            }
            vec![acc]
        }
        // `ite(c, t, e)`: `c` is one bit; mux each result bit.
        Op::Ite => {
            let cond = args[0][0];
            if args[1].len() != args[2].len() {
                return None;
            }
            args[1]
                .iter()
                .zip(&args[2])
                .map(|(&t, &e)| aig.mux(cond, t, e))
                .collect()
        }
        // Everything else (arithmetic, shifts, concat/extract, comparisons,
        // extensions, apply, quantifiers) is not yet covered by the reference.
        _ => return None,
    };
    Some(bits)
}

/// Bit width of a constant Boolean literal.
fn bool_lit(value: bool) -> AigLit {
    if value { AigLit::TRUE } else { AigLit::FALSE }
}

/// Maps two equal-length bit vectors elementwise; `None` on a width mismatch.
fn zip_map(
    a: &[AigLit],
    b: &[AigLit],
    mut combine: impl FnMut(AigLit, AigLit) -> AigLit,
) -> Option<Vec<AigLit>> {
    if a.len() != b.len() {
        return None;
    }
    Some(a.iter().zip(b).map(|(&x, &y)| combine(x, y)).collect())
}

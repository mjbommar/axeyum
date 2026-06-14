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
//! certificate, and the reference now covers the **entire supported `QF_BV`
//! operator set**: Boolean connectives, bitwise ops, `eq`/`bvcomp`, `ite`,
//! arithmetic (`bvadd`/`bvsub`/`bvneg`/`bvmul`), all comparisons (unsigned and
//! signed), shifts (`bvshl`/`bvlshr`/`bvashr`), the structural ops
//! (concat/extract, zero/sign extension, constant rotates), and unsigned/signed
//! division/remainder/modulo (a restoring divider with SMT-LIB totality). It is
//! sound *modulo trust in the reference*, which is independent of the production
//! code (so production code bugs surface as miter `sat`) — the project's
//! two-independent-procedures pattern applied to bit-blasting. Constructs not
//! bit-blasted at all (uninterpreted-function `apply`, quantifiers) return
//! [`BitblastMiterOutcome::NotCertifiable`].

use std::collections::HashMap;

use axeyum_aig::{Aig, AigInputId, AigLit, AigNode};
use axeyum_bv::{first_unsupported_op, first_unsupported_sort, lower_terms};
use axeyum_cnf::{
    ProofSolveOutcome, check_drat, solve_with_drat_proof, tseitin_encode, write_drat,
};
use axeyum_ir::{Op, Sort, SymbolId, TermArena, TermId, TermNode};

use crate::backend::SolverError;
use crate::proof::{UnsatProof, UnsatProofOutcome, export_qf_bv_unsat_proof};

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

/// An **end-to-end** `QF_BV` `unsat` certificate: the reduction is certified
/// faithful (the miter) *and* the resulting CNF is certified unsatisfiable (DRAT).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EndToEndUnsatOutcome {
    /// Term-level `unsat`, certified end to end. The faithfulness miter proves
    /// the production bit-blasting matches the independent reference on all
    /// inputs; the refutation proves the bit-blasted CNF unsatisfiable; the
    /// Tseitin step between them is equisatisfiability-preserving by construction.
    /// Sound modulo trust in the independent reference bit-blaster.
    Certified {
        /// The bit-blast-faithfulness miter certificate (DIMACS).
        faithfulness_dimacs: String,
        /// The bit-blast-faithfulness miter refutation (DRAT).
        faithfulness_drat: String,
        /// The CNF-`unsat` refutation (DIMACS + DRAT).
        unsat: UnsatProof,
    },
    /// The query is satisfiable, so there is no `unsat` to certify.
    Satisfiable,
    /// Could not certify end to end (an uncovered operator, or an inconclusive
    /// proof core).
    NotCertified,
}

/// Produces an end-to-end `QF_BV` `unsat` certificate by composing the
/// bit-blast-faithfulness miter ([`certify_bitblast_by_miter`]) with the
/// CNF-`unsat` DRAT proof ([`export_qf_bv_unsat_proof`]).
///
/// Together these establish *term-level* `unsat`: the term equals its AIG (miter,
/// modulo the independent reference), the AIG equals the CNF (Tseitin, by
/// construction), and the CNF is unsatisfiable (DRAT) — closing the term↔CNF gap
/// at scale, the goal of track (a) path (B).
///
/// # Errors
///
/// Returns [`SolverError::Backend`] if the miter reveals the production
/// bit-blasting **diverges** from the reference (a soundness alarm) or on an
/// internal failure; uncovered operators yield
/// [`EndToEndUnsatOutcome::NotCertified`].
pub fn certify_qf_bv_unsat_end_to_end(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<EndToEndUnsatOutcome, SolverError> {
    // 1. The bit-blasting of the assertions must be certified faithful.
    let (faithfulness_dimacs, faithfulness_drat) =
        match certify_bitblast_by_miter(arena, assertions)? {
            BitblastMiterOutcome::Certified { dimacs, drat } => (dimacs, drat),
            BitblastMiterOutcome::Diverged => {
                return Err(SolverError::Backend(
                "soundness alarm: production bit-blasting diverges from the independent reference"
                    .to_owned(),
            ));
            }
            BitblastMiterOutcome::Inconclusive | BitblastMiterOutcome::NotCertifiable => {
                return Ok(EndToEndUnsatOutcome::NotCertified);
            }
        };

    // 2. The resulting CNF must be unsatisfiable with a DRAT-checked proof.
    match export_qf_bv_unsat_proof(arena, assertions)? {
        UnsatProofOutcome::Proved(unsat) => Ok(EndToEndUnsatOutcome::Certified {
            faithfulness_dimacs,
            faithfulness_drat,
            unsat,
        }),
        UnsatProofOutcome::Satisfiable => Ok(EndToEndUnsatOutcome::Satisfiable),
        UnsatProofOutcome::Inconclusive => Ok(EndToEndUnsatOutcome::NotCertified),
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
        TermNode::WideBvConst(w) => w.to_lsb_bits().into_iter().map(bool_lit).collect(),
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
            vec![ref_eq_bits(aig, &args[0], &args[1])]
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
        // --- arithmetic (textbook gadgets, independent of the production code) -
        Op::BvNeg => ref_neg(aig, &args[0]),
        Op::BvAdd => ref_add(aig, &args[0], &args[1], AigLit::FALSE).0,
        Op::BvSub => ref_sub(aig, &args[0], &args[1]),
        Op::BvMul => ref_mul(aig, &args[0], &args[1]),
        // --- shifts (barrel shifter; SMT-LIB over-shift totality) -------------
        Op::BvShl => ref_shift_left(aig, &args[0], &args[1]),
        Op::BvLshr => ref_shift_right(aig, &args[0], &args[1], false),
        Op::BvAshr => ref_shift_right(aig, &args[0], &args[1], true),
        // --- comparisons (via the subtractor's borrow / sign) -----------------
        Op::BvUlt => vec![ref_ult(aig, &args[0], &args[1])],
        Op::BvUgt => vec![ref_ult(aig, &args[1], &args[0])],
        Op::BvUle => {
            let lt = ref_ult(aig, &args[0], &args[1]);
            let eq = ref_eq_bits(aig, &args[0], &args[1]);
            vec![aig.or(lt, eq)]
        }
        Op::BvUge => vec![ref_ult(aig, &args[0], &args[1]).negated()],
        Op::BvSlt => vec![ref_slt(aig, &args[0], &args[1])],
        Op::BvSgt => vec![ref_slt(aig, &args[1], &args[0])],
        Op::BvSle => {
            let lt = ref_slt(aig, &args[0], &args[1]);
            let eq = ref_eq_bits(aig, &args[0], &args[1]);
            vec![aig.or(lt, eq)]
        }
        Op::BvSge => vec![ref_slt(aig, &args[0], &args[1]).negated()],
        // `bvcomp`: 1-bit BV, 1 iff all bits equal.
        Op::BvComp => vec![ref_eq_bits(aig, &args[0], &args[1])],
        // --- structural -------------------------------------------------------
        // `concat(hi, lo)`: SMT-LIB puts the first operand at the high end; in
        // LSB-first order that is the low operand's bits followed by the high's.
        Op::Concat => {
            let mut bits = args[1].clone();
            bits.extend_from_slice(&args[0]);
            bits
        }
        // `extract[hi:lo]`: the inclusive LSB-first slice.
        Op::Extract { hi, lo } => {
            let (lo, hi) = (lo as usize, hi as usize);
            if hi >= args[0].len() || lo > hi {
                return None;
            }
            args[0][lo..=hi].to_vec()
        }
        // Zero/sign extension append `by` high bits (zero / the sign bit).
        Op::ZeroExt { by } => {
            let mut bits = args[0].clone();
            bits.extend(std::iter::repeat_n(AigLit::FALSE, by as usize));
            bits
        }
        Op::SignExt { by } => {
            let sign = *args[0].last()?;
            let mut bits = args[0].clone();
            bits.extend(std::iter::repeat_n(sign, by as usize));
            bits
        }
        // Constant rotates (amount already reduced modulo width at build time).
        Op::RotateLeft { by } => rotate(&args[0], by as usize, true),
        Op::RotateRight { by } => rotate(&args[0], by as usize, false),
        // Division/remainder/modulo (a restoring divider + SMT-LIB sign/totality
        // wrappers) live in their own helper to keep this dispatch readable.
        Op::BvUdiv | Op::BvUrem | Op::BvSdiv | Op::BvSrem | Op::BvSmod => {
            reference_division(op, args, aig)
        }
        // Still uncovered: apply (uninterpreted functions), quantifiers.
        _ => return None,
    };
    Some(bits)
}

/// Reference gadgets for the division/remainder/modulo operators. `bvudiv`/
/// `bvurem` use the restoring divider with SMT-LIB divide-by-zero totality; the
/// signed forms are sign wrappers over it (the unsigned all-ones totality
/// reproduces the signed by-zero results).
fn reference_division(op: Op, args: &[Vec<AigLit>], aig: &mut Aig) -> Vec<AigLit> {
    match op {
        Op::BvUdiv => ref_udiv_urem(aig, &args[0], &args[1]).0,
        Op::BvUrem => ref_udiv_urem(aig, &args[0], &args[1]).1,
        // `bvsdiv`: |s|/|t| with the sign set by the operands' signs.
        Op::BvSdiv => {
            let (abs_s, sign_s) = ref_abs(aig, &args[0]);
            let (abs_t, sign_t) = ref_abs(aig, &args[1]);
            let quotient = ref_udiv_urem(aig, &abs_s, &abs_t).0;
            let neg_q = ref_neg(aig, &quotient);
            let signs_differ = aig.xor(sign_s, sign_t);
            quotient
                .iter()
                .zip(&neg_q)
                .map(|(&q, &nq)| aig.mux(signs_differ, nq, q))
                .collect()
        }
        // `bvsrem`: remainder with the sign of the dividend.
        Op::BvSrem => {
            let (abs_s, sign_s) = ref_abs(aig, &args[0]);
            let (abs_t, _) = ref_abs(aig, &args[1]);
            let rem = ref_udiv_urem(aig, &abs_s, &abs_t).1;
            let neg_r = ref_neg(aig, &rem);
            rem.iter()
                .zip(&neg_r)
                .map(|(&r, &nr)| aig.mux(sign_s, nr, r))
                .collect()
        }
        // `bvsmod`: modulo with the sign of the divisor (the SMT-LIB 5-case form).
        Op::BvSmod => {
            let (abs_s, sign_s) = ref_abs(aig, &args[0]);
            let (abs_t, sign_t) = ref_abs(aig, &args[1]);
            let u = ref_udiv_urem(aig, &abs_s, &abs_t).1;
            let neg_u = ref_neg(aig, &u);
            let u_plus_t = ref_add(aig, &u, &args[1], AigLit::FALSE).0;
            let negu_plus_t = ref_add(aig, &neg_u, &args[1], AigLit::FALSE).0;
            let mut nonzero = AigLit::FALSE;
            for &bit in &u {
                nonzero = aig.or(nonzero, bit);
            }
            let u_is_zero = nonzero.negated();
            (0..u.len())
                .map(|i| {
                    // signs (s,t): 00→u, 10→neg_u+t, 01→u+t, 11→neg_u; u==0→0.
                    let when_t_neg = aig.mux(sign_s, neg_u[i], u_plus_t[i]);
                    let when_t_pos = aig.mux(sign_s, negu_plus_t[i], u[i]);
                    let sel = aig.mux(sign_t, when_t_neg, when_t_pos);
                    aig.mux(u_is_zero, AigLit::FALSE, sel)
                })
                .collect()
        }
        _ => unreachable!("reference_division handles only div/rem/mod operators"),
    }
}

/// `(|x|, sign_bit)` in two's complement: negate when the sign bit is set.
fn ref_abs(aig: &mut Aig, x: &[AigLit]) -> (Vec<AigLit>, AigLit) {
    let sign = x[x.len() - 1];
    let negated = ref_neg(aig, x);
    let abs = x
        .iter()
        .zip(&negated)
        .map(|(&xi, &ni)| aig.mux(sign, ni, xi))
        .collect();
    (abs, sign)
}

/// Restoring unsigned divider: returns `(bvudiv, bvurem)` with SMT-LIB
/// divide-by-zero totality (`bvudiv x 0 = all-ones`, `bvurem x 0 = x`).
fn ref_udiv_urem(aig: &mut Aig, a: &[AigLit], b: &[AigLit]) -> (Vec<AigLit>, Vec<AigLit>) {
    let width = a.len();
    // Divisor zero-extended by one bit so the partial remainder cannot overflow.
    let mut divisor = b.to_vec();
    divisor.push(AigLit::FALSE);
    let not_divisor: Vec<AigLit> = divisor.iter().map(|&x| x.negated()).collect();

    let mut rem = vec![AigLit::FALSE; width + 1];
    let mut quotient = vec![AigLit::FALSE; width];
    for i in (0..width).rev() {
        // rem = (rem << 1) | a[i]  (the dropped top bit is always zero).
        let mut shifted = Vec::with_capacity(width + 1);
        shifted.push(a[i]);
        shifted.extend_from_slice(&rem[0..width]);
        rem = shifted;

        // ge = rem >= divisor, via the subtractor's carry-out; conditionally
        // restore (subtract) and set the quotient bit.
        let (difference, carry) = ref_add(aig, &rem, &not_divisor, AigLit::TRUE);
        rem = rem
            .iter()
            .zip(&difference)
            .map(|(&keep, &subbed)| aig.mux(carry, subbed, keep))
            .collect();
        quotient[i] = carry;
    }

    // Totality: when the divisor is zero, `bvudiv` is all-ones and `bvurem` is
    // the dividend.
    let mut nonzero = AigLit::FALSE;
    for &bit in b {
        nonzero = aig.or(nonzero, bit);
    }
    let divisor_is_zero = nonzero.negated();
    let udiv = quotient
        .iter()
        .map(|&q| aig.mux(divisor_is_zero, AigLit::TRUE, q))
        .collect();
    let urem = rem[0..width]
        .iter()
        .zip(a)
        .map(|(&r, &dividend)| aig.mux(divisor_is_zero, dividend, r))
        .collect();
    (udiv, urem)
}

/// Rotates `bits` (LSB-first) by `by`; `left` toward the MSB, else toward the LSB.
fn rotate(bits: &[AigLit], by: usize, left: bool) -> Vec<AigLit> {
    let width = bits.len();
    if width == 0 {
        return Vec::new();
    }
    let by = by % width;
    (0..width)
        .map(|i| {
            let src = if left {
                (i + width - by) % width
            } else {
                (i + by) % width
            };
            bits[src]
        })
        .collect()
}

/// One bit: all of `a`'s and `b`'s bits are equal (AND of bitwise xnor).
fn ref_eq_bits(aig: &mut Aig, a: &[AigLit], b: &[AigLit]) -> AigLit {
    let mut acc = AigLit::TRUE;
    for (&x, &y) in a.iter().zip(b) {
        let same = aig.xor(x, y).negated();
        acc = aig.and(acc, same);
    }
    acc
}

/// Ripple-carry adder: returns `(sum, carry_out)` for `a + b + carry_in`
/// (operands equal width; sum truncated to that width).
fn ref_add(aig: &mut Aig, a: &[AigLit], b: &[AigLit], carry_in: AigLit) -> (Vec<AigLit>, AigLit) {
    let mut carry = carry_in;
    let mut sum = Vec::with_capacity(a.len());
    for (&ai, &bi) in a.iter().zip(b) {
        let axb = aig.xor(ai, bi);
        let s = aig.xor(axb, carry);
        let ab = aig.and(ai, bi);
        let carry_and = aig.and(carry, axb);
        carry = aig.or(ab, carry_and);
        sum.push(s);
    }
    (sum, carry)
}

/// Two's-complement negation: `~a + 1`.
fn ref_neg(aig: &mut Aig, a: &[AigLit]) -> Vec<AigLit> {
    let not_a: Vec<AigLit> = a.iter().map(|&x| x.negated()).collect();
    let zeros = vec![AigLit::FALSE; a.len()];
    ref_add(aig, &not_a, &zeros, AigLit::TRUE).0
}

/// Subtraction: `a + ~b + 1`.
fn ref_sub(aig: &mut Aig, a: &[AigLit], b: &[AigLit]) -> Vec<AigLit> {
    let not_b: Vec<AigLit> = b.iter().map(|&x| x.negated()).collect();
    ref_add(aig, a, &not_b, AigLit::TRUE).0
}

/// Shift-and-add multiplier, truncated to the operand width.
fn ref_mul(aig: &mut Aig, a: &[AigLit], b: &[AigLit]) -> Vec<AigLit> {
    let width = a.len();
    let mut acc = vec![AigLit::FALSE; width];
    for (i, &bi) in b.iter().enumerate() {
        let partial: Vec<AigLit> = (0..width)
            .map(|j| {
                if j >= i {
                    aig.and(a[j - i], bi)
                } else {
                    AigLit::FALSE
                }
            })
            .collect();
        acc = ref_add(aig, &acc, &partial, AigLit::FALSE).0;
    }
    acc
}

/// Barrel left shift; a shift amount `>=` width yields zero (SMT-LIB totality).
fn ref_shift_left(aig: &mut Aig, x: &[AigLit], amount: &[AigLit]) -> Vec<AigLit> {
    let width = x.len();
    let mut result = x.to_vec();
    for (i, &si) in amount.iter().enumerate() {
        let shift = if i < 64 { 1usize << i } else { usize::MAX };
        if shift >= width {
            result = result
                .iter()
                .map(|&r| aig.mux(si, AigLit::FALSE, r))
                .collect();
        } else {
            let shifted: Vec<AigLit> = (0..width)
                .map(|j| {
                    if j >= shift {
                        result[j - shift]
                    } else {
                        AigLit::FALSE
                    }
                })
                .collect();
            result = (0..width)
                .map(|j| aig.mux(si, shifted[j], result[j]))
                .collect();
        }
    }
    result
}

/// Barrel right shift; `arithmetic` fills with the sign bit (`bvashr`), else
/// zero (`bvlshr`). Over-shift yields the fill (SMT-LIB totality).
fn ref_shift_right(
    aig: &mut Aig,
    x: &[AigLit],
    amount: &[AigLit],
    arithmetic: bool,
) -> Vec<AigLit> {
    let width = x.len();
    let fill = if arithmetic {
        x[width - 1]
    } else {
        AigLit::FALSE
    };
    let mut result = x.to_vec();
    for (i, &si) in amount.iter().enumerate() {
        let shift = if i < 64 { 1usize << i } else { usize::MAX };
        if shift >= width {
            result = result.iter().map(|&r| aig.mux(si, fill, r)).collect();
        } else {
            let shifted: Vec<AigLit> = (0..width)
                .map(|j| {
                    if j + shift < width {
                        result[j + shift]
                    } else {
                        fill
                    }
                })
                .collect();
            result = (0..width)
                .map(|j| aig.mux(si, shifted[j], result[j]))
                .collect();
        }
    }
    result
}

/// Unsigned less-than: the subtraction `a - b = a + ~b + 1` borrows iff `a < b`,
/// i.e. its carry-out is 0.
fn ref_ult(aig: &mut Aig, a: &[AigLit], b: &[AigLit]) -> AigLit {
    let not_b: Vec<AigLit> = b.iter().map(|&x| x.negated()).collect();
    let (_, carry_out) = ref_add(aig, a, &not_b, AigLit::TRUE);
    carry_out.negated()
}

/// Signed less-than: if the sign bits differ, `a < b` iff `a` is negative;
/// otherwise iff `a - b` is negative.
fn ref_slt(aig: &mut Aig, a: &[AigLit], b: &[AigLit]) -> AigLit {
    let not_b: Vec<AigLit> = b.iter().map(|&x| x.negated()).collect();
    let (diff, _) = ref_add(aig, a, &not_b, AigLit::TRUE);
    let msb = a.len() - 1;
    let signs_differ = aig.xor(a[msb], b[msb]);
    aig.mux(signs_differ, a[msb], diff[msb])
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

#[cfg(test)]
mod reference_grounding {
    //! Grounds the independent reference bit-blaster in the trusted ground
    //! evaluator: for every covered operator, the reference's AIG must evaluate
    //! to the same value as the `axeyum-ir` evaluator on **all** inputs at small
    //! width. Combined with the miter (reference == production at any width),
    //! this anchors path (B)'s trust in the evaluator — the same spec that
    //! anchors `sat` model replay — rather than in the production bit-blaster.

    use super::{Aig, AigLit, reference_bits};
    use axeyum_ir::{Assignment, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval};
    use std::collections::{BTreeMap, BTreeSet, HashMap};

    fn width_of(arena: &TermArena, term: TermId) -> u32 {
        match arena.sort_of(term) {
            Sort::Bool => 1,
            Sort::BitVec(w) => w,
            other => panic!("unexpected sort {other}"),
        }
    }

    fn collect_symbols(arena: &TermArena, term: TermId, out: &mut BTreeMap<SymbolId, u32>) {
        let mut seen = BTreeSet::new();
        let mut stack = vec![term];
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match arena.node(t) {
                TermNode::Symbol(s) => {
                    out.insert(*s, width_of(arena, t));
                }
                TermNode::App { args, .. } => stack.extend(args.iter().copied()),
                _ => {}
            }
        }
    }

    /// Exhaustively checks the reference bit-blasting of `term` against the
    /// evaluator over every assignment to its symbols.
    fn check_exhaustive(arena: &TermArena, term: TermId) {
        let mut symbols = BTreeMap::new();
        collect_symbols(arena, term, &mut symbols);

        let mut aig = Aig::new();
        let mut shared: HashMap<(SymbolId, u32), AigLit> = HashMap::new();
        let mut order: Vec<(SymbolId, u32)> = Vec::new();
        for (&sym, &width) in &symbols {
            for bit in 0..width {
                let lit = aig.input(format!("i{}", order.len()));
                shared.insert((sym, bit), lit);
                order.push((sym, bit));
            }
        }
        let mut memo = HashMap::new();
        let bits = reference_bits(arena, term, &shared, &mut aig, &mut memo)
            .expect("reference covers the term");
        let total = u32::try_from(order.len()).unwrap();
        assert!(total <= 12, "keep the exhaustive enumeration small");
        let result_width = width_of(arena, term);

        for mask in 0u32..(1u32 << total) {
            let inputs: Vec<bool> = (0..order.len()).map(|i| (mask >> i) & 1 == 1).collect();
            let mut assignment = Assignment::new();
            for &sym in symbols.keys() {
                let mut value: u128 = 0;
                for (idx, &(os, ob)) in order.iter().enumerate() {
                    if os == sym && inputs[idx] {
                        value |= 1u128 << ob;
                    }
                }
                let v = match arena.symbol(sym).1 {
                    Sort::Bool => Value::Bool(value & 1 == 1),
                    Sort::BitVec(w) => Value::Bv { width: w, value },
                    other => panic!("unexpected sort {other}"),
                };
                assignment.set(sym, v);
            }
            let ref_bits = aig.eval_many(&bits, &inputs).unwrap();
            let ref_value = match arena.sort_of(term) {
                Sort::Bool => Value::Bool(ref_bits[0]),
                Sort::BitVec(_) => Value::Bv {
                    width: result_width,
                    value: ref_bits
                        .iter()
                        .enumerate()
                        .fold(0u128, |acc, (i, &b)| acc | (u128::from(b) << i)),
                },
                other => panic!("unexpected sort {other}"),
            };
            let term_value = eval(arena, term, &assignment).unwrap();
            assert_eq!(
                ref_value, term_value,
                "reference disagrees with the evaluator at input mask {mask}"
            );
        }
    }

    #[test]
    fn reference_gadgets_match_the_evaluator_exhaustively() {
        // Width 3 for two operands (6 input bits = 64 assignments per term) over
        // a representative set spanning every covered operator family.
        let w = 3;
        let mut arena = TermArena::new();
        let x = arena.bv_var("x", w).unwrap();
        let y = arena.bv_var("y", w).unwrap();
        let terms = [
            arena.bv_and(x, y).unwrap(),
            arena.bv_or(x, y).unwrap(),
            arena.bv_xor(x, y).unwrap(),
            arena.bv_nand(x, y).unwrap(),
            arena.bv_not(x).unwrap(),
            arena.bv_add(x, y).unwrap(),
            arena.bv_sub(x, y).unwrap(),
            arena.bv_neg(x).unwrap(),
            arena.bv_mul(x, y).unwrap(),
            arena.bv_udiv(x, y).unwrap(),
            arena.bv_urem(x, y).unwrap(),
            arena.bv_sdiv(x, y).unwrap(),
            arena.bv_srem(x, y).unwrap(),
            arena.bv_smod(x, y).unwrap(),
            arena.bv_shl(x, y).unwrap(),
            arena.bv_lshr(x, y).unwrap(),
            arena.bv_ashr(x, y).unwrap(),
            arena.eq(x, y).unwrap(),
            arena.bv_ult(x, y).unwrap(),
            arena.bv_ule(x, y).unwrap(),
            arena.bv_ugt(x, y).unwrap(),
            arena.bv_uge(x, y).unwrap(),
            arena.bv_slt(x, y).unwrap(),
            arena.bv_sle(x, y).unwrap(),
            arena.bv_sgt(x, y).unwrap(),
            arena.bv_sge(x, y).unwrap(),
            arena.bv_comp(x, y).unwrap(),
            arena.concat(x, y).unwrap(),
            arena.extract(2, 1, x).unwrap(),
            arena.zero_ext(2, x).unwrap(),
            arena.sign_ext(2, x).unwrap(),
            arena.rotate_left(1, x).unwrap(),
            arena.rotate_right(2, y).unwrap(),
        ];
        for term in terms {
            check_exhaustive(&arena, term);
        }
    }

    #[test]
    fn reference_ite_matches_the_evaluator_exhaustively() {
        let mut arena = TermArena::new();
        let c = arena.bool_var("c").unwrap();
        let x = arena.bv_var("x", 3).unwrap();
        let y = arena.bv_var("y", 3).unwrap();
        let ite = arena.ite(c, x, y).unwrap();
        check_exhaustive(&arena, ite);
    }
}

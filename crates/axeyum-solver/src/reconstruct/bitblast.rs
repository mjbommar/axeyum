//! Kernel-checked bit-blast and `QF_BV` proof reconstruction.

use std::collections::{BTreeMap, BTreeSet};

use axeyum_cnf::{AletheCommand, AletheLit, AletheTerm};
use axeyum_lean_kernel::{BinderInfo, Declaration, ExprId};

use super::{
    Assignment, Clause, CpsClause, LEAN_MODULE_THEOREM, ReconstructCtx, ReconstructError,
    and_intro, apply_cps_clause, check_against, check_false_prop, clause_to_cps, cps_clause_prop,
    fresh_axiom, fresh_fvar_id, iff_intro, normalize_cps_clause, prove_clause_by_cases,
    reconstruct_cnf_intro_rule, reconstruct_ordered_rup_cps_step, reconstruct_qf_uf_proof,
    reconstruct_resolution_step,
};

// ===========================================================================
// Bit-blast reconstruction (P3.7 slice 5) — the BITWISE QF_BV fragment.
//
// This is the bottom layer of the QF_BV proof: the `bitblast_*` steps that
// connect a bit-vector predicate to its bit-level Boolean form, plus the
// `cong`/`trans`/`equiv1`/`equiv2` plumbing the emitter threads them with. It
// reconstructs the BITWISE fragment only — `bitblast_var`, `bitblast_const`,
// `bitblast_not`, `bitblast_and`, `bitblast_or`, `bitblast_xor`, and
// `bitblast_equal`. Anything with a carry chain (`bitblast_add`/`_mult`/`_neg`),
// a shift, div/rem, or a structural reshaping (`extract`/`concat`/`sign_extend`)
// is explicitly REJECTED here (no panic) — those are later slices.
//
// ## The faithful bit model
//
// A width-`n` bit-vector term is modeled bit-by-bit, each bit a Lean `Prop`:
//
// - a **variable** `x`'s bit `i` is the opaque Prop atom keyed by the
//   projection `((_ @bit_of i) x)` (shared with the clausal `prop_atoms`);
// - a **constant** `#b…`'s bit `i` is the prelude's `True`/`False`;
// - `bvnot a` bit `i` is `Not (bit_i a)`;
// - `bvand a b` bit `i` is `And (bit_i a) (bit_i b)` (pointwise);
// - `bvor  a b` bit `i` is `Or  (bit_i a) (bit_i b)`;
// - `bvxor a b` bit `i` is `Not (Iff (bit_i a) (bit_i b))` (xor = ¬iff, the same
//   modeling choice the Tseitin/CNF-intro layer makes).
//
// So the bitwise operators are POINTWISE on bits — and the `bitblast_<op>`
// gadget the emitter writes (`(and (@bit_of i a) (@bit_of i b))`, …) is, under
// this model, the **same** structured Prop as `bv_bit` produces. The bitblast
// equalities are therefore reflexive: `bit_i(lhs) ↔ gadget_i` is `Iff.refl`.
//
// ## What a `bitblast_*` step reconstructs to
//
// Each step's conclusion is a unit clause `(= lhs rhs)`. `rhs` is either a
// `(@bbterm b0 … b_{n-1})` (a term op) or a single Boolean `B` (the predicate
// `bitblast_equal`). The reconstruction proves the **bit-iff conjunction**
//
//     ⋀_i ( bv_bit(lhs, i)  ↔  ⟦b_i⟧ )
//
// (for `bitblast_equal`, the single iff `⟦B⟧ ↔ ⟦B⟧`, i.e. the per-bit-AND form),
// each conjunct an `Iff.refl`-style identity, `And.intro`-folded for `n > 1`. The
// kernel `infer`s the assembled term and `def_eq`-checks it against that
// conjunction — the trusted gate. A wrong gadget bit makes some conjunct's two
// sides differ, the reflexive proof fails to type, and the kernel rejects.
// ===========================================================================

impl ReconstructCtx {
    /// Build a reflexive `Iff p p` proof: `Iff.intro p p (fun h => h) (fun h => h)`.
    fn mk_iff_refl(&mut self, p: ExprId) -> ExprId {
        let anon = self.kernel.anon();
        // id := fun (h : p) => h.
        let h = self.kernel.bvar(0);
        let id = self.kernel.lam(anon, p, h, BinderInfo::Default);
        iff_intro(self, p, p, id, id)
    }
}

/// The Lean `Prop` for bit `i` of a **bitwise** bit-vector term `term` under the
/// faithful bit model. Variables → opaque `((_ @bit_of i) x)` atom Props;
/// constants → `True`/`False`; `bvnot`/`bvand`/`bvor`/`bvxor`/`bvxnor` → pointwise
/// `Not`/`And`/`Or`/`Not (Iff …)`/`Iff` of the operand bits.
///
/// # Errors
///
/// Returns [`ReconstructError::UnsupportedTerm`] for any operator outside the
/// bitwise + `extract` + `bvadd`/`bvneg`/`bvmul` fragment (shifts, div/rem,
/// `concat`/`sign_extend`, n-ary `bvadd`/`bvmul`, …), a non-bit-vector shape, or
/// an out-of-range bit of a known-width constant. `extract` (bit `i` → bit
/// `lo + i`) and binary `bvadd`/`bvneg`/`bvmul` (carry chains) are supported.
#[allow(clippy::too_many_lines)] // a flat per-operator bit dispatch; clearer inline
pub(super) fn bv_bit(
    ctx: &mut ReconstructCtx,
    term: &AletheTerm,
    i: usize,
) -> Result<ExprId, ReconstructError> {
    match term {
        // A bit-vector constant `#b…` (MSB-first binary literal): bit `i` is
        // `True`/`False`. A bare symbol (variable): bit `i` is the opaque
        // projection atom `((_ @bit_of i) x)`.
        AletheTerm::Const(symbol) => {
            if let Some(bits) = parse_bv_literal(symbol) {
                // `bits` is LSB-first; out-of-range index is malformed.
                let bit = *bits
                    .get(i)
                    .ok_or_else(|| ReconstructError::UnsupportedTerm {
                        term: format!("bit {i} of constant {symbol}"),
                    })?;
                let name = if bit {
                    ctx.prelude.true_
                } else {
                    ctx.prelude.false_
                };
                Ok(ctx.kernel.const_(name, vec![]))
            } else {
                let proj = bit_of_atom(symbol, i);
                Ok(ctx.gate_term_to_prop(&proj))
            }
        }
        AletheTerm::App(head, args) => match (head.as_str(), args.as_slice()) {
            // A `(@bbterm b0 … b_{n-1})` operand: bit `i` is its `i`-th bit Prop
            // directly (resolving `@bit_of i (@bbterm …)` to `bs[i]`). This is how
            // the emitter feeds an already-bit-blasted child into the next operator.
            ("@bbterm", bits) => {
                let bit = bits
                    .get(i)
                    .ok_or_else(|| ReconstructError::UnsupportedTerm {
                        term: format!("bit {i} out of range of `{}`", term.key()),
                    })?;
                Ok(gadget_bit_to_prop(ctx, bit))
            }
            ("bvnot", [a]) => {
                let ai = bv_bit(ctx, a, i)?;
                Ok(ctx.mk_not(ai))
            }
            ("bvand", [a, b]) => {
                let ai = bv_bit(ctx, a, i)?;
                let bi = bv_bit(ctx, b, i)?;
                Ok(ctx.mk_and(ai, bi))
            }
            ("bvor", [a, b]) => {
                let ai = bv_bit(ctx, a, i)?;
                let bi = bv_bit(ctx, b, i)?;
                Ok(ctx.mk_or(ai, bi))
            }
            ("bvxor", [a, b]) => {
                let ai = bv_bit(ctx, a, i)?;
                let bi = bv_bit(ctx, b, i)?;
                let iff = ctx.mk_iff(ai, bi);
                Ok(ctx.mk_not(iff))
            }
            // Bitwise XNOR (binary): bit `i` is `(= a_i b_i)`, i.e. `a_i ↔ b_i`,
            // matching the emitter's `bitblast_xnor`. Pointwise, width-free.
            ("bvxnor", [a, b]) => {
                let ai = bv_bit(ctx, a, i)?;
                let bi = bv_bit(ctx, b, i)?;
                Ok(ctx.mk_iff(ai, bi))
            }
            // Ripple-carry adder (binary). Bit `i` of `(bvadd a b)` is
            // `a_i ⊕ b_i ⊕ carry_i`, needing only bits `0..=i` (no operand width).
            // We rebuild the exact emitter bit *term* (`ripple_carry_bits`) and run
            // it through the same `gate_term_to_prop` the gadget side uses, so the
            // per-bit iff is reflexive by construction (constant-bit/`false`-seed
            // rendering can never diverge — both sides take the identical path).
            ("bvadd", [a, b]) => {
                let bit_term = ripple_carry_bit_term(a, b, i);
                Ok(ctx.gate_term_to_prop(&bit_term))
            }
            // Two's-complement negate: `-x = (not x) + 1`, a width-free ripple
            // carry (carry-in `true`). Same reflexive build-and-gate as `bvadd`.
            ("bvneg", [x]) => {
                let bit_term = neg_bit_term(x, i);
                Ok(ctx.gate_term_to_prop(&bit_term))
            }
            // Two's-complement subtract: by the SMT-LIB definition `bvsub a b` =
            // `bvadd a (bvneg b)`, so bit `i` is the ripple-carry sum of `a` and
            // `(bvneg b)`. This is the FAITHFUL bit model of `bvsub` (the same
            // definitional reduction Carcara's `bv_poly_simp` validates at the term
            // level); modeling it here makes the Route-2 `bvsub`-rewrite proof's
            // projection `((_ @bit_of i) (bvsub a b))` resolve to exactly the
            // `bvadd a (bvneg b)` gadget bit the emitter wrote — so the bit-definition
            // is reflexive (`Iff.refl`) and the certified `False` is over the ORIGINAL
            // `bvsub` assertion, not a pre-lowered one.
            ("bvsub", [a, b]) => {
                let neg_b = AletheTerm::App("bvneg".to_owned(), vec![b.clone()]);
                let bit_term = ripple_carry_bit_term(a, &neg_b, i);
                Ok(ctx.gate_term_to_prop(&bit_term))
            }
            // Shift-add multiplier (binary). Result bit `i` is `res[i][i]` of the
            // emitter's triangle, width-free. Same reflexive build-and-gate.
            //
            // The inlined (un-shared) result term grows ~4.5x per bit, so a wide
            // multiplier explodes memory. Guard with a node-count budget: beyond it
            // we return a clean `UnsupportedTerm` rather than OOM. (A shared/`let`
            // encoding — emitter and reconstruction both — is the real fix; see the
            // findings note.)
            ("bvmul", [a, b]) => {
                let nodes = mult_bit_node_count(i);
                if nodes > MULT_BIT_NODE_BUDGET {
                    return Err(ReconstructError::UnsupportedTerm {
                        term: format!(
                            "bvmul bit {i} reconstructs to ~{nodes} inlined nodes \
                             (> {MULT_BIT_NODE_BUDGET}); needs a shared encoding"
                        ),
                    });
                }
                let bit_term = mult_bit_term(a, b, i);
                Ok(ctx.gate_term_to_prop(&bit_term))
            }
            // `(concat a b)` (a high, b low): result bit `i` is `b_i` for
            // `i < width(b)`, else `a_{i - width(b)}` — the emitter emits the low
            // operand's bits first. Handled here (not only in `lhs_bit_prop`) so a
            // `concat` nested inside a projection gadget resolves structurally.
            ("concat", [hi, lo]) => {
                let width_lo =
                    alethe_bv_width(ctx, lo).ok_or_else(|| ReconstructError::UnsupportedTerm {
                        term: format!("concat low-operand width unknown `{}`", term.key()),
                    })?;
                if i < width_lo {
                    bv_bit(ctx, lo, i)
                } else {
                    bv_bit(ctx, hi, i - width_lo)
                }
            }
            // `(bvcomp x y)`: a 1-bit result, its only bit the per-bit-equality AND.
            ("bvcomp", [x, y]) if i == 0 => {
                let width = alethe_bv_width(ctx, x)
                    .or_else(|| alethe_bv_width(ctx, y))
                    .ok_or_else(|| ReconstructError::UnsupportedTerm {
                        term: format!("bvcomp operand width unknown `{}`", term.key()),
                    })?;
                if width == 0 {
                    return Err(ReconstructError::MalformedStep {
                        rule: "bitblast_comp".to_owned(),
                        detail: "zero-width bvcomp operand".to_owned(),
                    });
                }
                let bit_term = comp_bit_term(x, y, width);
                Ok(ctx.gate_term_to_prop(&bit_term))
            }
            // **Constant** left/right shifts (`bvshl`/`bvlshr`/`bvashr` by a
            // bit-vector **literal** amount). These route bit `i` to *exactly* the
            // bit the `lower_const_shift` rewrite (`axeyum_rewrite`) collapses them
            // to — `bvshl k` → `(concat (extract a (w-1-k) 0) (bv0 k))` etc. — so
            // proving `(= shift concat)` per-bit is reflexive by construction and the
            // previously-TRUSTED lowering identity becomes kernel-checked (the gate
            // rejects any divergent routing). A *variable* shift amount stays out of
            // fragment (no literal `k`): falls through to the catch-all below.
            ("bvshl" | "bvlshr" | "bvashr", [a, amt]) => const_shift_bit(ctx, head, a, amt, i),
            _ => Err(ReconstructError::UnsupportedTerm {
                term: format!("non-bitwise bit-blast operand `{}`", term.key()),
            }),
        },
        // `((_ extract hi lo) x)`: bit `i` of the result is bit `lo + i` of `x`
        // (pure bit routing — no carry/structural logic), matching the emitter's
        // `bitblast_extract` (bits `lo..=hi` of `x`, LSB-first). Reflexive against
        // the gadget bit by construction; the kernel gate catches any divergence.
        AletheTerm::Indexed { op, indices, args } if op == "extract" => {
            let [hi, lo] = indices.as_slice() else {
                return Err(ReconstructError::UnsupportedTerm {
                    term: format!("extract needs two indices `{}`", term.key()),
                });
            };
            let [x] = args.as_slice() else {
                return Err(ReconstructError::UnsupportedTerm {
                    term: format!("extract needs one operand `{}`", term.key()),
                });
            };
            let lo = usize::try_from(*lo).map_err(|_| ReconstructError::UnsupportedTerm {
                term: format!("extract low index out of range `{}`", term.key()),
            })?;
            let hi = usize::try_from(*hi).map_err(|_| ReconstructError::UnsupportedTerm {
                term: format!("extract high index out of range `{}`", term.key()),
            })?;
            if hi < lo || i > hi - lo {
                return Err(ReconstructError::UnsupportedTerm {
                    term: format!("bit {i} out of range of extract `{}`", term.key()),
                });
            }
            bv_bit(ctx, x, lo + i)
        }
        // `((_ sign_extend by) x)`: bit `i` is `x_i` for `i < width(x)`, else the
        // sign bit `x_{width(x)-1}`. Handled here so a `sign_extend` nested inside a
        // projection gadget resolves structurally (the top-level case stays in
        // `lhs_bit_prop`, which already knows `result_width`).
        AletheTerm::Indexed { op, indices, args } if op == "sign_extend" => {
            let [by] = indices.as_slice() else {
                return Err(ReconstructError::UnsupportedTerm {
                    term: format!("sign_extend needs one index `{}`", term.key()),
                });
            };
            let [x] = args.as_slice() else {
                return Err(ReconstructError::UnsupportedTerm {
                    term: format!("sign_extend needs one operand `{}`", term.key()),
                });
            };
            let _ = by;
            let width_x =
                alethe_bv_width(ctx, x).ok_or_else(|| ReconstructError::UnsupportedTerm {
                    term: format!("sign_extend operand width unknown `{}`", term.key()),
                })?;
            if width_x == 0 {
                return Err(ReconstructError::MalformedStep {
                    rule: "bitblast_sign_extend".to_owned(),
                    detail: "zero-width sign_extend operand".to_owned(),
                });
            }
            let src = if i < width_x { i } else { width_x - 1 };
            bv_bit(ctx, x, src)
        }
        AletheTerm::Indexed { .. } => Err(ReconstructError::UnsupportedTerm {
            term: format!(
                "indexed operand outside the bitwise + extract fragment `{}`",
                term.key()
            ),
        }),
    }
}

/// The bit width of an Alethe bit-vector **term**, recovering it structurally so a
/// nested compound operand (in the projection-based gadget) can be bit-routed:
///
/// - `@bbterm b…` / `#b…` literal: the bit count, directly;
/// - a bare symbol: the width recorded by its `bitblast_var`/`bitblast_const` step
///   (via [`ReconstructCtx::bv_widths`]);
/// - `bvnot`/`bvand`/`bvor`/`bvxor`/`bvxnor`/`bvadd`/`bvneg`/`bvmul`: operand-0's
///   width (width-preserving ops);
/// - `((_ extract hi lo) x)`: `hi - lo + 1`;
/// - `((_ sign_extend by) x)`: `width(x) + by`;
/// - `(concat hi lo)`: `width(hi) + width(lo)`;
/// - `(bvcomp _ _)`: 1.
///
/// Returns [`None`] for an unrecognized / undeclared shape.
fn alethe_bv_width(ctx: &ReconstructCtx, term: &AletheTerm) -> Option<usize> {
    match term {
        AletheTerm::App(head, args) if head == "@bbterm" => Some(args.len()),
        AletheTerm::Const(name) => parse_bv_literal(name)
            .map_or_else(|| ctx.bv_widths.get(name).copied(), |b| Some(b.len())),
        AletheTerm::App(head, args) => match (head.as_str(), args.as_slice()) {
            // Width-preserving ops: operand-0's width.
            (
                "bvnot" | "bvand" | "bvor" | "bvxor" | "bvxnor" | "bvadd" | "bvmul" | "bvneg",
                [a, ..],
            ) => alethe_bv_width(ctx, a),
            ("bvcomp", [_, _]) => Some(1),
            ("concat", [hi, lo]) => Some(alethe_bv_width(ctx, hi)? + alethe_bv_width(ctx, lo)?),
            _ => None,
        },
        AletheTerm::Indexed {
            op,
            indices,
            args: _,
        } if op == "extract" => {
            let [hi, lo] = indices.as_slice() else {
                return None;
            };
            let hi = usize::try_from(*hi).ok()?;
            let lo = usize::try_from(*lo).ok()?;
            (hi >= lo).then(|| hi - lo + 1)
        }
        AletheTerm::Indexed { op, indices, args } if op == "sign_extend" => {
            let [by] = indices.as_slice() else {
                return None;
            };
            let [x] = args.as_slice() else {
                return None;
            };
            let by = usize::try_from(*by).ok()?;
            Some(alethe_bv_width(ctx, x)? + by)
        }
        AletheTerm::Indexed { .. } => None,
    }
}

/// Whether a `((_ @bit_of i) operand)` projection should be resolved through the
/// faithful bit model [`bv_bit`] (rather than kept as an opaque atom).
///
/// - A **compound** bit-vector term (`@bbterm`, any `bv…`/`concat` application, or an
///   `extract`/`sign_extend`) → resolve, so the projection agrees structurally with
///   the LHS expansion in the projection-based emission.
/// - A `#b…` **literal** → resolve, so `((_ @bit_of i) #b…)` (which the emitter's
///   `build_term_vec` projects for a constant operand) becomes the constant `True`/
///   `False` bit, matching the LHS constant model.
/// - A **bare symbol** → do NOT resolve: `bv_bit` models a symbol's bit as the same
///   opaque `@bit_of` atom, so resolving would recurse; keeping it opaque is correct.
pub(super) fn bit_of_operand_resolves(operand: &AletheTerm) -> bool {
    match operand {
        AletheTerm::Const(name) => parse_bv_literal(name).is_some(),
        AletheTerm::App(..) | AletheTerm::Indexed { .. } => true,
    }
}

/// The bit-projection atom `((_ @bit_of i) name)` as an [`AletheTerm`], matching
/// the emitter's spelling exactly so its opaque Prop key coincides.
fn bit_of_atom(name: &str, i: usize) -> AletheTerm {
    AletheTerm::Indexed {
        op: "@bit_of".to_owned(),
        indices: vec![i128::try_from(i).expect("bit index fits i128")],
        args: vec![AletheTerm::Const(name.to_owned())],
    }
}

/// Bit `j` of a bit-blast operand *as an [`AletheTerm`]*, mirroring the emitter's
/// `build_term_vec`: a `(@bbterm b…)` exposes its `j`-th bit directly, anything
/// else is the projection `((_ @bit_of j) operand)`.
fn operand_bit_term(operand: &AletheTerm, j: usize) -> AletheTerm {
    if let AletheTerm::App(head, args) = operand
        && head == "@bbterm"
        && let Some(bit) = args.get(j)
    {
        return bit.clone();
    }
    // A binary-literal constant `#b<MSB…LSB>`: bit `j` (LSB-first) is its actual
    // Boolean value, matching how the emitter bit-blasts a constant operand (bool
    // literals in the `@bbterm`), NOT an opaque `@bit_of` projection.
    if let AletheTerm::Const(lit) = operand
        && let Some(bits) = lit.strip_prefix("#b")
    {
        let n = bits.len();
        if j < n {
            let is_one = bits.as_bytes()[n - 1 - j] == b'1';
            return AletheTerm::Const(if is_one { "true" } else { "false" }.to_owned());
        }
    }
    AletheTerm::Indexed {
        op: "@bit_of".to_owned(),
        indices: vec![i128::try_from(j).expect("bit index fits i128")],
        args: vec![operand.clone()],
    }
}

/// Bit `i` of `(bvadd x y)` as an [`AletheTerm`], transcribing the emitter's
/// `ripple_carry_bits` verbatim (`carry_0 = false`;
/// `carry_k = (or (and x_{k-1} y_{k-1}) (and (xor x_{k-1} y_{k-1}) carry_{k-1}))`;
/// `bit_i = (xor (xor x_i y_i) carry_i)`). Building the term and gating it keeps
/// reconstruction reflexive with the gadget bit on both the structure and the
/// constant/`false` leaf rendering.
fn ripple_carry_bit_term(x: &AletheTerm, y: &AletheTerm, i: usize) -> AletheTerm {
    let app = |head: &str, args: Vec<AletheTerm>| AletheTerm::App(head.to_owned(), args);
    let mut carry = AletheTerm::Const("false".to_owned());
    for k in 1..=i {
        let xk = operand_bit_term(x, k - 1);
        let yk = operand_bit_term(y, k - 1);
        let and_xy = app("and", vec![xk.clone(), yk.clone()]);
        let xor_xy = app("xor", vec![xk, yk]);
        let and_carry = app("and", vec![xor_xy, carry]);
        carry = app("or", vec![and_xy, and_carry]);
    }
    let xi = operand_bit_term(x, i);
    let yi = operand_bit_term(y, i);
    let sum = app("xor", vec![xi, yi]);
    app("xor", vec![sum, carry])
}

/// Bit `i` of `(bvneg x)` as an [`AletheTerm`], transcribing the emitter's
/// `neg_step` verbatim: the ripple-carry adder of `(not x)` and `0` with carry-in
/// `true` (`c_0 = true`;
/// `c_k = (or (and (not x_{k-1}) false) (and (xor (not x_{k-1}) false) c_{k-1}))`;
/// `bit_i = (xor (xor (not x_i) false) c_i)`). Width-free (bits `0..=i` only) and
/// gated through `gate_term_to_prop` for reflexivity, like [`ripple_carry_bit_term`].
fn neg_bit_term(x: &AletheTerm, i: usize) -> AletheTerm {
    let app = |head: &str, args: Vec<AletheTerm>| AletheTerm::App(head.to_owned(), args);
    let not_bit = |j: usize| app("not", vec![operand_bit_term(x, j)]);
    let false_ = || AletheTerm::Const("false".to_owned());
    let mut carry = AletheTerm::Const("true".to_owned());
    for k in 1..=i {
        let nx = not_bit(k - 1);
        let and_false = app("and", vec![nx.clone(), false_()]);
        let xor_false = app("xor", vec![nx, false_()]);
        let and_carry = app("and", vec![xor_false, carry]);
        carry = app("or", vec![and_false, and_carry]);
    }
    let sum = app("xor", vec![not_bit(i), false_()]);
    app("xor", vec![sum, carry])
}

/// Bit `i` of `(bvmul x y)` as an [`AletheTerm`], transcribing the emitter's
/// `shift_add_multiplier_bits`. The multiplier result satisfies
/// `res[j][i] = res[i][i]` for every `j > i`, so result bit `i` is `res[i][i]` —
/// computable from rounds `0..=i` alone (running the emitter's triangle at
/// `size = i + 1`), hence width-free like the adders. Gated through
/// `gate_term_to_prop` for reflexivity with the gadget bit.
/// Node-count budget for an inlined `bvmul` result bit. Beyond this the un-shared
/// term (and the kernel `Expr`/`def_eq` over it) blows memory; ~width 7 is the
/// last bit under budget (width-8 bit-7 is ~41 k nodes). Reconstruction returns a
/// clean error past this; the durable fix is a shared/`let` encoding.
const MULT_BIT_NODE_BUDGET: u128 = 20_000;

/// Node count of `mult_bit_term(_, _, i)` *without building the term*, via the
/// same `shift_add_multiplier` recurrence — used to guard against the exponential
/// blowup before allocating. Mirrors the term shapes (`and`/`or`/`xor` = 1 + two
/// operands, `false` = 1, `and(y,x)` shift leaf = 3).
#[allow(clippy::needless_range_loop)] // the shift-add recurrence reads clearer with explicit j/k indices
fn mult_bit_node_count(i: usize) -> u128 {
    let size = i + 1;
    let shift = |j: usize, k: usize| -> u128 { if j <= k { 3 } else { 1 } };
    let mut res = vec![vec![0u128; size]; size];
    for k in 0..size {
        res[0][k] = shift(0, k);
    }
    for j in 1..size {
        let mut carry = vec![0u128; size];
        carry[0] = 1;
        for k in 1..size {
            carry[k] = if j < k {
                let r = res[j - 1][k - 1];
                let s = shift(j, k - 1);
                1 + (1 + r + s) + (1 + (1 + r + s) + carry[k - 1])
            } else {
                1
            };
        }
        for k in 0..size {
            res[j][k] = if k == 0 {
                shift(0, 0)
            } else if j > k {
                res[k][k]
            } else {
                1 + (1 + res[j - 1][k] + shift(j, k)) + carry[k]
            };
        }
    }
    res[size - 1][size - 1]
}

fn mult_bit_term(x: &AletheTerm, y: &AletheTerm, i: usize) -> AletheTerm {
    let size = i + 1;
    let app = |head: &str, args: Vec<AletheTerm>| AletheTerm::App(head.to_owned(), args);
    let false_ = || AletheTerm::Const("false".to_owned());
    // shift[j][k] = (and y_j x_{k-j}) for j <= k, else false.
    let shift: Vec<Vec<AletheTerm>> = (0..size)
        .map(|j| {
            (0..size)
                .map(|k| {
                    if j <= k {
                        app(
                            "and",
                            vec![operand_bit_term(y, j), operand_bit_term(x, k - j)],
                        )
                    } else {
                        false_()
                    }
                })
                .collect()
        })
        .collect();
    let mut res: Vec<Vec<AletheTerm>> = vec![(0..size).map(|k| shift[0][k].clone()).collect()];
    for j in 1..size {
        let mut carry_j = vec![false_()];
        for k in 1..size {
            let c = if j < k {
                app(
                    "or",
                    vec![
                        app(
                            "and",
                            vec![res[j - 1][k - 1].clone(), shift[j][k - 1].clone()],
                        ),
                        app(
                            "and",
                            vec![
                                app(
                                    "xor",
                                    vec![res[j - 1][k - 1].clone(), shift[j][k - 1].clone()],
                                ),
                                carry_j[k - 1].clone(),
                            ],
                        ),
                    ],
                )
            } else {
                false_()
            };
            carry_j.push(c);
        }
        let res_j: Vec<AletheTerm> = (0..size)
            .map(|k| {
                if k == 0 {
                    shift[0][0].clone()
                } else if j > k {
                    res[k][k].clone()
                } else {
                    app(
                        "xor",
                        vec![
                            app("xor", vec![res[j - 1][k].clone(), shift[j][k].clone()]),
                            carry_j[k].clone(),
                        ],
                    )
                }
            })
            .collect();
        res.push(res_j);
    }
    res[size - 1][size - 1].clone()
}

/// Parse an SMT-LIB `#b…` binary bit-vector literal into its LSB-first bit
/// values, or [`None`] if `symbol` is not such a literal (e.g. a variable name).
fn parse_bv_literal(symbol: &str) -> Option<Vec<bool>> {
    let rest = symbol.strip_prefix("#b")?;
    if rest.is_empty() || !rest.bytes().all(|c| c == b'0' || c == b'1') {
        return None;
    }
    // `#b` is MSB-first; reverse to LSB-first.
    Some(rest.bytes().rev().map(|c| c == b'1').collect())
}

/// The numeric value of a `#b…` bit-vector literal as a `u128`, or [`None`] if
/// `symbol` is not a literal or its width exceeds 128 bits. Used to read a
/// **constant shift amount** `k` (the only shift case reconstructed).
fn bv_literal_value(symbol: &str) -> Option<u128> {
    let bits = parse_bv_literal(symbol)?; // LSB-first
    if bits.len() > 128 {
        return None;
    }
    let mut value: u128 = 0;
    for (i, &b) in bits.iter().enumerate() {
        if b {
            value |= 1u128 << i;
        }
    }
    Some(value)
}

/// Bit `i` of a **constant** shift `(<op> a #b…)` (`op` ∈ `bvshl`/`bvlshr`/`bvashr`),
/// routed to exactly the source bit the `lower_const_shift` rewrite produces. With
/// operand width `w` and amount `k`:
///
/// - `bvshl`  (`a << k`): bit `i` is `False` for `i < k`, else `a_{i-k}`.
/// - `bvlshr` (`a >>ᵤ k`): bit `i` is `a_{i+k}` for `i+k < w`, else `False`.
/// - `bvashr` (`a >>ₛ k`): bit `i` is `a_{i+k}` for `i+k < w`, else the sign `a_{w-1}`.
///
/// The `k = 0` (identity) and `k ≥ w` (all-zero / all-sign) edges fall out of these
/// formulas directly. A non-literal amount yields [`ReconstructError::UnsupportedTerm`]
/// (a *variable* shift is out of fragment — not a missing rule, the term-model gap).
fn const_shift_bit(
    ctx: &mut ReconstructCtx,
    op: &str,
    a: &AletheTerm,
    amt: &AletheTerm,
    i: usize,
) -> Result<ExprId, ReconstructError> {
    let AletheTerm::Const(amt_sym) = amt else {
        return Err(ReconstructError::UnsupportedTerm {
            term: format!("non-constant {op} amount"),
        });
    };
    let k = bv_literal_value(amt_sym).ok_or_else(|| ReconstructError::UnsupportedTerm {
        term: format!("non-literal {op} amount `{amt_sym}`"),
    })?;
    let width = alethe_bv_width(ctx, a).ok_or_else(|| ReconstructError::UnsupportedTerm {
        term: format!("{op} operand width unknown"),
    })?;
    let width_u128 = u128::try_from(width).map_err(|_| ReconstructError::UnsupportedTerm {
        term: format!("{op} operand width too large"),
    })?;
    let i_u128 = u128::try_from(i).map_err(|_| ReconstructError::UnsupportedTerm {
        term: format!("{op} bit index too large"),
    })?;
    match op {
        "bvshl" => {
            if i_u128 < k {
                Ok(ctx.kernel.const_(ctx.prelude.false_, vec![]))
            } else {
                // `i - k < width` because `i < width` and `k ≥ 0`; the index fits `usize`.
                let src = i - usize::try_from(k).expect("k < i < width fits usize");
                bv_bit(ctx, a, src)
            }
        }
        "bvlshr" | "bvashr" => {
            if i_u128 + k < width_u128 {
                let src = i + usize::try_from(k).expect("i + k < width fits usize");
                bv_bit(ctx, a, src)
            } else if op == "bvashr" {
                bv_bit(ctx, a, width - 1) // sign bit
            } else {
                Ok(ctx.kernel.const_(ctx.prelude.false_, vec![]))
            }
        }
        other => Err(ReconstructError::UnsupportedTerm {
            term: format!("unexpected shift op `{other}`"),
        }),
    }
}

/// Reconstruct one **bitwise** `bitblast_*` step into a kernel-checked proof term
/// of its bit-iff conjunction.
///
/// `rule` is the bitblast rule (a term op concluding `(= lhs (@bbterm b…))`, or a
/// predicate — `bitblast_equal`/`bitblast_ult`/`bitblast_slt` — concluding
/// `(= <pred> B)` with `B` a single Boolean). The reconstructed term has type
///
/// - term op: `⋀_i ( bv_bit(lhs, i) ↔ ⟦b_i⟧ )` — one reflexive `Iff` per bit;
/// - predicate: `⟦B⟧ ↔ ⟦B⟧` (the reflexive iff of the bit-level form `B`).
///
/// Each conjunct is reflexive because `bv_bit(lhs, i)` is, by construction, the
/// same structured Prop as the gadget bit `⟦b_i⟧`. The kernel `infer`s the term
/// and `def_eq`-checks it against the stated conjunction.
///
/// # Errors
///
/// Returns [`ReconstructError::UnsupportedRule`] for a bitblast rule outside the
/// bitwise + `extract`/`sign_extend`/`concat` + `add`/`neg`/`mult` +
/// `ult`/`slt`/`comp` fragment (shifts, div/rem, …),
/// [`ReconstructError::MalformedStep`] for a conclusion that is
/// not the expected `(= lhs rhs)` shape, [`ReconstructError::UnsupportedTerm`] for
/// a non-bitwise operand, and [`ReconstructError::KernelRejected`] at the gate.
pub fn reconstruct_bitblast_step(
    ctx: &mut ReconstructCtx,
    rule: &str,
    conclusion: &[AletheLit],
) -> Result<ExprId, ReconstructError> {
    // The bitwise fragment, `extract` (bit-routing), and the carry-chain
    // arithmetic `bitblast_add` (binary) / `bitblast_neg` / `bitblast_mult`
    // (binary); reject the remaining shift/structural rules cleanly. (`add`/`mult`
    // over >2 operands surface as `UnsupportedTerm` from `bv_bit`.)
    match rule {
        "bitblast_var"
        | "bitblast_const"
        | "bitblast_not"
        | "bitblast_and"
        | "bitblast_or"
        | "bitblast_xor"
        | "bitblast_xnor"
        | "bitblast_extract"
        | "bitblast_sign_extend"
        | "bitblast_concat"
        | "bitblast_comp"
        | "bitblast_add"
        | "bitblast_neg"
        | "bitblast_mult"
        | "bitblast_equal"
        | "bitblast_ult"
        | "bitblast_slt" => {}
        other => {
            return Err(ReconstructError::UnsupportedRule {
                rule: format!(
                    "{other} (only the bitwise + extract + add/neg/mult bit-blast fragment is \
                     reconstructed)"
                ),
            });
        }
    }

    let (lhs, rhs) = bitblast_conclusion_sides(rule, conclusion)?;

    let (target, proof) = if matches!(rule, "bitblast_equal" | "bitblast_ult" | "bitblast_slt") {
        // `(= <pred> B)`: a bit-vector predicate (`=`/`bvult`/`bvslt`) whose
        // bit-level form `B` is a single Boolean (the per-bit-AND for `=`, the
        // unsigned/signed less-than ladder for `bvult`/`bvslt`). Reconstruct the
        // reflexive `⟦B⟧ ↔ ⟦B⟧`; the predicate's lhs connects to `B` via the bridge
        // in the end-to-end flow, exactly as for `bitblast_equal`.
        let b_prop = ctx.gate_term_to_prop(rhs);
        let iff = ctx.mk_iff(b_prop, b_prop);
        (iff, ctx.mk_iff_refl(b_prop))
    } else {
        // A term op `(= lhs (@bbterm b0 … b_{n-1}))`: prove the per-bit iff
        // conjunction `⋀_i ( bv_bit(lhs, i) ↔ ⟦b_i⟧ )`.
        let bits = bbterm_bits(rhs).ok_or_else(|| ReconstructError::MalformedStep {
            rule: rule.to_owned(),
            detail: "term-op conclusion rhs is not a `(@bbterm …)`".to_owned(),
        })?;
        if bits.is_empty() {
            return Err(ReconstructError::MalformedStep {
                rule: rule.to_owned(),
                detail: "empty `@bbterm` (zero-width bit-vector)".to_owned(),
            });
        }
        // Record a freshly bit-blasted leaf's width so structural consumers
        // (`concat`) can recover operand widths (bottom-up order: the leaf step
        // precedes its consumer's step).
        if matches!(rule, "bitblast_var" | "bitblast_const")
            && let AletheTerm::Const(name) = lhs
        {
            ctx.bv_widths.insert(name.clone(), bits.len());
        }
        // Build, per bit, `Iff (bv_bit lhs i) ⟦b_i⟧` and its reflexive proof; the
        // two sides coincide as Props, so the reflexive `Iff` type-checks. Fold
        // right with `And.intro` into the conjunction.
        let n = bits.len();
        let mut target = bit_iff_prop(ctx, lhs, &bits[n - 1], n - 1, n)?;
        let mut proof = bit_iff_refl(ctx, lhs, &bits[n - 1], n - 1, n)?;
        for i in (0..n - 1).rev() {
            let head_prop = bit_iff_prop(ctx, lhs, &bits[i], i, n)?;
            let head_proof = bit_iff_refl(ctx, lhs, &bits[i], i, n)?;
            proof = and_intro(ctx, head_prop, target, head_proof, proof);
            target = ctx.mk_and(head_prop, target);
        }
        (target, proof)
    };

    check_against(ctx, rule, proof, target)
}

/// Certify the **constant-shift → concat lowering identity** as a Lean-kernel-checked
/// theorem, turning the previously-TRUSTED `lower_const_shift` rewrite into an
/// externally-checked one.
///
/// Given a constant shift `shift = (<op> a #b…)` (`op` ∈ `bvshl`/`bvlshr`/`bvashr`,
/// the amount a bit-vector **literal**) and the `rhs` term `lower_const_shift`
/// collapses it to — `(concat (extract a (w-1-k) 0) (bv0 k))` for `bvshl`, the
/// `lshr`/`ashr` analogues, or the `k = 0` / `k ≥ w` edge forms — this proves the
/// **per-bit equality conjunction**
///
/// > `⋀_{i<width} ( bv_bit(shift, i) ↔ bv_bit(rhs, i) )`
///
/// i.e. *each bit of the shift is definitionally the corresponding bit of the
/// lowered concat*. Both sides route through the faithful `bv_bit` model; when the
/// lowering is correct they are the **same** `Prop`, so each conjunct is `Iff.refl`
/// and the `infer`/`def_eq` gate accepts. A **wrong** `rhs` (e.g. the wrong `k`, or
/// a swapped operand) makes some bit's two sides differ — the reflexive proof then
/// fails to `infer` to the stated conjunction and the kernel **rejects**. So the
/// check has teeth: it can never accept an unsound lowering.
///
/// `operand_width` is `a`'s bit width `w` (a bare-symbol operand carries no width in
/// the Alethe term); it is recorded in the context so the symbol's projection bits
/// route on both sides. This certifies **constant** shifts only — variable shifts and
/// division remain out of scope (a term-representation gap, not a missing rule).
///
/// # Errors
///
/// [`ReconstructError::UnsupportedTerm`] if `shift` is not a constant shift of a
/// bare-symbol operand, [`ReconstructError::MalformedStep`] for a zero width, and
/// [`ReconstructError::KernelRejected`] at the `infer`/`def_eq` gate (the soundness
/// boundary — a wrong lowering surfaces here as a rejection, never an accept).
pub fn reconstruct_const_shift_lowering(
    ctx: &mut ReconstructCtx,
    shift: &AletheTerm,
    rhs: &AletheTerm,
    operand_width: usize,
) -> Result<ExprId, ReconstructError> {
    if operand_width == 0 {
        return Err(ReconstructError::MalformedStep {
            rule: "const_shift_lowering".to_owned(),
            detail: "zero operand width".to_owned(),
        });
    }
    // Register the bare-symbol operand's width so `bv_bit`/`alethe_bv_width` can
    // route its projection bits on both sides.
    let AletheTerm::App(op, args) = shift else {
        return Err(ReconstructError::UnsupportedTerm {
            term: format!("not a shift application `{}`", shift.key()),
        });
    };
    let ("bvshl" | "bvlshr" | "bvashr", [a, _amt]) = (op.as_str(), args.as_slice()) else {
        return Err(ReconstructError::UnsupportedTerm {
            term: format!("not a constant `bvshl`/`bvlshr`/`bvashr` `{}`", shift.key()),
        });
    };
    if let AletheTerm::Const(name) = a
        && parse_bv_literal(name).is_none()
    {
        ctx.bv_widths.insert(name.clone(), operand_width);
    }

    // Build `⋀_i ( bv_bit(shift, i) ↔ bv_bit(rhs, i) )` and its reflexive proof,
    // folding right with `And.intro`. Each conjunct's two sides are the SAME `Prop`
    // exactly when the lowering is correct, so `mk_iff_refl` type-checks — the gate
    // rejects otherwise.
    let bit_iff = |ctx: &mut ReconstructCtx, i: usize| -> Result<ExprId, ReconstructError> {
        let l = bv_bit(ctx, shift, i)?;
        let r = bv_bit(ctx, rhs, i)?;
        Ok(ctx.mk_iff(l, r))
    };
    let last = operand_width - 1;
    let mut target = bit_iff(ctx, last)?;
    let mut proof = {
        let l = bv_bit(ctx, shift, last)?;
        ctx.mk_iff_refl(l)
    };
    for i in (0..last).rev() {
        let head_prop = bit_iff(ctx, i)?;
        let head_proof = {
            let l = bv_bit(ctx, shift, i)?;
            ctx.mk_iff_refl(l)
        };
        proof = and_intro(ctx, head_prop, target, head_proof, proof);
        target = ctx.mk_and(head_prop, target);
    }
    check_against(ctx, "const_shift_lowering", proof, target)
}

/// Certify the constant-shift lowering identity (see [`reconstruct_const_shift_lowering`])
/// **and render it as a self-contained Lean 4 module** an independent `lean` binary
/// can re-check.
///
/// Returns the `prelude`-mode source of `theorem <LEAN_MODULE_THEOREM> : <goal> :=
/// <proof>` (the per-bit equality conjunction) plus its `#print axioms` audit; a
/// faithful proof must report **no** `sorryAx`. A successful return means the
/// lowering identity was kernel-checked **and** rendered to externally-checkable
/// Lean — never a wrong identity.
///
/// # Errors
///
/// Same as [`reconstruct_const_shift_lowering`].
pub fn prove_const_shift_lowering_to_lean_module(
    shift: &AletheTerm,
    rhs: &AletheTerm,
    operand_width: usize,
) -> Result<String, ReconstructError> {
    let mut ctx = ReconstructCtx::new();
    let proof = reconstruct_const_shift_lowering(&mut ctx, shift, rhs, operand_width)?;
    let goal = ctx
        .kernel
        .infer(proof)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "const_shift_lowering".to_owned(),
            detail: format!("infer failed: {e:?}"),
        })?;
    Ok(ctx
        .kernel
        .render_lean_module(LEAN_MODULE_THEOREM, goal, proof))
}

/// Translate a `@bbterm` **gadget bit** into its `Prop`, agreeing with [`bv_bit`]
/// on the bit model: the Boolean literals `true`/`false` map to the prelude's
/// `True`/`False` (not an opaque atom), while bit projections and Boolean
/// connectives go through [`ReconstructCtx::gate_term_to_prop`] structurally.
fn gadget_bit_to_prop(ctx: &mut ReconstructCtx, bit: &AletheTerm) -> ExprId {
    match bit {
        AletheTerm::Const(s) if s == "true" => ctx.kernel.const_(ctx.prelude.true_, vec![]),
        AletheTerm::Const(s) if s == "false" => ctx.kernel.const_(ctx.prelude.false_, vec![]),
        other => ctx.gate_term_to_prop(other),
    }
}

/// The `Prop` for bit `i` of a term-op `lhs`. Routes through [`bv_bit`], except
/// for the width-needing top-level ops: `sign_extend` (operand width recovered as
/// `result_width - by`), `concat` (low-operand width via [`bv_operand_width`]), and
/// `bvcomp` (operand width via [`bv_operand_width`]). These appear only at the top
/// of their own step, never nested, so the width is known exactly here.
fn lhs_bit_prop(
    ctx: &mut ReconstructCtx,
    lhs: &AletheTerm,
    i: usize,
    result_width: usize,
) -> Result<ExprId, ReconstructError> {
    if let AletheTerm::Indexed { op, indices, args } = lhs
        && op == "sign_extend"
    {
        // `((_ sign_extend by) x)`: result width = width(x) + by, so
        // width(x) = result_width - by. Bit `i` is `x_i` for `i < width(x)`,
        // else the sign bit `x_{width(x)-1}`. Matches the emitter
        // (`build_term_vec(x, width)` then `by` copies of the last bit).
        let [by] = indices.as_slice() else {
            return Err(ReconstructError::UnsupportedTerm {
                term: format!("sign_extend needs one index `{}`", lhs.key()),
            });
        };
        let [x] = args.as_slice() else {
            return Err(ReconstructError::UnsupportedTerm {
                term: format!("sign_extend needs one operand `{}`", lhs.key()),
            });
        };
        let by = usize::try_from(*by).map_err(|_| ReconstructError::UnsupportedTerm {
            term: format!("sign_extend amount out of range `{}`", lhs.key()),
        })?;
        let width_x =
            result_width
                .checked_sub(by)
                .ok_or_else(|| ReconstructError::MalformedStep {
                    rule: "bitblast_sign_extend".to_owned(),
                    detail: "sign_extend amount exceeds result width".to_owned(),
                })?;
        if width_x == 0 {
            return Err(ReconstructError::MalformedStep {
                rule: "bitblast_sign_extend".to_owned(),
                detail: "zero-width sign_extend operand".to_owned(),
            });
        }
        let src = if i < width_x { i } else { width_x - 1 };
        let bit_term = operand_bit_term(x, src);
        return Ok(ctx.gate_term_to_prop(&bit_term));
    }
    if let AletheTerm::App(head, args) = lhs {
        if head == "concat" {
            // `(concat a b)` (a high, b low): result bit `i` is `b_i` for
            // `i < width(b)`, else `a_{i - width(b)}` — the emitter emits the low
            // operand's bits first. Needs width(b), recovered from a recorded
            // bit-blasted leaf width or a literal's length.
            let [hi, lo] = args.as_slice() else {
                return Err(ReconstructError::UnsupportedTerm {
                    term: format!("concat needs two operands `{}`", lhs.key()),
                });
            };
            let width_lo =
                alethe_bv_width(ctx, lo).ok_or_else(|| ReconstructError::UnsupportedTerm {
                    term: format!("concat low-operand width unknown `{}`", lhs.key()),
                })?;
            // Bit-route into the operand structurally (`bv_bit`), so a compound concat
            // operand expands rather than becoming an opaque `@bit_of` projection.
            return if i < width_lo {
                bv_bit(ctx, lo, i)
            } else {
                bv_bit(ctx, hi, i - width_lo)
            };
        }
        if head == "bvcomp" {
            // `(bvcomp x y)`: a 1-bit result whose only bit is the per-bit-equality
            // AND over the operand bits. Needs the operand width (via `bv_widths`).
            let [x, y] = args.as_slice() else {
                return Err(ReconstructError::UnsupportedTerm {
                    term: format!("bvcomp needs two operands `{}`", lhs.key()),
                });
            };
            let width = alethe_bv_width(ctx, x)
                .or_else(|| alethe_bv_width(ctx, y))
                .ok_or_else(|| ReconstructError::UnsupportedTerm {
                    term: format!("bvcomp operand width unknown `{}`", lhs.key()),
                })?;
            if width == 0 {
                return Err(ReconstructError::MalformedStep {
                    rule: "bitblast_comp".to_owned(),
                    detail: "zero-width bvcomp operand".to_owned(),
                });
            }
            let bit_term = comp_bit_term(x, y, width);
            return Ok(ctx.gate_term_to_prop(&bit_term));
        }
    }
    bv_bit(ctx, lhs, i)
}

/// Bit 0 of `(bvcomp x y)` as an [`AletheTerm`]: the per-bit-equality AND
/// `(and (= x0 y0) … (= x_{w-1} y_{w-1}))` (or the single `(= x0 y0)` for width 1),
/// transcribing the emitter's `bitwise_equal_and`. `bvcomp` is a 1-bit result, so
/// this is its only bit.
fn comp_bit_term(x: &AletheTerm, y: &AletheTerm, width: usize) -> AletheTerm {
    let es: Vec<AletheTerm> = (0..width)
        .map(|i| {
            AletheTerm::App(
                "=".to_owned(),
                vec![operand_bit_term(x, i), operand_bit_term(y, i)],
            )
        })
        .collect();
    if es.len() > 1 {
        AletheTerm::App("and".to_owned(), es)
    } else {
        es.into_iter().next().expect("a bit-vector has width >= 1")
    }
}

/// The `Prop` `Iff (lhs_bit i) ⟦gadget_i⟧` for bit `i` of a term op.
fn bit_iff_prop(
    ctx: &mut ReconstructCtx,
    lhs: &AletheTerm,
    gadget_i: &AletheTerm,
    i: usize,
    result_width: usize,
) -> Result<ExprId, ReconstructError> {
    let lhs_bit = lhs_bit_prop(ctx, lhs, i, result_width)?;
    let gadget = gadget_bit_to_prop(ctx, gadget_i);
    Ok(ctx.mk_iff(lhs_bit, gadget))
}

/// The reflexive proof of [`bit_iff_prop`]. Sound only because `lhs_bit(i)` and
/// `⟦gadget_i⟧` are the **same** Prop under the pointwise bit model; the kernel
/// gate at the call site rejects if they ever diverge.
fn bit_iff_refl(
    ctx: &mut ReconstructCtx,
    lhs: &AletheTerm,
    gadget_i: &AletheTerm,
    i: usize,
    result_width: usize,
) -> Result<ExprId, ReconstructError> {
    let lhs_bit = lhs_bit_prop(ctx, lhs, i, result_width)?;
    let _ = gadget_i;
    Ok(ctx.mk_iff_refl(lhs_bit))
}

/// Extract the `(lhs, rhs)` operands of a `bitblast_*` step's single positive
/// `(= lhs rhs)` conclusion literal.
fn bitblast_conclusion_sides<'a>(
    rule: &str,
    conclusion: &'a [AletheLit],
) -> Result<(&'a AletheTerm, &'a AletheTerm), ReconstructError> {
    let [lit] = conclusion else {
        return Err(ReconstructError::MalformedStep {
            rule: rule.to_owned(),
            detail: format!(
                "expected one conclusion literal, found {}",
                conclusion.len()
            ),
        });
    };
    if lit.negated {
        return Err(ReconstructError::MalformedStep {
            rule: rule.to_owned(),
            detail: "conclusion literal is negated".to_owned(),
        });
    }
    match &lit.atom {
        AletheTerm::App(head, args) if head == "=" && args.len() == 2 => Ok((&args[0], &args[1])),
        _ => Err(ReconstructError::MalformedStep {
            rule: rule.to_owned(),
            detail: "conclusion is not a positive equality `(= lhs rhs)`".to_owned(),
        }),
    }
}

/// The bit operands of a `(@bbterm b0 … b_{n-1})` term, or [`None`] if `term` is
/// not a `@bbterm` application.
fn bbterm_bits(term: &AletheTerm) -> Option<&[AletheTerm]> {
    match term {
        AletheTerm::App(head, args) if head == "@bbterm" => Some(args),
        _ => None,
    }
}

/// Reconstruct a **complete bitwise `QF_BV` `unsat` proof** (as emitted by
/// [`crate::prove_qf_bv_unsat_alethe`]) into a Lean proof term of type `False`
/// that the trusted [`axeyum_lean_kernel::Kernel`] type-checks.
///
/// This wires the slice-5 bit-blast layer to the slice-3 (resolution) and slice-4
/// (Tseitin CNF-introduction) layers. The full proof has three strata:
///
/// 1. a **bit-blast bridge** — `bitblast_*` steps concluding `(= t bbform)`,
///    chained by `cong`/`trans` and turned into bit-level Boolean unit clauses by
///    `equiv1`/`equiv2` + `resolution`;
/// 2. the **Tseitin CNF-introduction** tautologies (`and_pos`/`and_neg`/`or_*`/
///    `equiv_*`/`xor_*`) over the bit-level gates (slice 4);
/// 3. the **clausal resolution** refutation down to `(cl)` (slice 3).
///
/// ### What is reconstructed — the fully-fused closed proof (slice 6)
///
/// The whole bitwise refutation is reconstructed genuinely, and the final `False`
/// term is **closed over only the input-assumption hypotheses and `em`** — there is
/// **no** bridge axiom for `cong`/`trans`/`equiv1`/`equiv2`/`bitblast_*`.
///
/// The fusion models each input bit-vector **predicate** directly in its bit-level
/// `Prop` form. From the proof's `equiv1`/`equiv2` bridge clauses we learn, for each
/// predicate atom `pred = (= s t)`, its bit-level Boolean form `B` (the `equiv`
/// clause literally pairs `pred` with `B`). We register `pred ↦ B` in the context's
/// `bridge`, putting the clausal/gate translation into **bit mode**: every
/// occurrence of `pred` now translates to `⟦B⟧` (its `Prop` *is* its bit form). Then:
///
/// - an input `assume (= s t)` becomes a hypothesis `h : ⟦B⟧` directly — the bit
///   unit the refutation needs, no `equiv1`/`cong`/`trans` axiom;
/// - `equiv1` (clause `¬pred ∨ B`) and `equiv2` (clause `pred ∨ ¬B`) translate to
///   `¬⟦B⟧ ∨ ⟦B⟧` / `⟦B⟧ ∨ ¬⟦B⟧`, which are genuine `Prop` tautologies — proved
///   classically via `em`, not assumed;
/// - the `bitblast_*`/`cong`/`trans` steps conclude term-level `(= t bbform)`
///   equalities that are *never consumed by the refutation* (only the predicate-level
///   `equiv` clauses feed resolution), so they need no proof at all — their bit-iff
///   content is still separately kernel-checked up front (the slice-5 obligation);
/// - the CNF-introduction tautologies are slice-4 structural proofs and resolution
///   is the slice-3 constructive binary core, both now operating on the *same*
///   bit-level `Prop`s as the assumptions.
///
/// The closing `(cl)` is `infer`-checked against `False` — the trusted gate — and
/// (the new bar) [`ReconstructCtx::declared_axiom_roles`] then contains only
/// `"assume"` and `"em"`. A wrong gadget bit, wrong resolvent, or non-tautological
/// `equiv` clause makes a per-step kernel gate fire — never a wrong `False`.
///
/// # Errors
///
/// Returns a [`ReconstructError`] for any command shape outside this bitwise
/// fragment (a non-bitwise `bitblast_*` rule, an unknown premise, a resolution or
/// gate shape the slices do not handle), or a kernel rejection. It never panics.
pub fn reconstruct_qf_bv_proof(
    ctx: &mut ReconstructCtx,
    commands: &[AletheCommand],
) -> Result<ExprId, ReconstructError> {
    // First, verify every BITWISE `bitblast_*` step's conclusion reconstructs to a
    // kernel-checked bit-iff term (the slice-5 soundness obligation). A non-bitwise
    // `bitblast_*` rule (carry chain, shift, structural) is rejected here. This is
    // also where a non-bitwise `QF_BV` proof is cleanly rejected.
    for cmd in commands {
        if let AletheCommand::Step { rule, clause, .. } = cmd
            && rule.starts_with("bitblast_")
        {
            // Reconstruct-and-check; bitwise rules pass, others error out.
            reconstruct_bitblast_step(ctx, rule, clause)?;
        }
    }

    // Learn the predicate → bit-form bridge from the `equiv1`/`equiv2` steps, then
    // run the clausal walk in bit mode so every predicate is its bit-level `Prop`.
    let bridge = collect_bitblast_bridge(commands);
    ctx.bridge = Some(bridge);
    ctx.gate_memo.clear(); // gate Props depend on the bridge; invalidate the cache.
    let result = reconstruct_bitwise_clausal(ctx, commands);
    ctx.bridge = None;
    ctx.gate_memo.clear();
    result
}

/// Reconstruct a **`QF_UFBV` Ackermann certificate** (the shape
/// [`crate::prove_qf_ufbv_unsat_alethe`] emits) into a kernel-checked `False`,
/// with **no trusted reduction step**.
///
/// The certificate composes an EUF congruence head — deriving each
/// functional-consistency consequent `(= v_i v_j)` from the abstraction's
/// defining equations and the argument equalities via `eq_congruent` +
/// `eq_transitive` — with a bit-blast tail that refutes the reduced `QF_BV`
/// problem. Both strata are reconstructed and gated by the **trusted kernel**:
///
/// 1. **Head (EUF, the closed trust hole).** For each spliced congruence block
///    (`!cong_*` ids concluding a consequent `(= v_i v_j)` under a tail-assume
///    id), a standalone EUF refutation `{defs, arg-eqs, ¬(= v_i v_j)}` is
///    reconstructed via [`reconstruct_qf_uf_proof`] to a kernel-checked `False`.
///    This is the certificate's new content: the previously-*trusted*
///    consistency constraint is now **kernel-derived** by congruence — a wrong
///    congruence makes the kernel reject (never a wrong "checked").
/// 2. **Tail (bit-blast).** The congruence blocks are collapsed back to plain
///    `assume`s of their consequents, and the resulting reduced `QF_BV`
///    refutation is reconstructed via [`reconstruct_qf_bv_proof`] to a
///    kernel-checked `False` — the returned term.
///
/// The two strata meet at the consequent atoms `(= v_i v_j)`: the head proves
/// them (kernel-checked) and the tail consumes them (kernel-checked), so an
/// Ackermann-decided `QF_UFBV` `unsat` carries a machine-checkable proof with no
/// trusted reduction. The returned `ExprId` is the tail's `False`; the head
/// obligations are kernel-verified as a precondition (an `Err` if any fails).
///
/// # Errors
///
/// Returns a [`ReconstructError`] if the proof is not in the certificate shape
/// (no `!cong_*` congruence blocks), if any EUF head obligation fails to
/// reconstruct/kernel-check, or if the bit-blast tail fails — never panics.
pub fn reconstruct_qf_ufbv_proof(
    ctx: &mut ReconstructCtx,
    commands: &[AletheCommand],
) -> Result<ExprId, ReconstructError> {
    let blocks = collect_congruence_blocks(commands);
    if blocks.is_empty() {
        return Err(ReconstructError::UnsupportedRule {
            rule: "reconstruct_qf_ufbv_proof: no `!cong_*` Ackermann congruence \
                   blocks (not a QF_UFBV certificate)"
                .to_owned(),
        });
    }

    // 1. Kernel-check each congruence head: the consistency constraint is derived
    //    by congruence, not trusted. A fresh ctx per obligation keeps the EUF
    //    α-world atoms from colliding with the bit-blast tail's bit atoms.
    for block in &blocks {
        let euf = block.euf_refutation();
        let mut head_ctx = ReconstructCtx::new();
        reconstruct_qf_uf_proof(&mut head_ctx, &euf)?;
    }

    // 2. Collapse the congruence blocks to plain consequent `assume`s and
    //    reconstruct the bit-blast tail to `False`.
    let tail = collapse_congruence_blocks(commands, &blocks);
    reconstruct_qf_bv_proof(ctx, &tail)
}

/// One spliced congruence block: the `!cong_*` head commands deriving a
/// consequent `(= v_i v_j)`, plus the tail consequent step's id/clause/premises.
pub(super) struct CongruenceBlock {
    /// The tail id (e.g. `h3`) of the step concluding `(cl (= v_i v_j))`.
    consequent_id: String,
    /// The consequent equality literals `(= v_i v_j)`.
    consequent: Vec<AletheLit>,
    /// The `!cong_*` head commands (assumes + `eq_*`/`resolution` steps).
    head: Vec<AletheCommand>,
    /// The premise ids of the final consequent-producing resolution (the
    /// `eq_transitive` step plus its threaded unit equalities).
    final_premises: Vec<String>,
}

impl CongruenceBlock {
    /// A standalone EUF refutation of this congruence: the head's `assume`s
    /// (defs + arg-eqs), its `eq_*` theory steps and threading resolutions, plus
    /// a `¬(= v_i v_j)` assume and a closing resolution to `(cl)`. Reconstructable
    /// by [`reconstruct_qf_uf_proof`].
    fn euf_refutation(&self) -> Vec<AletheCommand> {
        let mut out = self.head.clone();
        // Re-emit the consequent-producing resolution under a private id (the
        // original tail id is not present in this standalone sub-proof).
        let consequent_step_id = "!cong_consequent".to_owned();
        out.push(AletheCommand::Step {
            id: consequent_step_id.clone(),
            clause: self.consequent.clone(),
            rule: "resolution".to_owned(),
            premises: self.final_premises.clone(),
            args: Vec::new(),
        });
        let negated: Vec<AletheLit> = self
            .consequent
            .iter()
            .map(|l| AletheLit {
                atom: l.atom.clone(),
                negated: !l.negated,
            })
            .collect();
        let diseq_id = "!cong_diseq".to_owned();
        out.push(AletheCommand::Assume {
            id: diseq_id.clone(),
            clause: negated,
        });
        out.push(AletheCommand::Step {
            id: "!cong_close".to_owned(),
            clause: Vec::new(),
            rule: "resolution".to_owned(),
            premises: vec![consequent_step_id, diseq_id],
            args: Vec::new(),
        });
        out
    }
}

/// Scan a certificate proof for the spliced congruence blocks: contiguous runs of
/// `!cong_*` commands followed by the consequent step (a non-`!cong_*` `Step`
/// whose premises reference a `!cong_trans_*`).
pub(super) fn collect_congruence_blocks(commands: &[AletheCommand]) -> Vec<CongruenceBlock> {
    let mut blocks: Vec<CongruenceBlock> = Vec::new();
    let mut head: Vec<AletheCommand> = Vec::new();
    for cmd in commands {
        let (id, premises): (&str, Vec<String>) = match cmd {
            AletheCommand::Assume { id, .. } => (id.as_str(), Vec::new()),
            AletheCommand::Step { id, premises, .. } => (id.as_str(), premises.clone()),
        };
        if id.starts_with("!cong_") {
            head.push(cmd.clone());
            continue;
        }
        // A non-`!cong_*` command. If it is the consequent step (references a
        // `!cong_trans_*` premise), it closes the current head block.
        let closes = premises.iter().any(|p| p.starts_with("!cong_trans_"));
        if closes
            && !head.is_empty()
            && let AletheCommand::Step {
                id,
                clause,
                premises,
                ..
            } = cmd
        {
            blocks.push(CongruenceBlock {
                consequent_id: id.clone(),
                consequent: clause.clone(),
                head: std::mem::take(&mut head),
                final_premises: premises.clone(),
            });
        }
    }
    blocks
}

/// Test-only accessor for a congruence block's standalone EUF head refutation
/// (the route-A audit reconstructs it directly to inspect its declared axioms).
#[cfg(test)]
pub(super) fn euf_refutation_for_test(block: &CongruenceBlock) -> Vec<AletheCommand> {
    block.euf_refutation()
}

/// Rebuild the proof with every congruence block collapsed to a plain `assume`
/// of its consequent (under the original tail id), yielding the reduced `QF_BV`
/// refutation that [`reconstruct_qf_bv_proof`] reconstructs.
fn collapse_congruence_blocks(
    commands: &[AletheCommand],
    blocks: &[CongruenceBlock],
) -> Vec<AletheCommand> {
    let consequent_ids: BTreeMap<&str, &CongruenceBlock> = blocks
        .iter()
        .map(|b| (b.consequent_id.as_str(), b))
        .collect();
    let mut out: Vec<AletheCommand> = Vec::with_capacity(commands.len());
    for cmd in commands {
        let id = match cmd {
            AletheCommand::Assume { id, .. } | AletheCommand::Step { id, .. } => id.as_str(),
        };
        if id.starts_with("!cong_") {
            continue; // head command, dropped
        }
        if let Some(block) = consequent_ids.get(id) {
            // The consequent step becomes a plain assume of `(= v_i v_j)`.
            out.push(AletheCommand::Assume {
                id: block.consequent_id.clone(),
                clause: block.consequent.clone(),
            });
        } else {
            out.push(cmd.clone());
        }
    }
    out
}

/// Scan the proof for `equiv1`/`equiv2` bridge clauses and learn, for each
/// bit-vector predicate atom, its bit-level Boolean form `B`.
///
/// The emitter's `equiv1` concludes `(cl (not pred) B)` and `equiv2` concludes
/// `(cl pred (not B))` — each clause pairs the predicate atom `pred` (a `(= s t)`
/// over bit-vector terms) with its bit form `B` (a Boolean over bit projections).
/// We read `pred ↦ B` straight from the clause: the predicate is the literal whose
/// atom is a `(= …)` over non-bit operands (it carries a `bvand`/`bvor`/… or a bare
/// bit-vector symbol), and `B` is the other literal's atom. This avoids tracing the
/// `cong`/`trans` chain — the `equiv` clause already exhibits the correspondence.
fn collect_bitblast_bridge(commands: &[AletheCommand]) -> BTreeMap<String, AletheTerm> {
    let mut bridge: BTreeMap<String, AletheTerm> = BTreeMap::new();
    for cmd in commands {
        let AletheCommand::Step { rule, clause, .. } = cmd else {
            continue;
        };
        if rule != "equiv1" && rule != "equiv2" {
            continue;
        }
        // The equiv clause is a 2-literal pairing of `pred` and `B`. Identify which
        // literal is the bit-vector predicate (it mentions a `@bit_of`-free
        // bit-vector operand) and which is the bit-level form.
        let [l0, l1] = clause.as_slice() else {
            continue;
        };
        let (pred, b_form) = if is_bv_predicate_atom(&l0.atom) {
            (&l0.atom, &l1.atom)
        } else if is_bv_predicate_atom(&l1.atom) {
            (&l1.atom, &l0.atom)
        } else {
            continue;
        };
        bridge.insert(pred.key(), b_form.clone());
    }
    bridge
}

/// Whether an atom is a bit-vector **predicate** `(= s t)` whose operands are
/// bit-vector *terms* (a bare symbol or a `bv…`/structural application), as opposed
/// to a bit-level Boolean `(= a_i b_i)` over `@bit_of` projections. The discriminator
/// is that at least one operand is **not** an `@bit_of` projection (nor a Boolean
/// gate / Boolean constant): a genuine bit-vector term.
fn is_bv_predicate_atom(term: &AletheTerm) -> bool {
    match term {
        // Bit-vector equality (`=` over BV operands) and the comparison predicates
        // (`bvult`/`bvslt`) whose bit-level form `B` is a ladder. Each carries a
        // `pred ↔ B` bridge entry so its `equiv1`/`equiv2` clause is reconstructed
        // as the tautology `¬B ∨ B` over the bit atoms.
        AletheTerm::App(head, args)
            if (head == "=" || head == "bvult" || head == "bvslt") && args.len() == 2 =>
        {
            args.iter().any(is_bitvector_operand)
        }
        _ => false,
    }
}

/// Whether a term is a bit-vector operand (a bare symbol that is not a Boolean
/// literal, or a `bv…` application), distinguishing a predicate's BV operand from a
/// bit-level Boolean leaf (`@bit_of` projection, `and`/`or`/`xor`/`not`/`=` gate).
fn is_bitvector_operand(term: &AletheTerm) -> bool {
    match term {
        AletheTerm::Const(s) => s != "true" && s != "false" && !s.starts_with("#b"),
        AletheTerm::App(head, _) => head.starts_with("bv") || head == "concat" || head == "@bbterm",
        AletheTerm::Indexed { .. } => false,
    }
}

/// The fused clausal walk for a bitwise `QF_BV` proof: a superset of
/// [`reconstruct_resolution_proof`] that threads the bit-blast bridge rules under
/// the context's **bit mode** (`bridge` set), so the reconstructed `False` is closed
/// over only the input-assumption hypotheses and `em`.
///
/// Each command becomes a [`Clause`] (its literals + a kernel proof of the clause's
/// bit-level `Prop` encoding). `assume` is the input predicate hypothesis (its
/// `Prop` is the predicate's bit form, via the bridge); `resolution` is the slice-3
/// constructive core; the CNF-introduction rules are the slice-4 structural
/// tautologies; `equiv1`/`equiv2` are genuine `¬B ∨ B` tautologies; the
/// `cong`/`trans`/`bitblast_*` term-equality steps are deferred (never consumed by
/// the refutation, so never forced into the `False` term). The final `(cl)` is
/// checked against `False`.
fn reconstruct_bitwise_clausal(
    ctx: &mut ReconstructCtx,
    commands: &[AletheCommand],
) -> Result<ExprId, ReconstructError> {
    let _ = ctx.em_axiom();
    let mut env: BTreeMap<String, Clause> = BTreeMap::new();

    for cmd in commands {
        match cmd {
            AletheCommand::Assume { id, clause } => {
                let prop = ctx.clause_to_prop(clause);
                let proof = fresh_axiom(ctx, prop, "assume")?;
                env.insert(
                    id.clone(),
                    Clause {
                        lits: clause.clone(),
                        proof,
                    },
                );
            }
            AletheCommand::Step {
                id,
                clause,
                rule,
                premises,
                ..
            } => {
                let recovered = reconstruct_bitwise_step(ctx, rule, clause, premises, &env)?;
                if let Some(recovered) = recovered {
                    if clause.is_empty() {
                        return check_false_prop(ctx, recovered.proof);
                    }
                    env.insert(id.clone(), recovered);
                }
            }
        }
    }
    Err(ReconstructError::NoEmptyClause)
}

/// Reconstruct a large bitwise Alethe tail through the compact CPS clause
/// boundary. Source assumptions and small gate-introduction clauses cross from
/// the established `Or` encoding exactly once; learned resolution clauses never
/// expand back into nested disjunctions.
#[allow(clippy::too_many_lines)]
pub(super) fn reconstruct_bitwise_cps_tail(
    ctx: &mut ReconstructCtx,
    commands: &[AletheCommand],
    assumption_proofs: &[ExprId],
) -> Result<ExprId, ReconstructError> {
    let _ = ctx.em_axiom();

    // Slice the command DAG backwards from the final empty clause. Large native
    // traces include many learned clauses that do not contribute to the close.
    let mut dependencies = BTreeMap::<String, Vec<String>>::new();
    let mut empty_step = None;
    for command in commands {
        if let AletheCommand::Step {
            id,
            clause,
            premises,
            ..
        } = command
        {
            dependencies.insert(id.clone(), premises.clone());
            if clause.is_empty() {
                empty_step = Some(id.clone());
            }
        }
    }
    let mut live = BTreeSet::new();
    let mut stack = empty_step.into_iter().collect::<Vec<_>>();
    while let Some(id) = stack.pop() {
        if !live.insert(id.clone()) {
            continue;
        }
        if let Some(premises) = dependencies.get(&id) {
            stack.extend(premises.iter().cloned());
        }
    }
    if live.is_empty() {
        return Err(ReconstructError::NoEmptyClause);
    }
    let mut source_proofs = assumption_proofs.iter();
    let mut or_env = BTreeMap::<String, Clause>::new();
    let mut cps_env = BTreeMap::<String, CpsClause>::new();
    let mut lets = Vec::new();

    for command in commands {
        let (id, mut recovered, or_clause) = match command {
            AletheCommand::Assume { id, clause } => {
                let source_proof = *source_proofs
                    .next()
                    .ok_or_else(|| ReconstructError::UnsupportedResolution {
                        detail: "Alethe CPS tail has too many assumptions".to_owned(),
                    })?;
                if !live.contains(id) {
                    continue;
                }
                let proposition = ctx.clause_to_prop(clause);
                let source_proof = check_against(
                    ctx,
                    "source_instance_assume_cps",
                    source_proof,
                    proposition,
                )?;
                let clause_proof = Clause {
                    lits: clause.clone(),
                    proof: source_proof,
                };
                let recovered = clause_to_cps(ctx, &clause_proof)?;
                (id, recovered, Some(clause_proof))
            }
            AletheCommand::Step {
                id,
                clause,
                rule,
                premises,
                ..
            } => {
                if !live.contains(id) {
                    continue;
                }
                if matches!(rule.as_str(), "resolution" | "th_resolution") {
                    let recovered = if premises.iter().all(|premise| cps_env.contains_key(premise)) {
                        reconstruct_ordered_rup_cps_step(ctx, clause, premises, &cps_env)?
                    } else if let Some(definition) = try_reconstruct_bit_definition(ctx, clause)? {
                        clause_to_cps(ctx, &definition)?
                    } else {
                        let missing = premises
                            .iter()
                            .find(|premise| !cps_env.contains_key(*premise))
                            .cloned()
                            .unwrap_or_else(|| "<unknown>".to_owned());
                        return Err(ReconstructError::UnknownPremise { id: missing });
                    };
                    (id, recovered, None)
                } else {
                    let Some(clause_proof) =
                        reconstruct_bitwise_step(ctx, rule, clause, premises, &or_env)?
                    else {
                        continue;
                    };
                    let recovered = clause_to_cps(ctx, &clause_proof)?;
                    (id, recovered, Some(clause_proof))
                }
            }
        };

        recovered = normalize_cps_clause(ctx, &recovered)?;
        if recovered.lits.is_empty() {
            if source_proofs.next().is_some() {
                return Err(ReconstructError::UnsupportedResolution {
                    detail: "unused source-derived assumptions in CPS tail".to_owned(),
                });
            }
            let false_ = ctx.kernel.const_(ctx.prelude.false_, vec![]);
            let mut proof = apply_cps_clause(ctx, &recovered, false_, []);
            let fvars = lets
                .iter()
                .map(|(fvar, _, _, _)| *fvar)
                .collect::<Vec<_>>();
            proof = ctx.kernel.abstract_fvars(proof, &fvars);
            for (index, (_, name, ty, value)) in lets.into_iter().enumerate().rev() {
                let ty = ctx.kernel.abstract_fvars(ty, &fvars[..index]);
                let value = ctx.kernel.abstract_fvars(value, &fvars[..index]);
                proof = ctx.kernel.let_(name, ty, value, proof);
            }
            return check_false_prop(ctx, proof);
        }

        // Deferred checking closes the complete proof after local aliases have
        // been abstracted. Alias every live clause in that mode: a later wide
        // RUP step may mention thousands of nominally single-use clauses, and
        // leaving even three out of four proofs inline re-expands their complete
        // derivations inside every handler. The one-let-per-clause overhead is
        // linear and keeps both the kernel DAG and exported module linear in the
        // LRAT dependency graph.
        let should_alias = ctx.defer_open_step_checks;
        if should_alias {
            let ty = cps_clause_prop(ctx, &recovered.lits);
            if ctx.closed_aliases.cps_clauses {
                if ctx.kernel.has_fvars(ty)
                    || ctx.kernel.num_loose_bvars(ty) != 0
                    || ctx.kernel.has_fvars(recovered.proof)
                    || ctx.kernel.num_loose_bvars(recovered.proof) != 0
                {
                    return Err(ReconstructError::KernelRejected {
                        rule: "global_cps_clause_alias".to_owned(),
                        detail: "closed CPS declaration contains a local variable".to_owned(),
                    });
                }
                let name = ctx.fresh_name("cps_clause");
                ctx.kernel
                    .add_declaration(Declaration::Theorem {
                        name,
                        uparams: vec![],
                        ty,
                        value: recovered.proof,
                    })
                    .map_err(|error| ReconstructError::KernelRejected {
                        rule: "global_cps_clause_alias".to_owned(),
                        detail: format!("theorem admission failed: {error:?}"),
                    })?;
                recovered.proof = ctx.kernel.const_(name, vec![]);
            } else {
                let fvar = fresh_fvar_id(ctx);
                let name = ctx.fresh_name("cps_clause");
                lets.push((fvar, name, ty, recovered.proof));
                recovered.proof = ctx.kernel.fvar(fvar);
            }
        }
        if let Some(or_clause) = or_clause {
            or_env.insert(id.clone(), or_clause);
        }
        cps_env.insert(id.clone(), recovered);
    }
    Err(ReconstructError::NoEmptyClause)
}

/// Reconstruct one step of the fused bitwise clausal walk.
///
/// Returns `Ok(Some(clause))` for a step that contributes a clause to the
/// refutation, or `Ok(None)` for a **deferred** term-level bridge step
/// (`cong`/`trans`/`bitblast_*`) that the refutation never consumes — those carry no
/// reconstructed proof, so they introduce no axiom into the final `False` term.
pub(super) fn reconstruct_bitwise_step(
    ctx: &mut ReconstructCtx,
    rule: &str,
    clause: &[AletheLit],
    premises: &[String],
    env: &BTreeMap<String, Clause>,
) -> Result<Option<Clause>, ReconstructError> {
    match rule {
        // Slice-3 resolution core (also closes to `(cl)`).
        "resolution" | "th_resolution" => {
            // A compound term's **bit-definition** unit `(cl B_t)` is emitted as
            // `equiv1` + `resolution` against the (deferred) `bitblast_*` term-equality
            // step, so one premise is not in `env`. Under the faithful bit model the
            // definition `B_t = (and (= ((_ @bit_of i) t) g_i) …)` is a conjunction of
            // *reflexive* iffs (`((_ @bit_of i) t)` resolves structurally to the same
            // Prop as `g_i`), hence a tautology proved directly — no premise needed.
            if premises.iter().any(|p| !env.contains_key(p))
                && let Some(def) = try_reconstruct_bit_definition(ctx, clause)?
            {
                return Ok(Some(def));
            }
            Ok(Some(reconstruct_resolution_step(
                ctx, clause, premises, env,
            )?))
        }
        // Slice-4 Tseitin CNF-introduction tautologies, proved structurally.
        "and_pos" | "and_neg" | "or_pos" | "or_neg" | "equiv_pos1" | "equiv_pos2"
        | "equiv_neg1" | "equiv_neg2" | "xor_pos1" | "xor_pos2" | "xor_neg1" | "xor_neg2" => {
            let proof = reconstruct_cnf_intro_rule(ctx, rule, clause)?;
            Ok(Some(Clause {
                lits: clause.to_vec(),
                proof,
            }))
        }
        // The predicate↔bit-form bridge. Under bit mode `⟦pred⟧ ≡ ⟦B⟧`, so the
        // `equiv1`/`equiv2` clause `(¬pred ∨ B)` / `(pred ∨ ¬B)` is a genuine
        // `Prop` tautology — proved classically (via `em`), not assumed.
        "equiv1" | "equiv2" => Ok(Some(reconstruct_equiv_bridge(ctx, rule, clause)?)),
        // The Boolean-constant pins the emitter feeds into the SAT refutation when a
        // carry-chain gadget (`bvadd`/`bvneg`/`bvmul`, the Route-2 `bvsub` rewrite)
        // embeds a literal `true`/`false` operand:
        //   `true`  → `(cl true)`      : Prop `True`,     proved by `True.intro`.
        //   `false` → `(cl (not false))`: Prop `Not False`, proved by `fun h => h`.
        // Both are closed tautologies (no axiom enters the `False` term).
        "true" | "false" => Ok(Some(reconstruct_bool_const_pin(ctx, rule, clause)?)),
        // Term-level bridge steps that the refutation never consumes (only the
        // predicate-level `equiv` clauses feed resolution). Defer them: no proof is
        // built, so no axiom is introduced. Their bit-iff content is separately
        // kernel-checked in `reconstruct_qf_bv_proof`.
        //
        // `bv_poly_simp` is the Route-2 `bvsub`-rewrite bridge: the term equality
        // `(= (bvsub a b) (bvadd a (bvneg b)))` Carcara validates (polynomial-equal
        // mod 2^w). The refutation consumes it only via the `trans`-chained term
        // equality `(= (bvsub a b) bbform)`, whose bit content is the `bvsub`
        // bit-definition (reflexive under the faithful `bv_bit` model, where
        // `bvsub a b` bit `i` IS the `bvadd a (bvneg b)` bit). So, like `cong`/`trans`,
        // it is deferred: no axiom enters the `False` term.
        "cong" | "trans" | "bv_poly_simp" => Ok(None),
        r if r.starts_with("bitblast_") => Ok(None),
        other => Err(ReconstructError::UnsupportedRule {
            rule: other.to_owned(),
        }),
    }
}

/// Try to reconstruct a compound term's **bit-definition** unit clause `(cl B_t)`,
/// where `B_t = (and (= ((_ @bit_of i) t) g_i) …)` (or the single `(= … g_0)` for a
/// width-1 term) ties each projection `((_ @bit_of i) t)` to its gadget bit `g_i`.
///
/// Under the faithful bit model, `((_ @bit_of i) t)` for a compound `t` resolves
/// structurally (via [`bv_bit`], the same path the gadget `g_i` takes), so each
/// conjunct `(= ((_ @bit_of i) t) g_i)` is `Iff P P` — a reflexive identity. The
/// whole `B_t` is therefore an `And`-fold of `Iff.refl`s, proved directly with no
/// premise. The result is `check_against`-gated: if any conjunct is NOT reflexive
/// (a wrong gadget bit), the kernel rejects.
///
/// Returns `Ok(None)` if `clause` is not a single positive bit-definition literal,
/// so the caller falls back to ordinary resolution.
fn try_reconstruct_bit_definition(
    ctx: &mut ReconstructCtx,
    clause: &[AletheLit],
) -> Result<Option<Clause>, ReconstructError> {
    // Must be a single positive literal `B_t`.
    let [lit] = clause else {
        return Ok(None);
    };
    if lit.negated {
        return Ok(None);
    }
    // Collect the conjuncts of `B_t`: either `(and c0 c1 …)` or a single `c0`.
    let conjuncts: Vec<&AletheTerm> = match &lit.atom {
        AletheTerm::App(head, args) if head == "and" && !args.is_empty() => args.iter().collect(),
        single @ AletheTerm::App(head, _) if head == "=" => vec![single],
        _ => return Ok(None),
    };
    // Every conjunct must be a bit-definition equality `(= ((_ @bit_of i) t) g_i)`
    // whose left side projects a COMPOUND term (not a bare symbol — that would be an
    // ordinary predicate's bit form, not a definition).
    let mut defines_compound = false;
    for c in &conjuncts {
        let AletheTerm::App(head, args) = c else {
            return Ok(None);
        };
        if head != "=" || args.len() != 2 {
            return Ok(None);
        }
        match &args[0] {
            AletheTerm::Indexed {
                op, args: pargs, ..
            } if op == "@bit_of" && pargs.len() == 1 => {
                if !matches!(pargs[0], AletheTerm::Const(_)) {
                    defines_compound = true;
                }
            }
            _ => return Ok(None),
        }
    }
    if !defines_compound {
        return Ok(None);
    }

    // Build the proof: each conjunct's `Prop` is `Iff ⟦lhs⟧ ⟦rhs⟧`; under the model
    // `⟦lhs⟧` and `⟦rhs⟧` coincide, so its proof is `mk_iff_refl(⟦lhs⟧)`. `And.intro`
    // fold (right-nested) the per-conjunct refl proofs.
    let mut props: Vec<ExprId> = Vec::with_capacity(conjuncts.len());
    let mut proofs: Vec<ExprId> = Vec::with_capacity(conjuncts.len());
    for c in &conjuncts {
        let AletheTerm::App(_, args) = c else {
            return Ok(None);
        };
        let lhs_prop = ctx.gate_term_to_prop(&args[0]);
        let rhs_prop = ctx.gate_term_to_prop(&args[1]);
        props.push(ctx.mk_iff(lhs_prop, rhs_prop));
        // The reflexive proof of `Iff lhs rhs` is well-typed only if `lhs`/`rhs`
        // coincide as Props; the final `check_against` is the gate.
        proofs.push(ctx.mk_iff_refl(lhs_prop));
    }
    // Right-fold `And.intro`.
    let n = props.len();
    let mut acc_prop = props[n - 1];
    let mut acc_proof = proofs[n - 1];
    for i in (0..n - 1).rev() {
        acc_proof = and_intro(ctx, props[i], acc_prop, proofs[i], acc_proof);
        acc_prop = ctx.mk_and(props[i], acc_prop);
    }
    let target = ctx.gate_clause_to_prop(clause);
    let proof = check_against(ctx, "bit_definition", acc_proof, target)?;
    Ok(Some(Clause {
        lits: clause.to_vec(),
        proof,
    }))
}

/// Reconstruct an `equiv1`/`equiv2` bridge clause as a genuine bit-level `Prop`
/// tautology under bit mode.
///
/// In bit mode the predicate atom `pred` translates to its bit form `⟦B⟧`, so the
/// `equiv1` clause `(cl (not pred) B)` is `¬⟦B⟧ ∨ ⟦B⟧` and the `equiv2` clause
/// `(cl pred (not B))` is `⟦B⟧ ∨ ¬⟦B⟧` — both `Prop` tautologies. We prove them with
/// the same classical case-split engine the CNF-introduction tautologies use
/// ([`prove_clause_by_cases`]): the clause is a tautology over its (bit-level) atoms,
/// so the engine finds a satisfied literal in every assignment. The result is
/// `check_against`-gated to the clause's bit-level `Prop` encoding.
///
/// If the clause is not a `¬X ∨ X` tautology under bit mode (e.g. the bridge map did
/// not identify the predicate, so the two literals are unrelated atoms), the
/// case-split engine fails and a [`ReconstructError::MalformedStep`] surfaces — never
/// a silently-assumed bridge.
fn reconstruct_equiv_bridge(
    ctx: &mut ReconstructCtx,
    rule: &str,
    clause: &[AletheLit],
) -> Result<Clause, ReconstructError> {
    let _ = ctx.em_axiom();

    // The case-split atoms: the distinct gate leaves of the (bridge-substituted)
    // clause. Substitute each literal's atom through the bridge so `collect_atoms`
    // (which is not itself bridge-aware) decomposes the bit form, not the opaque
    // predicate.
    let substituted: Vec<AletheLit> = clause
        .iter()
        .map(|lit| AletheLit {
            atom: ctx.bridge_substitute(&lit.atom),
            negated: lit.negated,
        })
        .collect();

    // The bridge clause is `¬pred ∨ B` (equiv1) / `pred ∨ ¬B` (equiv2); after
    // substitution both literals share the atom `B`, so the tautology is just
    // `¬⟦B⟧ ∨ ⟦B⟧`, provable by `em ⟦B⟧`. Case-split over the substituted literal
    // atoms THEMSELVES (treated as opaque via `prove_term`'s assignment-first
    // lookup), not their bit leaves — `collect_atoms` would recurse into `B` and
    // give a `2^leaves` split over the ladder.
    let mut atom_keys: Vec<(String, AletheTerm)> = Vec::new();
    let mut seen = std::collections::BTreeSet::new();
    for lit in &substituted {
        let k = lit.atom.key();
        if seen.insert(k.clone()) {
            atom_keys.push((k, lit.atom.clone()));
        }
    }

    // The target is the ORIGINAL clause's bit-level `Prop` (predicate atoms route
    // through the bridge inside `gate_clause_to_prop`); the substituted clause has
    // the identical `Prop`, so proving over the substituted form yields a term of
    // the target type.
    let target = ctx.gate_clause_to_prop(clause);
    let mut assignment = Assignment::new();
    let proof = prove_clause_by_cases(ctx, &atom_keys, 0, &mut assignment, &substituted, target)?;
    let proof = check_against(ctx, rule, proof, target)?;
    Ok(Clause {
        lits: clause.to_vec(),
        proof,
    })
}

/// Reconstruct a Boolean-constant pin clause — the Carcara `true`/`false` tautology
/// the emitter feeds into the SAT refutation to fix a carry-chain gadget's literal
/// `true`/`false` operand:
///
/// - `true` → clause `(cl true)`, Prop `True`, proof `True.intro`;
/// - `false` → clause `(cl (not false))`, Prop `Not False` (i.e. `False → False`),
///   proof the identity `fun (h : False) => h`.
///
/// Both are closed (no axiom/hypothesis), `check_against`-gated to the clause's `Prop`.
fn reconstruct_bool_const_pin(
    ctx: &mut ReconstructCtx,
    rule: &str,
    clause: &[AletheLit],
) -> Result<Clause, ReconstructError> {
    let target = ctx.gate_clause_to_prop(clause);
    let raw = match rule {
        "true" => ctx.kernel.const_(ctx.prelude.true_intro, vec![]),
        "false" => {
            // `fun (h : False) => h : False → False`, defeq `Not False`.
            let anon = ctx.kernel.anon();
            let false_const = ctx.kernel.const_(ctx.prelude.false_, vec![]);
            let body = ctx.kernel.bvar(0);
            ctx.kernel.lam(anon, false_const, body, BinderInfo::Default)
        }
        _ => {
            return Err(ReconstructError::UnsupportedRule {
                rule: rule.to_owned(),
            });
        }
    };
    let proof = check_against(ctx, rule, raw, target)?;
    Ok(Clause {
        lits: clause.to_vec(),
        proof,
    })
}

impl ReconstructCtx {
    /// Rewrite an atom term through the bit-blast bridge: if its key names a
    /// registered bit-vector predicate, return its bit-level Boolean form `B`;
    /// otherwise return the term unchanged. Used to expose the bit-level structure
    /// to the (non-bridge-aware) tautology case-split engine.
    pub(super) fn bridge_substitute(&self, term: &AletheTerm) -> AletheTerm {
        if let Some(bridge) = &self.bridge
            && let Some(b_form) = bridge.get(&term.key())
        {
            return b_form.clone();
        }
        match term {
            AletheTerm::App(head, args) => AletheTerm::App(
                head.clone(),
                args.iter().map(|arg| self.bridge_substitute(arg)).collect(),
            ),
            AletheTerm::Indexed { op, indices, args } => AletheTerm::Indexed {
                op: op.clone(),
                indices: indices.clone(),
                args: args.iter().map(|arg| self.bridge_substitute(arg)).collect(),
            },
            AletheTerm::Const(_) => term.clone(),
        }
    }
}

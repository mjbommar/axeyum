//! Kernel-checked universal instantiation and existential elimination.

use std::collections::{BTreeMap, BTreeSet};

use axeyum_cnf::{AletheCommand, AletheLit, AletheTerm};
use axeyum_lean_kernel::{BinderInfo, ExprId, ExprNode, NameId};

use super::{
    ClauseProof, ReconstructCtx, ReconstructError, ResolutionResult, as_positive_eq, check_against,
    check_false, fresh_axiom, reconstruct_assume, reconstruct_resolution,
};

// ===========================================================================
// Quantifier instantiation (the first quantified-`unsat` slice) — reconstruct
// a `forall_inst`-driven refutation to a kernel-checked `False`.
//
// ## Kernel modeling of ∀
//
// A universal `∀(x : α). P(x)` over the EUF carrier `α` is the **dependent
// product** `Pi (x : α), ⟦P x⟧`, where `⟦P x⟧ : Prop` is the body's translation
// with the bound variable rendered as the de-Bruijn `bvar(0)` (this slice's
// bodies are quantifier-free, so `x` is always at index 0). The universal
// hypothesis is declared as an axiom `h_forall : Pi (x : α), ⟦P x⟧`.
//
// **Instantiation is application** (`forall_elim`): for a witness `t`,
// `h_forall ⟦t⟧ : ⟦P x⟧[bvar 0 := ⟦t⟧]`, and the kernel's `infer` β/Pi-reduces
// that to `⟦P t⟧` — exactly the ground instance equality. The reconstructed
// instance is therefore an ordinary [`ClauseProof::EqUnit`] whose proof term is
// the application, and the **ground tail** (the EUF resolution to the empty
// clause) is the existing [`reconstruct_qf_uf_proof`] machinery threaded with
// these instance units.
//
// ## Soundness
//
// Every instance application is `infer`/`def_eq`-checked against the translated
// instance equality before it enters the ground walk, and the final `False` goes
// through [`check_false`] — so a wrong witness, a wrong Pi body, or a mis-shaped
// `forall_inst` makes the kernel reject it (a `ReconstructError`), never a wrong
// `False`. The only addition to the trusted base is one axiom per quantified
// assertion — the honest encoding of the input universal.
// ===========================================================================

impl ReconstructCtx {
    /// Translate an Alethe term into a Lean [`ExprId`] in the EUF model, with each
    /// quantified variable in `var_names` rendered as a de-Bruijn `bvar`. The list
    /// is outermost-first, matching the binder chain `Pi (x₀:α), … Pi (xₙ:α), …`;
    /// variable `var_names[i]` therefore sits at de-Bruijn index
    /// `var_names.len() - 1 - i` (the **innermost** binder is index 0). For a single
    /// universal (`var_names = [x]`) this is `bvar(0)`, as before.
    ///
    /// # Errors
    ///
    /// As [`Self::alethe_term_to_expr`]: [`ReconstructError::UnsupportedTerm`] for
    /// an out-of-scope shape.
    fn alethe_term_to_expr_bound(
        &mut self,
        term: &AletheTerm,
        var_names: &[&str],
    ) -> Result<ExprId, ReconstructError> {
        match term {
            AletheTerm::Const(symbol) => {
                if let Some(i) = var_names.iter().position(|v| v == symbol) {
                    // de-Bruijn index: innermost binder (last in `var_names`) is 0.
                    let index = u32::try_from(var_names.len() - 1 - i)
                        .map_err(|_| ReconstructError::UnsupportedTerm { term: term.key() })?;
                    Ok(self.kernel.bvar(index))
                } else {
                    let name = self.atom_const(symbol);
                    Ok(self.kernel.const_(name, vec![]))
                }
            }
            AletheTerm::App(head, args) if head == "=" => {
                let [l, r] = args.as_slice() else {
                    return Err(ReconstructError::UnsupportedTerm { term: term.key() });
                };
                let l = self.alethe_term_to_expr_bound(l, var_names)?;
                let r = self.alethe_term_to_expr_bound(r, var_names)?;
                Ok(self.mk_eq(l, r))
            }
            AletheTerm::App(head, args) if !args.is_empty() => {
                let f_name = self.func_const(head, args.len());
                let mut e = self.kernel.const_(f_name, vec![]);
                for arg in args {
                    let a = self.alethe_term_to_expr_bound(arg, var_names)?;
                    e = self.kernel.app(e, a);
                }
                Ok(e)
            }
            AletheTerm::App(..) | AletheTerm::Indexed { .. } => {
                Err(ReconstructError::UnsupportedTerm { term: term.key() })
            }
        }
    }
}

/// What a parsed (possibly nested) Alethe `(forall (x) … body)` atom carries: the
/// ordered bound-variable names (outermost first) and the quantifier-free inner
/// body, ready for translation.
struct ForallAtom<'a> {
    var_names: Vec<&'a str>,
    body: &'a AletheTerm,
}

/// Parse a (possibly nested) `(forall (x) (forall (y) … body))` Alethe atom — the
/// opaque universal the quantifier emitter `assume`s. Each level is encoded as
/// `App("forall", [Const(x), inner])`; this peels the chain, collecting the bound
/// variables outermost-first and returning the innermost quantifier-free body.
/// `None` if `atom` is not a `forall` chain.
fn as_forall_atom(atom: &AletheTerm) -> Option<ForallAtom<'_>> {
    let mut var_names = Vec::new();
    let mut cur = atom;
    while let AletheTerm::App(head, args) = cur {
        if head != "forall" || args.len() != 2 {
            break;
        }
        let AletheTerm::Const(var_name) = &args[0] else {
            return None;
        };
        var_names.push(var_name.as_str());
        cur = &args[1];
    }
    if var_names.is_empty() {
        return None;
    }
    Some(ForallAtom {
        var_names,
        body: cur,
    })
}

/// Infer the witness **tuple** `[t₀, …]` (one per bound variable in `var_names`,
/// in that order) by matching the instance `inst` against `body[xᵢ := ?]`: the
/// first occurrence of each `Const(xᵢ)` fixes `tᵢ`, later occurrences must agree,
/// and all other structure must match verbatim. Returns the witnesses, or `None`
/// if `inst` is not a consistent instance of `body` (so a malformed `forall_inst`
/// is rejected rather than mis-reconstructed), or if any bound variable does not
/// occur in `body` (no witness to apply) — out of this slice.
fn infer_witness<'a>(
    var_names: &[&str],
    body: &AletheTerm,
    inst: &'a AletheTerm,
) -> Option<Vec<&'a AletheTerm>> {
    fn go<'a>(
        var_names: &[&str],
        body: &AletheTerm,
        inst: &'a AletheTerm,
        witnesses: &mut BTreeMap<String, &'a AletheTerm>,
    ) -> bool {
        match body {
            AletheTerm::Const(c) if var_names.iter().any(|v| v == c) => {
                if let Some(w) = witnesses.get(c) {
                    *w == inst
                } else {
                    witnesses.insert(c.clone(), inst);
                    true
                }
            }
            AletheTerm::Const(_) => body == inst,
            AletheTerm::App(bh, ba) => {
                let AletheTerm::App(ih, ia) = inst else {
                    return false;
                };
                bh == ih
                    && ba.len() == ia.len()
                    && ba
                        .iter()
                        .zip(ia)
                        .all(|(b, i)| go(var_names, b, i, witnesses))
            }
            AletheTerm::Indexed {
                op: bo,
                indices: bi,
                args: ba,
            } => {
                let AletheTerm::Indexed {
                    op: io,
                    indices: ii,
                    args: ia,
                } = inst
                else {
                    return false;
                };
                bo == io
                    && bi == ii
                    && ba.len() == ia.len()
                    && ba
                        .iter()
                        .zip(ia)
                        .all(|(b, i)| go(var_names, b, i, witnesses))
            }
        }
    }
    let mut witnesses: BTreeMap<String, &'a AletheTerm> = BTreeMap::new();
    if !go(var_names, body, inst, &mut witnesses) {
        return None;
    }
    // Every bound variable must have been bound (occur in the body).
    var_names
        .iter()
        .map(|v| witnesses.get(*v).copied())
        .collect()
}

/// A `forall_inst` clause `(cl (not (forall (x) … body)) inst)` recorded for lazy
/// reconstruction: it is turned into a ground-instance unit when a `resolution`
/// resolves it against the universal axiom.
#[derive(Clone)]
struct ForallInstClause {
    /// The bound variable names of the universal it instantiates (outermost first).
    var_names: Vec<String>,
    /// The universal inner body (with the bound variables free, as `Const(x)`).
    body: AletheTerm,
    /// The instance literal `inst = body[xᵢ := tᵢ]` (positive).
    inst: AletheTerm,
}

/// The reconstruction environment for the quantifier walk: a per-id map to either
/// a ground [`ClauseProof`] (reusing the EUF machinery), a universal axiom, or a
/// pending `forall_inst` clause.
enum QuantProof {
    /// A ground clause proof (unit equality/disequality or EUF theory clause),
    /// reconstructed exactly as the EUF walk does.
    Ground(ClauseProof),
    /// A universal `assume`: the dependent-product axiom
    /// `h : Pi (x:α), … Pi (xₙ:α), ⟦body⟧`, with its binder names and body kept for
    /// witness translation.
    ForallAxiom {
        /// The bound variable names (outermost first).
        var_names: Vec<String>,
        /// The universal inner body (Alethe, the bound variables free).
        body: AletheTerm,
        /// The axiom proof term `h_forall : Pi (x:α), … ⟦body⟧`.
        proof: ExprId,
    },
    /// A pending `forall_inst` theory clause, reconstructed on resolution.
    Inst(ForallInstClause),
}

/// Reconstruct a **complete** quantifier-instantiation `unsat` Alethe proof (the
/// shape [`crate::prove_quant_unsat_alethe`] emits) into a Lean proof term of type
/// `False` that the trusted [`axeyum_lean_kernel::Kernel`] type-checks.
///
/// The proof's quantifier layer is an `assume` of the universal over an opaque
/// `(forall (x) body)` atom, one `forall_inst` step per witness, and a
/// `resolution` of each `forall_inst` against the universal to the ground instance
/// unit; the ground tail is the EUF refutation of those instances plus the side
/// assertions (the `prove_qf_uf_unsat_alethe` shape, here with ids prefixed `g_`).
///
/// ## How each command maps
///
/// - **`assume (cl (forall (x) body))`** ⇒ an axiom `h : Pi (x:α), ⟦body⟧` (the
///   universal as a dependent product; `forall_elim` is its application).
/// - **`assume (cl …)`** (an equality / disequality side fact) ⇒ the EUF
///   `reconstruct_assume` unit hypothesis.
/// - **`forall_inst (cl (not (forall (x) body)) inst)`** ⇒ recorded pending.
/// - **`resolution [forall-axiom, forall_inst]`** ⇒ `h ⟦t⟧ : ⟦inst⟧` (the witness
///   `t` inferred from `inst = body[x:=t]`), an `infer`-checked ground unit.
/// - **`eq_*`/`resolution`/`th_resolution`/empty clause** ⇒ the EUF
///   `reconstruct_resolution` machinery, closing to `False`.
///
/// # Errors
///
/// Returns a [`ReconstructError`] for any out-of-scope command shape, an unknown
/// premise id, a malformed `forall_inst`/resolution, a missing empty-clause
/// derivation, or a kernel rejection. It never panics on malformed input.
pub fn reconstruct_quant_unsat_proof(
    ctx: &mut ReconstructCtx,
    commands: &[AletheCommand],
) -> Result<ExprId, ReconstructError> {
    let mut env: BTreeMap<String, QuantProof> = BTreeMap::new();

    for cmd in commands {
        match cmd {
            AletheCommand::Assume { id, clause } => {
                // A universal `(cl (forall (x) body))`, or an ordinary EUF unit.
                if let [l] = clause.as_slice()
                    && !l.negated
                    && let Some(fa) = as_forall_atom(&l.atom)
                {
                    let var_names: Vec<String> =
                        fa.var_names.iter().map(|&s| s.to_owned()).collect();
                    let body = fa.body.clone();
                    let proof = declare_forall_axiom(ctx, &fa.var_names, &body)?;
                    env.insert(
                        id.clone(),
                        QuantProof::ForallAxiom {
                            var_names,
                            body,
                            proof,
                        },
                    );
                    continue;
                }
                let cp = reconstruct_assume(ctx, clause)?;
                env.insert(id.clone(), QuantProof::Ground(cp));
            }
            AletheCommand::Step {
                id,
                clause,
                rule,
                premises,
                ..
            } => match rule.as_str() {
                "forall_inst" => {
                    let inst_clause = parse_forall_inst(clause)?;
                    env.insert(id.clone(), QuantProof::Inst(inst_clause));
                }
                "eq_reflexive" | "eq_symmetric" | "eq_transitive" | "eq_congruent" => {
                    env.insert(
                        id.clone(),
                        QuantProof::Ground(ClauseProof::TheoryClause {
                            rule: rule.clone(),
                            clause: clause.clone(),
                        }),
                    );
                }
                "resolution" | "th_resolution" => {
                    // A quantifier resolution (forall-axiom against a forall_inst)
                    // yields the ground instance unit; otherwise it is a ground EUF
                    // resolution / the closing empty clause.
                    if let Some(unit) = try_instance_resolution(ctx, premises, &env)? {
                        env.insert(id.clone(), QuantProof::Ground(unit));
                        continue;
                    }
                    let ground_env = ground_view(&env);
                    match reconstruct_resolution(ctx, clause, premises, &ground_env)? {
                        ResolutionResult::Clause(cp) => {
                            env.insert(id.clone(), QuantProof::Ground(cp));
                        }
                        ResolutionResult::FalseProof(proof) => {
                            return check_false(ctx, proof);
                        }
                    }
                }
                other => {
                    return Err(ReconstructError::UnsupportedRule {
                        rule: other.to_owned(),
                    });
                }
            },
        }
    }

    Err(ReconstructError::NoEmptyClause)
}

/// Declare the universal axiom `h : Pi (x : α), … Pi (xₙ : α), ⟦body⟧` (one binder
/// per name in `var_names`, outermost first) and return its `Const`.
pub(super) fn declare_forall_axiom(
    ctx: &mut ReconstructCtx,
    var_names: &[&str],
    body: &AletheTerm,
) -> Result<ExprId, ReconstructError> {
    let mut ty = ctx.alethe_term_to_expr_bound(body, var_names)?;
    let anon = ctx.kernel.anon();
    // Wrap one `Pi (· : α)` per bound variable. Each wrap adds an outer binder, so
    // the count is what matters; `alethe_term_to_expr_bound` already placed each
    // variable at its de-Bruijn index for this nesting depth.
    for _ in var_names {
        ty = ctx.kernel.pi(anon, ctx.alpha, ty, BinderInfo::Default);
    }
    fresh_axiom(ctx, ty, "forall")
}

/// Parse a `forall_inst` step's clause `(cl (not (forall (x) … body)) inst)`.
fn parse_forall_inst(clause: &[AletheLit]) -> Result<ForallInstClause, ReconstructError> {
    let [neg, pos] = clause else {
        return Err(ReconstructError::MalformedStep {
            rule: "forall_inst".to_owned(),
            detail: "expected exactly two literals `(not (forall …)) inst`".to_owned(),
        });
    };
    if !neg.negated || pos.negated {
        return Err(ReconstructError::MalformedStep {
            rule: "forall_inst".to_owned(),
            detail: "literal polarities are not `(not (forall …))` then positive `inst`".to_owned(),
        });
    }
    let Some(fa) = as_forall_atom(&neg.atom) else {
        return Err(ReconstructError::MalformedStep {
            rule: "forall_inst".to_owned(),
            detail: "first literal is not a `(forall (x) … body)` atom".to_owned(),
        });
    };
    Ok(ForallInstClause {
        var_names: fa.var_names.iter().map(|&s| s.to_owned()).collect(),
        body: fa.body.clone(),
        inst: pos.atom.clone(),
    })
}

/// If `premises` are exactly a universal axiom and a pending `forall_inst` over the
/// same universal, reconstruct the instance unit `(h ⟦t₀⟧ …) : ⟦inst⟧`
/// (`forall_elim`, one application per bound variable). Returns `Ok(Some(unit))` on
/// a quantifier resolution, `Ok(None)` when it is not one (so the caller falls back
/// to the EUF resolution path).
fn try_instance_resolution(
    ctx: &mut ReconstructCtx,
    premises: &[String],
    env: &BTreeMap<String, QuantProof>,
) -> Result<Option<ClauseProof>, ReconstructError> {
    // Find an axiom premise and an inst premise (order-independent).
    let mut axiom: Option<(&[String], &AletheTerm, ExprId)> = None;
    let mut inst: Option<&ForallInstClause> = None;
    for p in premises {
        match env.get(p) {
            Some(QuantProof::ForallAxiom {
                var_names,
                body,
                proof,
            }) => axiom = Some((var_names, body, *proof)),
            Some(QuantProof::Inst(ic)) => inst = Some(ic),
            _ => {}
        }
    }
    let (Some((ax_vars, ax_body, ax_proof)), Some(ic)) = (axiom, inst) else {
        return Ok(None);
    };
    // The inst clause must instantiate this very universal.
    if ic.var_names != ax_vars || &ic.body != ax_body {
        return Err(ReconstructError::UnsupportedResolution {
            detail: "forall_inst resolves against a different universal".to_owned(),
        });
    }
    // Infer the witness tuple from `inst = body[xᵢ := tᵢ]`, translate each, and
    // apply the axiom to them in binder order (outermost first).
    let ax_var_refs: Vec<&str> = ax_vars.iter().map(String::as_str).collect();
    let witnesses = infer_witness(&ax_var_refs, ax_body, &ic.inst).ok_or_else(|| {
        ReconstructError::MalformedStep {
            rule: "forall_inst".to_owned(),
            detail: "instance is not a consistent substitution of the universal body".to_owned(),
        }
    })?;
    // forall_elim chain: (((h ⟦t₀⟧) ⟦t₁⟧) …) : ⟦body⟧[xᵢ := ⟦tᵢ⟧]  (≡ ⟦inst⟧).
    let mut app = ax_proof;
    for witness in witnesses {
        let t_expr = ctx.alethe_term_to_expr(witness)?;
        app = ctx.kernel.app(app, t_expr);
    }
    // Validate against the translated instance and package as the matching unit.
    if let Some((l, r)) = as_positive_eq(&AletheLit {
        atom: ic.inst.clone(),
        negated: false,
    }) {
        let le = ctx.alethe_term_to_expr(l)?;
        let re = ctx.alethe_term_to_expr(r)?;
        let expected = ctx.mk_eq(le, re);
        let proof = check_against(ctx, "forall_inst", app, expected)?;
        Ok(Some(ClauseProof::EqUnit {
            l: l.clone(),
            r: r.clone(),
            proof,
        }))
    } else {
        Err(ReconstructError::UnsupportedResolution {
            detail: "forall_inst instance is not an equality (outside this EUF slice)".to_owned(),
        })
    }
}

/// A read-only [`ClauseProof`] view of the quantifier environment for the EUF
/// resolution machinery: ground entries pass through; an axiom / pending inst is
/// not a ground clause and is omitted (a resolution citing one as a ground premise
/// is a real shape error the EUF path will surface).
fn ground_view(env: &BTreeMap<String, QuantProof>) -> BTreeMap<String, ClauseProof> {
    let mut out = BTreeMap::new();
    for (id, qp) in env {
        if let QuantProof::Ground(cp) = qp {
            out.insert(id.clone(), cp.clone());
        }
    }
    out
}

// ===========================================================================
// Existential skolemization (P3.7) — CERTIFY the trusted skolemization step.
//
// ## The certificate and what it certifies
//
// [`crate::solve`] replaces a top-level `∃x. P(x)` with `P(sk)` for a fresh
// constant `sk` and refutes the skolemized query — a *trusted* step. The
// emitter [`crate::prove_skolem_unsat_alethe`] produces a [`crate::SkolemCert`]: an
// Alethe proof of the **skolemized** refutation (where each `sk_k` is an
// ordinary uninterpreted constant and each `P(sk_k)` is an `assume`d EUF unit)
// plus, per existential, the bound-variable name, the single-equality body `P`
// (bound variable free), and the skolem name `sk_k`.
//
// ## Kernel modeling of ∃ and the `Exists.elim` wrapping
//
// `∃(x : α). P(x)` is the prelude inductive `Exists.{1} α p` with
// `p := fun (x : α) => ⟦P x⟧ : α → Prop`. The existential hypothesis is the
// honest axiom `h_∃ : Exists α p` (mirroring how a universal becomes a `Pi`
// axiom).
//
// The skolemized refutation `R : False` is reconstructed by the existing
// quantifier walk; it mentions `Const(sk_k)` (the skolem atom) and
// `Const(hyp_k)` (the `P(sk_k)` assumption axiom). `R` is **parametric** in
// these: it refutes `P(sk_k) ∧ Rest` for the *arbitrary* constant `sk_k`. So,
// replacing each `Const(sk_k) ↦ w_k` and `Const(hyp_k) ↦ hw_k` turns `R` into
// the minor premise `fun (w_k : α) (hw_k : p_k w_k) => R'` and
//
//     Exists.rec.{1} α p_k (fun _ => False) (fun w_k hw_k => R') h_∃_k : False
//
// is the `Exists.elim`. Several existentials nest (innermost-out). The skolem
// atom and assumption are turned into fresh **fvars** first, then the standard
// `abstract_fvars` + `lam` machinery handles binder depth.
//
// ## Soundness
//
// The minor's body is the same kernel-checked refutation `R`; the
// `Exists.rec` applications and the final term are `infer`/`def_eq False`-gated
// through [`check_false`]. The only additions to the trusted base are the per-`∃`
// axiom `h_∃_k` (the honest encoding of the input existential) and whatever the
// inner refutation already adds (the universal axioms / side `assume`s). A wrong
// body `p_k`, a mis-identified skolem/assumption, or a wrong nesting makes the
// kernel reject the `Exists.rec` application — never a wrong `False`.
// ===========================================================================

impl ReconstructCtx {
    /// The constant [`NameId`] previously declared (lazily) for the EUF atom
    /// `name`, if any. Used by the skolem reconstruction to locate a skolem
    /// constant after the inner refutation has been reconstructed.
    fn atom_name_id(&self, name: &str) -> Option<NameId> {
        self.atoms.get(name).copied()
    }

    /// Replace every `Const(target, _)` in `e` with the expression `repl`,
    /// **correctly shifting** `repl` under intervening binders. Here `repl` is
    /// always a loose `BVar` (the `Exists.elim`-bound variable), so passing
    /// through a binder lifts it by one. A pure structural rewrite over the public
    /// expression constructors — no reduction.
    fn replace_const(&mut self, e: ExprId, target: NameId, repl: ExprId) -> ExprId {
        self.replace_const_aux(e, target, repl, 0)
    }

    fn replace_const_aux(&mut self, e: ExprId, target: NameId, repl: ExprId, depth: u32) -> ExprId {
        match self.kernel.expr_node(e).clone() {
            ExprNode::Const(n, _) if n == target => {
                // Lift the (loose-bvar) replacement to the current binder depth.
                self.kernel.lift_loose_bvars(repl, 0, depth)
            }
            ExprNode::BVar(_)
            | ExprNode::FVar(_)
            | ExprNode::Sort(_)
            | ExprNode::Const(..)
            | ExprNode::Lit(_) => e,
            ExprNode::App(f, a) => {
                let f = self.replace_const_aux(f, target, repl, depth);
                let a = self.replace_const_aux(a, target, repl, depth);
                self.kernel.app(f, a)
            }
            ExprNode::Lam(name, ty, body, info) => {
                let ty = self.replace_const_aux(ty, target, repl, depth);
                let body = self.replace_const_aux(body, target, repl, depth + 1);
                self.kernel.lam(name, ty, body, info)
            }
            ExprNode::Pi(name, ty, body, info) => {
                let ty = self.replace_const_aux(ty, target, repl, depth);
                let body = self.replace_const_aux(body, target, repl, depth + 1);
                self.kernel.pi(name, ty, body, info)
            }
            ExprNode::Let(name, ty, val, body) => {
                let ty = self.replace_const_aux(ty, target, repl, depth);
                let val = self.replace_const_aux(val, target, repl, depth);
                let body = self.replace_const_aux(body, target, repl, depth + 1);
                self.kernel.let_(name, ty, val, body)
            }
            ExprNode::Proj(type_name, field_index, structure) => {
                let structure = self.replace_const_aux(structure, target, repl, depth);
                self.kernel.proj(type_name, field_index, structure)
            }
        }
    }

    /// Build the existential predicate `p := fun (x : α) => ⟦body x⟧ : α → Prop`
    /// and the proposition `Exists.{1} α p`, from a single-equality `body` whose
    /// bound variable is `bound_var`.
    fn mk_exists(
        &mut self,
        bound_var: &str,
        body: &AletheTerm,
    ) -> Result<(ExprId, ExprId), ReconstructError> {
        // ⟦body⟧ with the bound variable at de-Bruijn 0 (a one-binder context).
        let body_expr = self.alethe_term_to_expr_bound(body, &[bound_var])?;
        let anon = self.kernel.anon();
        // p := fun (x : α) => ⟦body⟧.
        let p = self
            .kernel
            .lam(anon, self.alpha, body_expr, BinderInfo::Default);
        // Exists.{1} α p.
        let exists_const = self.kernel.const_(self.prelude.exists_, vec![self.one]);
        let e = self.kernel.app(exists_const, self.alpha);
        let exists_ap = self.kernel.app(e, p);
        Ok((p, exists_ap))
    }

    /// `Exists.rec.{1} α p (fun _ => False) minor major : False` — the
    /// `Exists.elim` at a constant `False` motive.
    fn mk_exists_elim_false(
        &mut self,
        p: ExprId,
        exists_ap: ExprId,
        minor: ExprId,
        major: ExprId,
    ) -> ExprId {
        let anon = self.kernel.anon();
        let false_ = self.kernel.const_(self.prelude.false_, vec![]);
        // motive := fun (_ : Exists α p) => False.
        let motive = self
            .kernel
            .lam(anon, exists_ap, false_, BinderInfo::Default);
        let rec = self
            .kernel
            .const_(self.prelude.exists_rec, vec![self.one]);
        let e = self.kernel.app(rec, self.alpha);
        let e = self.kernel.app(e, p);
        let e = self.kernel.app(e, motive);
        let e = self.kernel.app(e, minor);
        self.kernel.app(e, major)
    }
}

/// One skolemized existential prepared for the `Exists.elim` wrapping: the
/// predicate `p_k`, the proposition `Exists α p_k`, the existential hypothesis
/// axiom `h_∃_k`, and the skolem-constant / `P(sk_k)`-assumption `NameId`s.
///
/// The `NameId`s are `Option`: when the skolemized refutation does **not** use
/// the witness (the inner refutation closes from the side facts alone — possible
/// only when the existential was *vacuous* to the contradiction), the skolem
/// atom and/or its assumption are never interned/declared by the inner walk, and
/// the corresponding `Exists.elim` minor binder is simply unused. The resulting
/// `False` is still sound over the original `∃` assertion.
struct PreparedExists {
    p: ExprId,
    exists_ap: ExprId,
    h_exists: ExprId,
    skolem: Option<NameId>,
    assumption: Option<NameId>,
}

/// Reconstruct a **top-level existential skolemization** refutation
/// ([`crate::prove_skolem_unsat_alethe`]'s [`crate::SkolemCert`]) into a Lean proof term
/// of type `False` that the trusted [`axeyum_lean_kernel::Kernel`] type-checks — certifying the
/// otherwise-trusted skolemization step over the **original** `∃` assertions.
///
/// The embedded Alethe (the skolemized refutation) is reconstructed by the
/// existing quantifier walk to `R : False`; each existential `∃x. (= l r)`
/// becomes `Exists.{1} α p_k` (with `p_k := fun x => ⟦(= l r) x⟧`) and an honest
/// axiom `h_∃_k : Exists α p_k`. `R` is parametric in each skolem constant
/// `sk_k` and its `P(sk_k)` assumption, so it is wrapped (innermost existential
/// out) as
/// `Exists.rec α p_k (fun _ => False) (fun w hw => R[sk_k:=w, P(sk_k):=hw]) h_∃_k`.
///
/// # Errors
///
/// Returns a [`ReconstructError`] if the embedded refutation does not
/// reconstruct, if a skolem constant or its `P(sk)` assumption cannot be located
/// in the reconstructed term's environment, or if the assembled `Exists.elim`
/// term is rejected by the kernel. Never panics on malformed input.
pub fn reconstruct_skolem_unsat_proof(
    ctx: &mut ReconstructCtx,
    cert: &crate::SkolemCert,
) -> Result<ExprId, ReconstructError> {
    if cert.skolems.is_empty() {
        return Err(ReconstructError::MalformedStep {
            rule: "skolemize".to_owned(),
            detail: "certificate has no existential to certify".to_owned(),
        });
    }

    // Pre-declare each existential's predicate / proposition / honest hypothesis
    // axiom, and the **expected** `P(sk_k)` assumption proposition (used to locate
    // the assumption axiom the inner walk will declare). We declare these before
    // the inner walk so the skolem atoms are interned consistently; the inner walk
    // declares the `P(sk_k)` assumption itself.
    let mut expected_assumption: Vec<ExprId> = Vec::with_capacity(cert.skolems.len());
    let mut exists_data: Vec<(ExprId, ExprId, ExprId, String)> =
        Vec::with_capacity(cert.skolems.len());
    for rec in &cert.skolems {
        let (p, exists_ap) = ctx.mk_exists(&rec.bound_var, &rec.body)?;
        let h_exists = fresh_axiom(ctx, exists_ap, "exists")?;
        // The skolemized assumption `P(sk_k) = body[x := sk_k]`, as a closed
        // proposition `Eq α ⟦l[x:=sk]⟧ ⟦r[x:=sk]⟧`.
        let assume_prop = skolemized_assumption_prop(ctx, rec)?;
        expected_assumption.push(assume_prop);
        exists_data.push((p, exists_ap, h_exists, rec.skolem_name.clone()));
    }

    // Snapshot the "assume" axioms before the inner walk so we can identify the
    // ones the walk declares for the `P(sk_k)` units.
    let before: BTreeSet<NameId> = ctx
        .axiom_roles
        .iter()
        .filter(|(_, role)| role.as_str() == "assume")
        .map(|(&n, _)| n)
        .collect();

    // Reconstruct the skolemized refutation `R : False`.
    let refutation = reconstruct_quant_unsat_proof(ctx, &cert.commands)?;

    // Identify, per existential, the skolem-constant `NameId` (interned by the
    // walk's atom translation) and the `P(sk_k)` assumption axiom (a freshly-added
    // "assume" axiom whose type is def-eq to the expected `P(sk_k)` proposition).
    let mut prepared: Vec<PreparedExists> = Vec::with_capacity(cert.skolems.len());
    for (idx, (p, exists_ap, h_exists, skolem_name)) in exists_data.into_iter().enumerate() {
        // The skolem atom / `P(sk_k)` assumption are present iff the inner
        // refutation actually used the witness. An absent one (a vacuous
        // existential) leaves the corresponding `Exists.elim` binder unused.
        let skolem = ctx.atom_name_id(&skolem_name);
        let assumption = find_assumption_axiom(ctx, &before, expected_assumption[idx]);
        prepared.push(PreparedExists {
            p,
            exists_ap,
            h_exists,
            skolem,
            assumption,
        });
    }

    // Wrap `R` in nested `Exists.elim`s, innermost existential first. For each, a
    // fresh `w` fvar (the witness) replaces `Const(skolem)` and a fresh `hw` fvar
    // (the `p w` proof) replaces `Const(assumption)`; then `abstract_fvars` turns
    // them into the minor's two binders (unused binders are fine — a vacuous
    // existential simply does not mention `w`/`hw`).
    let mut acc = refutation;
    for pe in prepared.into_iter().rev() {
        let w_fvar = ctx.fresh_local_fvar();
        let hw_fvar = ctx.fresh_local_fvar();
        let w = ctx.kernel.fvar(w_fvar);
        let hw = ctx.kernel.fvar(hw_fvar);
        // R[skolem := w, assumption := hw] (each substitution a no-op when the
        // corresponding constant is absent).
        if let Some(skolem) = pe.skolem {
            acc = ctx.replace_const(acc, skolem, w);
        }
        if let Some(assumption) = pe.assumption {
            acc = ctx.replace_const(acc, assumption, hw);
        }
        // minor := fun (w : α) (hw : p w) => acc.
        //   `hw`'s domain `p w` is under the `w` binder ⇒ `w` is BVar 0 there.
        let w_bvar0 = ctx.kernel.bvar(0);
        let p_w_dom = ctx.kernel.app(pe.p, w_bvar0);
        // Abstract the two fvars: innermost-first ⇒ [w_fvar, hw_fvar] makes
        // `hw_fvar → BVar 0`, `w_fvar → BVar 1` in the body.
        let body = ctx.kernel.abstract_fvars(acc, &[w_fvar, hw_fvar]);
        let anon = ctx.kernel.anon();
        let inner = ctx.kernel.lam(anon, p_w_dom, body, BinderInfo::Default);
        let minor = ctx.kernel.lam(anon, ctx.alpha, inner, BinderInfo::Default);
        // Exists.rec α p (fun _ => False) minor h_∃ : False.
        acc = ctx.mk_exists_elim_false(pe.p, pe.exists_ap, minor, pe.h_exists);
    }

    check_false(ctx, acc)
}

/// The closed proposition `Eq α ⟦l[x:=sk]⟧ ⟦r[x:=sk]⟧` for a single-equality
/// existential body `(= l r)` with bound variable `x` and skolem constant `sk` —
/// the type of the `P(sk)` assumption the inner walk declares.
fn skolemized_assumption_prop(
    ctx: &mut ReconstructCtx,
    rec: &crate::SkolemRecord,
) -> Result<ExprId, ReconstructError> {
    let AletheTerm::App(head, args) = &rec.body else {
        return Err(ReconstructError::MalformedStep {
            rule: "skolemize".to_owned(),
            detail: "existential body is not an application".to_owned(),
        });
    };
    if head != "=" || args.len() != 2 {
        return Err(ReconstructError::MalformedStep {
            rule: "skolemize".to_owned(),
            detail: "existential body is not a single equality `(= l r)`".to_owned(),
        });
    }
    // Translate each operand with `bound_var ↦ Const(skolem_name)`.
    let l = subst_bound_to_skolem(ctx, &args[0], &rec.bound_var, &rec.skolem_name)?;
    let r = subst_bound_to_skolem(ctx, &args[1], &rec.bound_var, &rec.skolem_name)?;
    Ok(ctx.mk_eq(l, r))
}

/// Translate an Alethe term to a Lean `ExprId`, rendering each `Const(bound_var)`
/// as the skolem constant `Const(skolem_name)` (an EUF atom). Otherwise identical
/// to [`ReconstructCtx::alethe_term_to_expr`].
fn subst_bound_to_skolem(
    ctx: &mut ReconstructCtx,
    term: &AletheTerm,
    bound_var: &str,
    skolem_name: &str,
) -> Result<ExprId, ReconstructError> {
    match term {
        AletheTerm::Const(s) if s == bound_var => {
            let name = ctx.atom_const(skolem_name);
            Ok(ctx.kernel.const_(name, vec![]))
        }
        AletheTerm::Const(s) => {
            let name = ctx.atom_const(s);
            Ok(ctx.kernel.const_(name, vec![]))
        }
        AletheTerm::App(head, args) if head == "=" => {
            let [l, r] = args.as_slice() else {
                return Err(ReconstructError::UnsupportedTerm { term: term.key() });
            };
            let l = subst_bound_to_skolem(ctx, l, bound_var, skolem_name)?;
            let r = subst_bound_to_skolem(ctx, r, bound_var, skolem_name)?;
            Ok(ctx.mk_eq(l, r))
        }
        AletheTerm::App(head, args) if !args.is_empty() => {
            let f_name = ctx.func_const(head, args.len());
            let mut e = ctx.kernel.const_(f_name, vec![]);
            for arg in args {
                let a = subst_bound_to_skolem(ctx, arg, bound_var, skolem_name)?;
                e = ctx.kernel.app(e, a);
            }
            Ok(e)
        }
        AletheTerm::App(..) | AletheTerm::Indexed { .. } => {
            Err(ReconstructError::UnsupportedTerm { term: term.key() })
        }
    }
}

/// Find the "assume" axiom — declared by the inner refutation walk (i.e. *not*
/// already in `before`) — whose declared type is [`axeyum_lean_kernel::Kernel::def_eq`] to `expected`
/// (the `P(sk)` proposition). The skolem constants are fresh, so each `P(sk_k)`
/// type is unique among the assumptions, giving an unambiguous match.
fn find_assumption_axiom(
    ctx: &mut ReconstructCtx,
    before: &BTreeSet<NameId>,
    expected: ExprId,
) -> Option<NameId> {
    // Collect candidates deterministically (BTreeMap iteration order is by id).
    let candidates: Vec<NameId> = ctx
        .axiom_roles
        .iter()
        .filter(|(n, role)| role.as_str() == "assume" && !before.contains(*n))
        .map(|(&n, _)| n)
        .collect();
    for n in candidates {
        let ty = ctx.kernel.environment().get(n)?.ty();
        if ctx.kernel.def_eq(ty, expected) {
            return Some(n);
        }
    }
    None
}

impl ReconstructCtx {
    /// Mint a fresh free-variable id for transient `Exists.elim` binders, from the
    /// context's deterministic counter (kept well above any kernel-internal fvar
    /// by a large offset, since reconstruction otherwise builds closed terms).
    fn fresh_local_fvar(&mut self) -> u64 {
        let id = self.next_id;
        self.next_id += 1;
        // Offset into a private high range so these never alias a kernel fvar.
        id.wrapping_add(1 << 48)
    }
}

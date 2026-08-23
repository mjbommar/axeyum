//! Untrusted, bounded general producer for the `Int.ModEq`/`Nat.ModEq`-shaped
//! **definitional-equivalence family**: `ModEq n a b` unfolds transparently
//! (delta) to `a % n = b % n`, so every lemma this schema targets is a plain
//! `Eq`/`Iff` combinator once that one unfolding step is taken. This module
//! never names `Int`, `Nat`, `ModEq`, `%`, or any target/sibling declaration:
//! it peels every leading `Pi` binder into a fresh free variable (an ordinary
//! hypothesis, exactly like a domain binder — there is no dependent/induction
//! distinction to make here, unlike `bounded_induction_support`), and at the
//! terminal, non-`Pi` goal it `whnf`s to see through whatever the goal's own
//! head symbol transparently unfolds to, then closes an `Eq`-headed goal by
//! reflexivity, symmetry, or transitivity over the retained hypotheses, and
//! an `Iff`-headed goal by `Iff.intro` composed from two nested closures (one
//! per direction, each with the other side's hypothesis freshly introduced).
//!
//! `Eq.symm`/`Eq.trans` are **not** borrowed from the environment (the
//! isolated statement-import kernel keeps only whatever the target
//! definition's own type transitively needs to elaborate, which for a bare
//! `Prop`-valued `def` is never a proof-combinator theorem) — they are
//! reconstructed here directly from `Eq.rec`, the same technique
//! `axeyum-lean-import::trusted_substitution` uses internally for its own
//! `Eq.symm`/`congrArg`/`congr` bridges (independently re-derived in this
//! module, not imported, since that module's helpers are private and this
//! producer must stand on its own). `Iff.intro` is simply `Iff`'s own
//! (structurally discovered, never assumed) two-field constructor.
//!
//! Circularity is impossible by construction, not merely checked after the
//! fact: every `Const` node this module ever builds names `Eq`, `Eq.refl`,
//! `Eq.rec`, `Iff`, or `Iff`'s constructor — nothing else — and every other
//! leaf in a built proof is a bound variable or a free variable this same
//! module minted while peeling binders. There is no code path through which a
//! target theorem's own name, or any sibling `ModEq` fact's name, could ever
//! appear in a candidate this module returns. The operation binary still
//! confirms this mechanically (never by doc comment) over
//! `Kernel::declaration_dependency_closure`, and
//! `crates/axeyum-lean-import/tests/modeq_family_operation.rs` carries the
//! adversarial fixture proving that check actually rejects a candidate that
//! *does* cite its own target.

use axeyum_lean_kernel::{BinderInfo, Declaration, ExprId, ExprNode, Kernel, LevelId, NameId};

/// Maximum number of leading `Pi` binders this producer will peel — shared
/// across ordinary domain binders and hypothesis (`P -> ...`) binders, since
/// this schema draws no distinction between them. Four is enough for every
/// `int-modeq-*`/`nat-modeq-*` goal (`trans`'s five binders — `n a b c` plus
/// two hypothesis arrows — is the deepest), with slack for the nested
/// `Iff.intro` nested closures re-entering the same peeling loop.
pub const MAX_BINDERS: usize = 8;

/// One fully constructed candidate.
#[derive(Debug)]
pub struct Candidate {
    pub proof: ExprId,
    pub binders_used: usize,
}

/// Why the bounded search declined, tagged by stage.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeclineReason {
    BinderBudgetExceeded,
    RequiredDeclarationUnavailable(String),
    UnsupportedRecursorShape(String),
    UnsupportedIffShape(String),
    TerminalNotClosed,
}

impl std::fmt::Display for DeclineReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::BinderBudgetExceeded => {
                write!(f, "binder budget exceeded: maximum {MAX_BINDERS}")
            }
            Self::RequiredDeclarationUnavailable(name) => {
                write!(
                    f,
                    "required declaration {name:?} occurs a number of times other than one"
                )
            }
            Self::UnsupportedRecursorShape(detail) => {
                write!(f, "unsupported recursor shape: {detail}")
            }
            Self::UnsupportedIffShape(detail) => write!(f, "unsupported Iff shape: {detail}"),
            Self::TerminalNotClosed => write!(
                f,
                "terminal goal is not an Eq/Iff shape this schema's refl/symm/trans/Iff.intro combinators can close"
            ),
        }
    }
}

fn exact_name(kernel: &Kernel, rendered: &str) -> Result<NameId, DeclineReason> {
    let matches: Vec<_> = kernel
        .environment()
        .iter()
        .filter_map(|(name, _)| {
            (kernel.display_name(*name).to_string() == rendered).then_some(*name)
        })
        .collect();
    match matches.as_slice() {
        [name] => Ok(*name),
        _ => Err(DeclineReason::RequiredDeclarationUnavailable(
            rendered.to_owned(),
        )),
    }
}

fn app_spine(kernel: &Kernel, mut expression: ExprId) -> (ExprId, Vec<ExprId>) {
    let mut arguments = Vec::new();
    while let ExprNode::App(function, argument) = kernel.expr_node(expression) {
        arguments.push(*argument);
        expression = *function;
    }
    arguments.reverse();
    (expression, arguments)
}

/// `fun (name : ty) => body[fv]`, closing `fv` via `Kernel::abstract_fvars`.
fn lam_fv(
    kernel: &mut Kernel,
    name: NameId,
    fv: u64,
    ty: ExprId,
    body: ExprId,
    info: BinderInfo,
) -> ExprId {
    let abstracted = kernel.abstract_fvars(body, &[fv]);
    kernel.lam(name, ty, abstracted, info)
}

/// The ambient `Eq`/`Eq.refl`/`Eq.rec` primitives, discovered by exact
/// display name and checked rather than assumed — same discipline as
/// `bounded_induction_support::discover_eq_primitives` and
/// `trusted_substitution::discover_eq`, independently re-derived here since
/// both of those are private to their own modules.
struct EqPrimitives {
    eq: NameId,
    eq_refl: NameId,
    eq_rec: NameId,
}

fn discover_eq(kernel: &Kernel) -> Result<EqPrimitives, DeclineReason> {
    let eq = exact_name(kernel, "Eq")?;
    let eq_refl = exact_name(kernel, "Eq.refl")?;
    let eq_rec = exact_name(kernel, "Eq.rec")?;
    let Some(Declaration::Recursor { uparams, .. }) = kernel.environment().get(eq_rec) else {
        return Err(DeclineReason::UnsupportedRecursorShape(
            "Eq.rec is not a Recursor declaration".to_owned(),
        ));
    };
    if uparams.len() != 2 {
        return Err(DeclineReason::UnsupportedRecursorShape(format!(
            "Eq.rec has {} universe parameters, expected 2",
            uparams.len()
        )));
    }
    Ok(EqPrimitives {
        eq,
        eq_refl,
        eq_rec,
    })
}

/// The ambient `Iff`/`Iff.intro` primitives — `Iff`'s own single, two-field
/// constructor, discovered by exact name and checked structurally (never
/// assumed): `Iff.intro` must be a `Constructor` declaration with exactly two
/// fields beyond `Iff`'s own two parameters. Optional at the top level (a
/// pure `Eq`-family fact like `refl`/`symm`/`trans` never needs it), so
/// callers that only ever reach `Eq` goals are unaffected by its absence.
struct IffPrimitives {
    iff: NameId,
    iff_intro: NameId,
}

fn discover_iff(kernel: &Kernel) -> Result<IffPrimitives, DeclineReason> {
    let iff = exact_name(kernel, "Iff")?;
    let iff_intro = exact_name(kernel, "Iff.intro")?;
    let Some(Declaration::Constructor { num_fields, .. }) = kernel.environment().get(iff_intro)
    else {
        return Err(DeclineReason::UnsupportedIffShape(
            "Iff.intro is not a Constructor declaration".to_owned(),
        ));
    };
    if *num_fields != 2 {
        return Err(DeclineReason::UnsupportedIffShape(format!(
            "Iff.intro has {num_fields} fields beyond Iff's own parameters, expected 2"
        )));
    }
    Ok(IffPrimitives { iff, iff_intro })
}

/// A parsed `Eq.{level} carrier lhs rhs` goal.
#[derive(Debug, Clone, Copy)]
struct EqGoal {
    level: LevelId,
    carrier: ExprId,
    lhs: ExprId,
    rhs: ExprId,
}

fn parse_eq_goal(kernel: &Kernel, eq_name: NameId, goal: ExprId) -> Option<EqGoal> {
    let (head, arguments) = app_spine(kernel, goal);
    let ExprNode::Const(name, levels) = kernel.expr_node(head) else {
        return None;
    };
    if *name != eq_name || arguments.len() != 3 || levels.len() != 1 {
        return None;
    }
    Some(EqGoal {
        level: levels[0],
        carrier: arguments[0],
        lhs: arguments[1],
        rhs: arguments[2],
    })
}

fn build_eq(
    kernel: &mut Kernel,
    eq: NameId,
    level: LevelId,
    carrier: ExprId,
    x: ExprId,
    y: ExprId,
) -> ExprId {
    let head = kernel.const_(eq, vec![level]);
    let with_carrier = kernel.app(head, carrier);
    let with_x = kernel.app(with_carrier, x);
    kernel.app(with_x, y)
}

fn build_eq_refl(
    kernel: &mut Kernel,
    eq_refl: NameId,
    level: LevelId,
    carrier: ExprId,
    x: ExprId,
) -> ExprId {
    let head = kernel.const_(eq_refl, vec![level]);
    let with_carrier = kernel.app(head, carrier);
    kernel.app(with_carrier, x)
}

/// `Eq.symm`'s value at a specific `(level, carrier, x, y, proof)`, built
/// directly from `Eq.rec` with motive `fun (z : carrier) (_ : Eq x z) => Eq z
/// x` — never a borrowed `Eq.symm`. Mirrors
/// `trusted_substitution::build_eq_symm` exactly (independently re-derived;
/// that function is private).
#[allow(clippy::too_many_arguments)]
fn build_eq_symm(
    kernel: &mut Kernel,
    eqp: &EqPrimitives,
    next_fvar: &mut u64,
    level: LevelId,
    carrier: ExprId,
    x: ExprId,
    y: ExprId,
    proof: ExprId,
) -> ExprId {
    let anon = kernel.anon();
    *next_fvar += 1;
    let z_fv = *next_fvar;
    let z = kernel.fvar(z_fv);
    let concl = build_eq(kernel, eqp.eq, level, carrier, z, x);
    let hyp_ty = build_eq(kernel, eqp.eq, level, carrier, x, z);
    let anon_hyp = kernel.anon();
    let inner = kernel.lam(anon_hyp, hyp_ty, concl, BinderInfo::Default);
    let motive = lam_fv(kernel, anon, z_fv, carrier, inner, BinderInfo::Default);
    let refl_case = build_eq_refl(kernel, eqp.eq_refl, level, carrier, x);
    let zero = kernel.level_zero();
    let rec = kernel.const_(eqp.eq_rec, vec![zero, level]);
    let with_carrier = kernel.app(rec, carrier);
    let with_x = kernel.app(with_carrier, x);
    let with_motive = kernel.app(with_x, motive);
    let with_minor = kernel.app(with_motive, refl_case);
    let with_y = kernel.app(with_minor, y);
    kernel.app(with_y, proof)
}

/// Transitivity of `Eq`, from `p1 : Eq level carrier x y` and `p2 : Eq level
/// carrier y z`, to a proof of `Eq level carrier x z` — again directly from
/// `Eq.rec`, never a borrowed `Eq.trans`. Mirrors
/// `trusted_substitution::build_trans` exactly (independently re-derived).
#[allow(clippy::too_many_arguments)]
fn build_eq_trans(
    kernel: &mut Kernel,
    eqp: &EqPrimitives,
    next_fvar: &mut u64,
    level: LevelId,
    carrier: ExprId,
    x: ExprId,
    y: ExprId,
    p1: ExprId,
    z: ExprId,
    p2: ExprId,
) -> ExprId {
    let anon = kernel.anon();
    *next_fvar += 1;
    let z_fv = *next_fvar;
    let zvar = kernel.fvar(z_fv);
    let concl = build_eq(kernel, eqp.eq, level, carrier, x, zvar);
    let hyp_ty = build_eq(kernel, eqp.eq, level, carrier, y, zvar);
    let anon_hyp = kernel.anon();
    let inner = kernel.lam(anon_hyp, hyp_ty, concl, BinderInfo::Default);
    let motive = lam_fv(kernel, anon, z_fv, carrier, inner, BinderInfo::Default);
    let zero = kernel.level_zero();
    let rec = kernel.const_(eqp.eq_rec, vec![zero, level]);
    let with_carrier = kernel.app(rec, carrier);
    let with_x = kernel.app(with_carrier, y);
    let with_motive = kernel.app(with_x, motive);
    let with_minor = kernel.app(with_motive, p1);
    let with_z = kernel.app(with_minor, z);
    kernel.app(with_z, p2)
}

/// `Iff.intro p q mp mpr : Iff p q`. `Iff`'s own structure parameters (`p`,
/// `q`) are the constructor's leading positional arguments at the term level
/// regardless of their surface binder-info, exactly like every other
/// constructor application this codebase builds by hand (e.g.
/// `bounded_induction_support::build_eq_refl` applies `Eq`'s own carrier
/// positionally). `Iff` is `Prop`-valued with no polymorphism, so
/// `Iff.intro` takes no universe arguments.
#[allow(clippy::similar_names)]
fn build_iff_intro(
    kernel: &mut Kernel,
    iffp: &IffPrimitives,
    p: ExprId,
    q: ExprId,
    mp: ExprId,
    mpr: ExprId,
) -> ExprId {
    let head = kernel.const_(iffp.iff_intro, vec![]);
    let step1 = kernel.app(head, p);
    let step2 = kernel.app(step1, q);
    let step3 = kernel.app(step2, mp);
    kernel.app(step3, mpr)
}

/// A retained ordinary hypothesis introduced while peeling a leading `Pi`:
/// the free variable standing for it, and its (uninstantiated) type.
type Hyp = (u64, ExprId);

struct Search {
    eqp: EqPrimitives,
    iffp: Option<IffPrimitives>,
    next_fvar: u64,
    binders_left: usize,
    binders_used: usize,
}

impl Search {
    /// Peel every leading `Pi` binder of `goal` into a fresh free variable,
    /// recording each as an ordinary hypothesis (no dependent/induction
    /// distinction — see the module doc), then close the terminal goal.
    fn attempt(
        &mut self,
        kernel: &mut Kernel,
        goal: ExprId,
        hyps: &mut Vec<Hyp>,
    ) -> Result<ExprId, DeclineReason> {
        if let ExprNode::Pi(name, ty, body, info) = kernel.expr_node(goal).clone() {
            if self.binders_left == 0 {
                return Err(DeclineReason::BinderBudgetExceeded);
            }
            self.binders_left -= 1;
            self.binders_used += 1;
            self.next_fvar += 1;
            let fv = self.next_fvar;
            let x = kernel.fvar(fv);
            let body_inst = kernel.instantiate(body, &[x]);
            hyps.push((fv, ty));
            let inner = self.attempt(kernel, body_inst, hyps);
            hyps.pop();
            self.binders_left += 1;
            let value = inner?;
            return Ok(lam_fv(kernel, name, fv, ty, value, info));
        }
        self.close_terminal(kernel, goal, hyps)
    }

    fn close_terminal(
        &mut self,
        kernel: &mut Kernel,
        goal: ExprId,
        hyps: &mut Vec<Hyp>,
    ) -> Result<ExprId, DeclineReason> {
        // Try Iff BEFORE whnf: `Iff p q` is already in whnf (an inductive
        // type former never itself iota/beta-reduces), and whnf-ing first
        // would gain nothing here while costing a needless unfold attempt.
        if let Some(proof) = self.try_iff(kernel, goal, hyps)? {
            return Ok(proof);
        }
        let goal_whnf = kernel.whnf(goal);
        self.try_eq(kernel, goal_whnf, hyps)
    }

    #[allow(clippy::similar_names)]
    fn try_iff(
        &mut self,
        kernel: &mut Kernel,
        goal: ExprId,
        hyps: &mut Vec<Hyp>,
    ) -> Result<Option<ExprId>, DeclineReason> {
        let (head, args) = app_spine(kernel, goal);
        let ExprNode::Const(name, _) = kernel.expr_node(head).clone() else {
            return Ok(None);
        };
        let Some(iffp) = &self.iffp else {
            return Ok(None);
        };
        if name != iffp.iff || args.len() != 2 {
            return Ok(None);
        }
        let (p, q) = (args[0], args[1]);
        if self.binders_left < 2 {
            return Err(DeclineReason::BinderBudgetExceeded);
        }

        self.binders_left -= 1;
        self.binders_used += 1;
        self.next_fvar += 1;
        let hp_fv = self.next_fvar;
        hyps.push((hp_fv, p));
        let mp_body = self.attempt(kernel, q, hyps);
        hyps.pop();
        self.binders_left += 1;
        let anon = kernel.anon();
        let mp = lam_fv(kernel, anon, hp_fv, p, mp_body?, BinderInfo::Default);

        self.binders_left -= 1;
        self.binders_used += 1;
        self.next_fvar += 1;
        let hq_fv = self.next_fvar;
        hyps.push((hq_fv, q));
        let mpr_body = self.attempt(kernel, p, hyps);
        hyps.pop();
        self.binders_left += 1;
        let anon = kernel.anon();
        let mpr = lam_fv(kernel, anon, hq_fv, q, mpr_body?, BinderInfo::Default);

        // `iffp` was borrowed immutably above and dropped before these
        // `&mut Kernel` calls; re-borrow to build the final application.
        let iffp = self.iffp.as_ref().expect("checked Some above");
        Ok(Some(build_iff_intro(kernel, iffp, p, q, mp, mpr)))
    }

    fn try_eq(
        &mut self,
        kernel: &mut Kernel,
        goal_whnf: ExprId,
        hyps: &[Hyp],
    ) -> Result<ExprId, DeclineReason> {
        let Some(goal) = parse_eq_goal(kernel, self.eqp.eq, goal_whnf) else {
            return Err(DeclineReason::TerminalNotClosed);
        };
        if kernel.def_eq(goal.lhs, goal.rhs) {
            return Ok(build_eq_refl(
                kernel,
                self.eqp.eq_refl,
                goal.level,
                goal.carrier,
                goal.lhs,
            ));
        }
        // Symmetry: one hypothesis `h : Eq carrier rhs lhs` closes `Eq
        // carrier lhs rhs` via `Eq.symm h`.
        for &(fv, ty) in hyps.iter().rev() {
            let ty_whnf = kernel.whnf(ty);
            let Some(h) = parse_eq_goal(kernel, self.eqp.eq, ty_whnf) else {
                continue;
            };
            if kernel.def_eq(h.carrier, goal.carrier)
                && kernel.def_eq(h.lhs, goal.rhs)
                && kernel.def_eq(h.rhs, goal.lhs)
            {
                let proof = kernel.fvar(fv);
                return Ok(build_eq_symm(
                    kernel,
                    &self.eqp,
                    &mut self.next_fvar,
                    h.level,
                    h.carrier,
                    h.lhs,
                    h.rhs,
                    proof,
                ));
            }
        }
        // Transitivity: hypotheses `h1 : Eq carrier lhs mid`, `h2 : Eq
        // carrier mid rhs` close `Eq carrier lhs rhs` via `Eq.trans h1 h2`.
        for &(fv1, ty1) in hyps {
            let ty1_whnf = kernel.whnf(ty1);
            let Some(h1) = parse_eq_goal(kernel, self.eqp.eq, ty1_whnf) else {
                continue;
            };
            if !(kernel.def_eq(h1.carrier, goal.carrier) && kernel.def_eq(h1.lhs, goal.lhs)) {
                continue;
            }
            for &(fv2, ty2) in hyps {
                if fv1 == fv2 {
                    continue;
                }
                let ty2_whnf = kernel.whnf(ty2);
                let Some(h2) = parse_eq_goal(kernel, self.eqp.eq, ty2_whnf) else {
                    continue;
                };
                if kernel.def_eq(h2.carrier, goal.carrier)
                    && kernel.def_eq(h1.rhs, h2.lhs)
                    && kernel.def_eq(h2.rhs, goal.rhs)
                {
                    let p1 = kernel.fvar(fv1);
                    let p2 = kernel.fvar(fv2);
                    return Ok(build_eq_trans(
                        kernel,
                        &self.eqp,
                        &mut self.next_fvar,
                        h1.level,
                        h1.carrier,
                        h1.lhs,
                        h1.rhs,
                        p1,
                        h2.rhs,
                        p2,
                    ));
                }
            }
        }
        Err(DeclineReason::TerminalNotClosed)
    }
}

/// First free-variable id this producer mints. Chosen far above anything an
/// import stream, `bounded_induction_support` (`9_000_000`), or
/// `trusted_substitution` (`900_000_000`) would use, so this producer's free
/// variables cannot collide with any of them within one process.
const FVAR_BASE: u64 = 9_500_000_000;

/// Entry point: propose a candidate proof of `goal` under this module's
/// bounded Eq/Iff-combinator schema. Declines (never panics, never hangs)
/// whenever the goal is not entirely built from `Pi` binders over an
/// eventual `Eq`- or `Iff`-headed terminal this schema's refl/symm/trans/
/// `Iff.intro` combinators can close.
pub fn propose_modeq_family(kernel: &mut Kernel, goal: ExprId) -> Result<Candidate, DeclineReason> {
    let eqp = discover_eq(kernel)?;
    let iffp = discover_iff(kernel).ok();
    let mut search = Search {
        eqp,
        iffp,
        next_fvar: FVAR_BASE,
        binders_left: MAX_BINDERS,
        binders_used: 0,
    };
    let mut hyps = Vec::new();
    let proof = search.attempt(kernel, goal, &mut hyps)?;
    Ok(Candidate {
        proof,
        binders_used: search.binders_used,
    })
}

/// The mechanical circularity/trust audit an admitted candidate must pass,
/// computed **only** from `Kernel::declaration_dependency_closure` /
/// `Kernel::axiom_footprint` / `Kernel::theorem_dependencies` — never from a
/// doc comment, never from a head-symbol text match on a rendered name. This
/// is a pure function of an already-`add_declaration`-admitted `candidate`,
/// so `modeq_family_operation` and this module's own
/// `crates/axeyum-lean-import/tests/modeq_family_operation.rs` adversarial
/// fixture call the exact same check.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CircularityAudit {
    /// Whether `candidate`'s full transitive dependency closure contains
    /// `target` itself — the direct self-citation this guard exists for.
    pub target_dependency: bool,
    /// `Kernel::axiom_footprint(candidate)`'s length: any `Axiom`/`Opaque`/
    /// `Quotient` reached. This module's own construction never introduces
    /// one, so a nonzero count here always means the candidate reached
    /// something outside this module's own Eq/Iff primitives.
    pub axiom_footprint: usize,
    /// `Kernel::theorem_dependencies(candidate)`'s length: any OTHER
    /// already-proved `Theorem` — a sibling `ModEq` fact or anything else —
    /// the candidate cited instead of deriving everything from this module's
    /// own Eq/Iff primitives (all of which are `Inductive`/`Constructor`/
    /// `Recursor` declarations, never `Theorem`-kind, so this module's own
    /// candidates always measure zero here).
    pub theorem_dependencies: usize,
}

impl CircularityAudit {
    /// The candidate is genuinely independent of `target` and of every other
    /// already-proved theorem: no self-citation, no axiom/opaque/quotient
    /// reached, no borrowed theorem cited.
    #[must_use]
    pub fn passes(&self) -> bool {
        !self.target_dependency && self.axiom_footprint == 0 && self.theorem_dependencies == 0
    }
}

/// Compute [`CircularityAudit`] for an already-admitted `candidate` against
/// `target`.
#[must_use]
pub fn audit_circularity(kernel: &Kernel, candidate: NameId, target: NameId) -> CircularityAudit {
    let closure = kernel.declaration_dependency_closure(candidate);
    CircularityAudit {
        target_dependency: closure.contains(&target),
        axiom_footprint: kernel.axiom_footprint(candidate).len(),
        theorem_dependencies: kernel.theorem_dependencies(candidate).len(),
    }
}

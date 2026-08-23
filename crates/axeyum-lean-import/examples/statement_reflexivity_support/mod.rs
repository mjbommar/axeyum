//! Untrusted, bounded reflexivity proposal logic shared with adversarial tests.
//!
//! The producer recognizes a fixed, small set of terminal-goal shapes after
//! peeling the goal's leading `∀`/`→` telescope, and for each shape proposes
//! a candidate proof built only from **constructors and reducible
//! definitions** already present in the untrusted stream's own environment —
//! never a cited `Theorem`. The independent kernel's own type checker (via
//! [`axeyum_lean_kernel::Kernel::add_declaration`], called by the two
//! examples that use this module) is the sole authority on whether a
//! candidate is valid: nothing here needs to be trusted, only bounded.
//!
//! Supported terminal heads:
//!
//! - `Eq` (3 args: type, lhs, rhs) — propose `Eq.refl lhs`, the original
//!   route. Valid whenever lhs/rhs are definitionally equal, regardless of
//!   how deep the reduction is (β/δ/ι), since the kernel does the real work.
//! - `Nat.le` / `LE.le` (Nat-typed) — propose `Nat.le.refl a`, valid exactly
//!   when `b` is definitionally `a`.
//! - `Nat.lt` / `LT.lt` (Nat-typed) — propose `Nat.le.refl (Nat.succ a)`,
//!   valid exactly when `b` is definitionally `Nat.succ a` (e.g. `n < n+1`,
//!   since `n+1` δ-reduces to `Nat.succ n`).
//! - `Ne` (Nat-typed) — recognized only when one side is structurally
//!   `Nat.zero` and the other `Nat.succ _` (a real constructor mismatch;
//!   never attempted for a *stuck* term, e.g. a recursive function applied
//!   to a free variable, which is exactly what most real `≠` goals in this
//!   producer's target population turn out to be). Proposes a
//!   `Nat.noConfusion`-based refutation of the hypothesized equality, the
//!   same idiom Lean core itself uses for `Nat.succ_ne_zero`.
//! - `Nat.dvd` / `Dvd.dvd` (Nat-typed) — recognized only when the divisor
//!   side is structurally `Nat.mul a c` for some `c` (a `dvd_mul_right`-style
//!   goal). Building the required `Exists.intro` witness from raw primitives
//!   costs more [`MAX_CONSTRUCTED_NODES`] than this producer's fixed budget
//!   allows for any nonzero binder count, so — see [`propose_dvd`] — this
//!   route currently always declines via the *construction budget*, never a
//!   shape mismatch, once past its cheap structural pre-checks. That is a
//!   real, measured property of this budget and this construction, not an
//!   unimplemented case: the pre-checks are exercised (and adversarially
//!   tested) on their own.
//!
//! Every route is **blind to truth**: it proposes a candidate whenever the
//! syntactic shape matches, and relies entirely on the caller's independent
//! kernel to reject a candidate whose sides are not actually definitionally
//! equal. This is what makes widening safe — a bug in any route here can only
//! ever produce *more declines*, never a false admission, because the
//! declaration's *stated type* (`ty: goal`, set by the caller) is always the
//! untouched original goal, and the kernel's own type checker independently
//! infers and compares the candidate's type against it.

use axeyum_lean_kernel::{BinderInfo, ExprId, ExprNode, Kernel, LevelId, NameId};

pub const MAX_BINDERS: usize = 8;
pub const MAX_CONSTRUCTED_NODES: usize = 16;

#[derive(Debug)]
pub struct Candidate {
    pub proof: ExprId,
    pub binders: usize,
    pub constructed_nodes: usize,
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

fn exact_name(kernel: &Kernel, rendered: &str) -> Result<NameId, String> {
    let matches: Vec<_> = kernel
        .environment()
        .iter()
        .filter_map(|(name, _)| {
            (kernel.display_name(*name).to_string() == rendered).then_some(*name)
        })
        .collect();
    match matches.as_slice() {
        [name] => Ok(*name),
        _ => Err(format!(
            "required declaration {rendered:?} occurs {} times",
            matches.len()
        )),
    }
}

fn is_nat_const(kernel: &Kernel, expression: ExprId, nat_name: NameId) -> bool {
    matches!(kernel.expr_node(expression), ExprNode::Const(name, _) if *name == nat_name)
}

/// Extract the trailing `(a, b)` operands of a binary Nat relation or
/// divisibility application, accepting either the raw 2-arg form
/// (`Nat.le a b`, exactly the shape [`super::nat_order_substitution`] builds
/// against) or the 4-arg typeclass-method form real Mathlib surface notation
/// (`≤`, `<`, `∣`) elaborates to (`LE.le Nat inst a b`). The typeclass form is
/// only accepted when its type argument really is `Nat` — this producer never
/// reasons about any other carrier.
fn nat_relation_args(
    kernel: &Kernel,
    direct_name: &str,
    rendered_head: &str,
    arguments: &[ExprId],
) -> Option<(ExprId, ExprId)> {
    if rendered_head == direct_name && arguments.len() == 2 {
        return Some((arguments[0], arguments[1]));
    }
    if arguments.len() == 4 {
        let nat_name = exact_name(kernel, "Nat").ok()?;
        if is_nat_const(kernel, arguments[0], nat_name) {
            return Some((arguments[2], arguments[3]));
        }
    }
    None
}

enum NatCtor {
    Zero,
    Succ,
}

/// Classify `expression` as the literal `Nat.zero` constructor (no
/// arguments) or a `Nat.succ _` application (one argument), or neither.
/// Purely structural, no reduction is attempted: a *stuck* Nat-valued term
/// (anything not already headed by one of the two constructors, e.g. a
/// recursive function applied to a free variable) is correctly reported as
/// neither, which is what most real `≠` goals over a symbolic argument are.
fn nat_ctor_shape(kernel: &Kernel, expression: ExprId) -> Option<NatCtor> {
    let (head, arguments) = app_spine(kernel, expression);
    let ExprNode::Const(name, _) = kernel.expr_node(head) else {
        return None;
    };
    match (
        kernel.display_name(*name).to_string().as_str(),
        arguments.len(),
    ) {
        ("Nat.zero", 0) => Some(NatCtor::Zero),
        ("Nat.succ", 1) => Some(NatCtor::Succ),
        _ => None,
    }
}

fn synth_name(kernel: &mut Kernel, label: &str) -> NameId {
    let root = kernel.anon();
    kernel.name_str(root, label)
}

/// Tracks how many proof-term nodes a route has spent building its
/// candidate, so every route (old or new) pays the same
/// [`MAX_CONSTRUCTED_NODES`] budget under the same, honest accounting: one
/// unit per `Kernel` call that becomes (or reshapes) part of the constructed
/// value. Read-only kernel queries (`expr_node`, `display_name`, `def_eq`,
/// name synthesis) are not proof-term construction and are never counted,
/// matching the original Eq route's convention (which never counted
/// `app_spine`, `display_name`, or `.clone()`).
struct Spend<'k> {
    kernel: &'k mut Kernel,
    nodes: usize,
}

impl<'k> Spend<'k> {
    fn new(kernel: &'k mut Kernel) -> Self {
        Self { kernel, nodes: 0 }
    }

    fn const_(&mut self, name: NameId, levels: Vec<LevelId>) -> ExprId {
        self.nodes += 1;
        self.kernel.const_(name, levels)
    }

    fn app(&mut self, function: ExprId, argument: ExprId) -> ExprId {
        self.nodes += 1;
        self.kernel.app(function, argument)
    }

    fn lam(&mut self, name: NameId, ty: ExprId, body: ExprId, info: BinderInfo) -> ExprId {
        self.nodes += 1;
        self.kernel.lam(name, ty, body, info)
    }

    fn bvar(&mut self, index: u32) -> ExprId {
        self.nodes += 1;
        self.kernel.bvar(index)
    }

    fn lift(&mut self, expression: ExprId, cutoff: u32, amount: u32) -> ExprId {
        self.nodes += 1;
        self.kernel.lift_loose_bvars(expression, cutoff, amount)
    }
}

/// `Eq` route (unchanged from before this producer supported anything else):
/// propose `Eq.refl lhs`, reusing the goal's own `Eq.{levels}` universe
/// arguments.
fn propose_eq(
    spend: &mut Spend,
    levels: Vec<LevelId>,
    arguments: &[ExprId],
) -> Result<ExprId, String> {
    if arguments.len() != 3 {
        return Err("terminal goal is not an exact Eq application".to_owned());
    }
    let eq_refl_name = exact_name(spend.kernel, "Eq.refl")?;
    let mut proof = spend.const_(eq_refl_name, levels);
    proof = spend.app(proof, arguments[0]);
    proof = spend.app(proof, arguments[1]);
    Ok(proof)
}

/// `Nat.le` / `LE.le` route: propose `Nat.le.refl a`, valid exactly when the
/// goal's `b` is definitionally `a`.
fn propose_le(
    spend: &mut Spend,
    rendered_head: &str,
    arguments: &[ExprId],
) -> Result<ExprId, String> {
    let (a, _b) = nat_relation_args(spend.kernel, "Nat.le", rendered_head, arguments)
        .ok_or_else(|| "terminal goal is not an exact Nat.le application".to_owned())?;
    let le_refl_name = exact_name(spend.kernel, "Nat.le.refl")?;
    let refl = spend.const_(le_refl_name, vec![]);
    Ok(spend.app(refl, a))
}

/// `Nat.lt` / `LT.lt` route: propose `Nat.le.refl (Nat.succ a)`, valid
/// exactly when the goal's `b` is definitionally `Nat.succ a` (e.g.
/// `n < n + 1`, since `n + 1` δ-reduces to `Nat.succ n`).
fn propose_lt(
    spend: &mut Spend,
    rendered_head: &str,
    arguments: &[ExprId],
) -> Result<ExprId, String> {
    let (a, _b) = nat_relation_args(spend.kernel, "Nat.lt", rendered_head, arguments)
        .ok_or_else(|| "terminal goal is not an exact Nat.lt application".to_owned())?;
    let succ_name = exact_name(spend.kernel, "Nat.succ")?;
    let le_refl_name = exact_name(spend.kernel, "Nat.le.refl")?;
    let succ_const = spend.const_(succ_name, vec![]);
    let succ_a = spend.app(succ_const, a);
    let refl_const = spend.const_(le_refl_name, vec![]);
    Ok(spend.app(refl_const, succ_a))
}

/// `Ne` route: recognized only when exactly one of the two sides is
/// structurally `Nat.zero` and the other `Nat.succ _`. Proposes
/// `fun (h : a = b) => Nat.noConfusion False a b h`, the same idiom Lean core
/// itself uses for `Nat.succ_ne_zero`.
fn propose_ne(spend: &mut Spend, arguments: &[ExprId]) -> Result<ExprId, String> {
    if arguments.len() != 3 {
        return Err("terminal goal is not an exact Ne application".to_owned());
    }
    let (ty, a, b) = (arguments[0], arguments[1], arguments[2]);
    let nat_name = exact_name(spend.kernel, "Nat")?;
    if !is_nat_const(spend.kernel, ty, nat_name) {
        return Err("Ne route requires a Nat-typed Ne application".to_owned());
    }
    let mismatched = matches!(
        (
            nat_ctor_shape(spend.kernel, a),
            nat_ctor_shape(spend.kernel, b)
        ),
        (Some(NatCtor::Zero), Some(NatCtor::Succ)) | (Some(NatCtor::Succ), Some(NatCtor::Zero))
    );
    if !mismatched {
        return Err(
            "Ne goal sides are not a recognized Nat.zero/Nat.succ constructor mismatch".to_owned(),
        );
    }

    let eq_name = exact_name(spend.kernel, "Eq")?;
    let no_confusion_name = exact_name(spend.kernel, "Nat.noConfusion")?;
    let false_name = exact_name(spend.kernel, "False")?;

    let zero_level = spend.kernel.level_zero();
    let type_level = spend.kernel.level_succ(zero_level);

    let eq_const = spend.const_(eq_name, vec![type_level]);
    let mut domain_ty = spend.app(eq_const, ty);
    domain_ty = spend.app(domain_ty, a);
    domain_ty = spend.app(domain_ty, b);

    let a_lifted = spend.lift(a, 0, 1);
    let b_lifted = spend.lift(b, 0, 1);
    let hyp_bvar = spend.bvar(0);
    let false_const = spend.const_(false_name, vec![]);
    let noconf_const = spend.const_(no_confusion_name, vec![zero_level]);
    let mut body = spend.app(noconf_const, false_const);
    body = spend.app(body, a_lifted);
    body = spend.app(body, b_lifted);
    body = spend.app(body, hyp_bvar);

    let h_name = synth_name(spend.kernel, "h");
    Ok(spend.lam(h_name, domain_ty, body, BinderInfo::Default))
}

/// `Nat.dvd` / `Dvd.dvd` route: recognized only when the divisor side `n` is
/// structurally `Nat.mul a c` for some witness `c` (a `dvd_mul_right`-style
/// goal — `n = a * c` is then literally reflexive). Proposes
/// `Exists.intro Nat (fun q => n = a * q) c (Eq.refl n)`.
///
/// Building this from raw `Exists`/`Eq` primitives costs at least 19
/// constructed nodes (the `Exists.intro` spine, the motive lambda's own `Eq`
/// application, and the rebuilt `a * q`), which already exceeds
/// [`MAX_CONSTRUCTED_NODES`] with **zero** leading binders — so, past its two
/// cheap structural/semantic pre-checks below, this route always declines via
/// the construction-budget check shared with every other route. That is a
/// real, measured property of this construction and this fixed budget, which
/// this producer's contract does not allow raising.
fn propose_dvd(
    spend: &mut Spend,
    rendered_head: &str,
    arguments: &[ExprId],
) -> Result<ExprId, String> {
    let (a, n) = nat_relation_args(spend.kernel, "Nat.dvd", rendered_head, arguments)
        .ok_or_else(|| "terminal goal is not an exact Nat.dvd application".to_owned())?;

    let (mul_head, mul_arguments) = app_spine(spend.kernel, n);
    let shape_error = || "Dvd goal's divisor is not a recognized Nat.mul application".to_owned();
    let ExprNode::Const(mul_name, _) = spend.kernel.expr_node(mul_head) else {
        return Err(shape_error());
    };
    let mul_name = *mul_name;
    if mul_arguments.len() != 2 || spend.kernel.display_name(mul_name).to_string() != "Nat.mul" {
        return Err(shape_error());
    }
    let (mul_a, mul_c) = (mul_arguments[0], mul_arguments[1]);
    if !spend.kernel.def_eq(a, mul_a) {
        return Err(
            "Dvd goal's divisor does not match the recognized product's first factor".to_owned(),
        );
    }

    let nat_name = exact_name(spend.kernel, "Nat")?;
    let eq_name = exact_name(spend.kernel, "Eq")?;
    let eq_refl_name = exact_name(spend.kernel, "Eq.refl")?;
    let exists_intro_name = exact_name(spend.kernel, "Exists.intro")?;

    let zero_level = spend.kernel.level_zero();
    let type_level = spend.kernel.level_succ(zero_level);

    let nat_ty = spend.const_(nat_name, vec![]);
    let n_lifted = spend.lift(n, 0, 1);
    let a_lifted = spend.lift(a, 0, 1);
    let c_bvar = spend.bvar(0);
    let mul_head_app = spend.app(mul_head, a_lifted);
    let mul_rebuilt = spend.app(mul_head_app, c_bvar);
    let eq_const_inner = spend.const_(eq_name, vec![type_level]);
    let mut motive_body = spend.app(eq_const_inner, nat_ty);
    motive_body = spend.app(motive_body, n_lifted);
    motive_body = spend.app(motive_body, mul_rebuilt);
    let c_name = synth_name(spend.kernel, "c");
    let motive = spend.lam(c_name, nat_ty, motive_body, BinderInfo::Default);

    let eq_refl_const = spend.const_(eq_refl_name, vec![type_level]);
    let mut eq_refl_proof = spend.app(eq_refl_const, nat_ty);
    eq_refl_proof = spend.app(eq_refl_proof, n);

    let exists_intro_const = spend.const_(exists_intro_name, vec![type_level]);
    let mut proof = spend.app(exists_intro_const, nat_ty);
    proof = spend.app(proof, motive);
    proof = spend.app(proof, mul_c);
    proof = spend.app(proof, eq_refl_proof);
    Ok(proof)
}

pub fn propose_reflexivity(kernel: &mut Kernel, goal: ExprId) -> Result<Candidate, String> {
    let mut binders: Vec<(NameId, ExprId, BinderInfo)> = Vec::new();
    let mut cursor = goal;
    while let ExprNode::Pi(name, ty, body, info) = kernel.expr_node(cursor) {
        if binders.len() == MAX_BINDERS {
            return Err(format!("binder budget exceeded: maximum {MAX_BINDERS}"));
        }
        binders.push((*name, *ty, *info));
        cursor = *body;
    }

    let (head, arguments) = app_spine(kernel, cursor);
    let ExprNode::Const(head_name, levels) = kernel.expr_node(head) else {
        return Err("terminal goal is not constant-headed equality".to_owned());
    };
    let head_name = *head_name;
    let levels = levels.clone();
    let rendered_head = kernel.display_name(head_name).to_string();

    let mut spend = Spend::new(kernel);
    let body_proof = match rendered_head.as_str() {
        "Eq" => propose_eq(&mut spend, levels, &arguments)?,
        "Nat.le" | "LE.le" => propose_le(&mut spend, &rendered_head, &arguments)?,
        "Nat.lt" | "LT.lt" => propose_lt(&mut spend, &rendered_head, &arguments)?,
        "Ne" => propose_ne(&mut spend, &arguments)?,
        "Nat.dvd" | "Dvd.dvd" => propose_dvd(&mut spend, &rendered_head, &arguments)?,
        _ => {
            return Err(format!(
                "terminal goal head {rendered_head:?} is not a supported reflexivity target"
            ));
        }
    };

    let mut proof = body_proof;
    for (name, ty, info) in binders.iter().rev() {
        proof = spend.lam(*name, *ty, proof, *info);
    }
    let constructed_nodes = spend.nodes;
    if constructed_nodes > MAX_CONSTRUCTED_NODES {
        return Err(format!(
            "construction budget exceeded: {constructed_nodes} > {MAX_CONSTRUCTED_NODES}"
        ));
    }
    Ok(Candidate {
        proof,
        binders: binders.len(),
        constructed_nodes,
    })
}

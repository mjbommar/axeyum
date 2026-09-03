//! The ℕ fragment: an oriented rewrite set over `+`, `*`, `succ`, `pred`,
//! `sub`, matched first-order against the goal's own `ExprId` graph and
//! applied outermost-first to a fixed point — see the crate-root [module
//! docs](super) for the whole design.
//!
//! ## The default rule set
//!
//! Every identity/annihilator law with no side condition, plus the three
//! defining equations a growing accumulator needs (`Nat.add`/`Nat.mul`
//! recurse on their *second* argument — see
//! `docs/contributor-guide/kernel-proof-engineering.md` — so both are stuck
//! at a symbolic FIRST argument without them):
//!
//! | lemma | statement | role |
//! | --- | --- | --- |
//! | `add_zero` | `add n zero = n` | identity |
//! | `zero_add` | `add zero n = n` | identity |
//! | `mul_zero` | `mul n zero = zero` | annihilator |
//! | `zero_mul` | `mul zero n = zero` | annihilator |
//! | `mul_one` | `mul a one = a` | identity |
//! | `one_mul` | `mul one a = a` | identity |
//! | `pred_succ` | `pred (succ n) = n` | defining |
//! | `sub_zero` | `sub n zero = n` | identity |
//! | `sub_self` | `sub n n = zero` | defining (repeated pattern variable) |
//! | `succ_add` | `add (succ a) b = succ (add a b)` | defining |
//! | `add_succ` | `add a (succ b) = succ (add a b)` | defining |
//! | `succ_mul` | `mul (succ a) b = add (mul a b) b` | defining |
//!
//! `Nat.succ_pred_of_pos` (the brief's `succ_pred`) needs a positivity
//! hypothesis this hypothesis-free matcher cannot discharge; `pred_succ`
//! (unconditional) fills the same "successor/predecessor cancellation" role.

use crate::ExprNode;
use crate::NameId;
use crate::NatOps;
use crate::NatPrelude;
use crate::expr::ExprId;

use super::{Decline, MAX_STEPS, Orientation};

/// One oriented rewrite rule: a previously-declared lemma plus a stateless
/// closure describing its `arity`-ary LHS/RHS pattern over fresh pattern
/// variables — see the crate-root module docs on why this needs no
/// kernel-`Pi`-type introspection.
pub struct Rule<D> {
    /// The declared lemma this rule cites.
    pub name: NameId,
    /// How many pattern variables `build` expects.
    pub arity: usize,
    /// Which side the pattern matches, and which way the rewrite runs.
    pub orientation: Orientation,
    /// `(lhs, rhs)` of the lemma's statement, over `arity` args.
    pub build: fn(&mut D, &[ExprId]) -> (ExprId, ExprId),
}

// `fn` pointers are always `Copy`/`Clone` regardless of `D`; a `#[derive]`
// would additionally (and incorrectly) require `D: Clone`.
impl<D> Clone for Rule<D> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<D> Copy for Rule<D> {}

fn r_add_zero<D: NatOps>(d: &mut D, a: &[ExprId]) -> (ExprId, ExprId) {
    let z = d.zero();
    (d.add(a[0], z), a[0])
}
fn r_zero_add<D: NatOps>(d: &mut D, a: &[ExprId]) -> (ExprId, ExprId) {
    let z = d.zero();
    (d.add(z, a[0]), a[0])
}
fn r_mul_zero<D: NatOps>(d: &mut D, a: &[ExprId]) -> (ExprId, ExprId) {
    let z = d.zero();
    (d.mul(a[0], z), z)
}
fn r_zero_mul<D: NatOps>(d: &mut D, a: &[ExprId]) -> (ExprId, ExprId) {
    let z = d.zero();
    (d.mul(z, a[0]), z)
}
fn r_mul_one<D: NatOps>(d: &mut D, a: &[ExprId]) -> (ExprId, ExprId) {
    let one = d.num(1);
    (d.mul(a[0], one), a[0])
}
fn r_one_mul<D: NatOps>(d: &mut D, a: &[ExprId]) -> (ExprId, ExprId) {
    let one = d.num(1);
    (d.mul(one, a[0]), a[0])
}
fn r_pred_succ<D: NatOps>(d: &mut D, a: &[ExprId]) -> (ExprId, ExprId) {
    let s = d.succ(a[0]);
    (d.pred(s), a[0])
}
fn r_sub_zero<D: NatOps>(d: &mut D, a: &[ExprId]) -> (ExprId, ExprId) {
    let z = d.zero();
    (d.sub(a[0], z), a[0])
}
fn r_sub_self<D: NatOps>(d: &mut D, a: &[ExprId]) -> (ExprId, ExprId) {
    let z = d.zero();
    // Both LHS operands are the SAME `ExprId` (`a[0]` used twice) -- the
    // repeated-pattern-variable case, see the module docs.
    (d.sub(a[0], a[0]), z)
}
fn r_succ_add<D: NatOps>(d: &mut D, a: &[ExprId]) -> (ExprId, ExprId) {
    let sa = d.succ(a[0]);
    let lhs = d.add(sa, a[1]);
    let inner = d.add(a[0], a[1]);
    let rhs = d.succ(inner);
    (lhs, rhs)
}
fn r_add_succ<D: NatOps>(d: &mut D, a: &[ExprId]) -> (ExprId, ExprId) {
    let sb = d.succ(a[1]);
    let lhs = d.add(a[0], sb);
    let inner = d.add(a[0], a[1]);
    let rhs = d.succ(inner);
    (lhs, rhs)
}
fn r_succ_mul<D: NatOps>(d: &mut D, a: &[ExprId]) -> (ExprId, ExprId) {
    let sa = d.succ(a[0]);
    let lhs = d.mul(sa, a[1]);
    let ab = d.mul(a[0], a[1]);
    let rhs = d.add(ab, a[1]);
    (lhs, rhs)
}

/// The default ℕ rewrite set — see the module docs' table.
pub fn default_rules<D: NatOps>(p: &NatPrelude) -> Vec<Rule<D>> {
    use Orientation::Forward;
    vec![
        Rule {
            name: p.add_zero,
            arity: 1,
            orientation: Forward,
            build: r_add_zero,
        },
        Rule {
            name: p.zero_add,
            arity: 1,
            orientation: Forward,
            build: r_zero_add,
        },
        Rule {
            name: p.mul_zero,
            arity: 1,
            orientation: Forward,
            build: r_mul_zero,
        },
        Rule {
            name: p.zero_mul,
            arity: 1,
            orientation: Forward,
            build: r_zero_mul,
        },
        Rule {
            name: p.mul_one,
            arity: 1,
            orientation: Forward,
            build: r_mul_one,
        },
        Rule {
            name: p.one_mul,
            arity: 1,
            orientation: Forward,
            build: r_one_mul,
        },
        Rule {
            name: p.pred_succ,
            arity: 1,
            orientation: Forward,
            build: r_pred_succ,
        },
        Rule {
            name: p.sub_zero,
            arity: 1,
            orientation: Forward,
            build: r_sub_zero,
        },
        Rule {
            name: p.sub_self,
            arity: 1,
            orientation: Forward,
            build: r_sub_self,
        },
        Rule {
            name: p.succ_add,
            arity: 2,
            orientation: Forward,
            build: r_succ_add,
        },
        Rule {
            name: p.add_succ,
            arity: 2,
            orientation: Forward,
            build: r_add_succ,
        },
        Rule {
            name: p.succ_mul,
            arity: 2,
            orientation: Forward,
            build: r_succ_mul,
        },
    ]
}

/// The default set plus caller-supplied extras for one call — the design's
/// "a list of `(lemma NameId, orientation)` the caller supplies plus a
/// default set per carrier".
pub fn with_extra<D: NatOps>(defaults: &[Rule<D>], extra: &[Rule<D>]) -> Vec<Rule<D>> {
    let mut rules = defaults.to_vec();
    rules.extend_from_slice(extra);
    rules
}

fn r_right_distrib<D: NatOps>(d: &mut D, a: &[ExprId]) -> (ExprId, ExprId) {
    let sum = d.add(a[0], a[1]);
    let lhs = d.mul(sum, a[2]);
    let ac = d.mul(a[0], a[2]);
    let bc = d.mul(a[1], a[2]);
    let rhs = d.add(ac, bc);
    (lhs, rhs)
}

/// `Nat.right_distrib` as a caller-supplied extra rule: `mul (add a b) c =
/// add (mul a c) (mul b c)`. Not in [`default_rules`] — it is one-directional
/// and matches only when the multiplicand's LEFT operand is itself
/// `add`-headed, so it is safe to add for a goal whose shape needs exactly
/// one distribution step, but it is a caller decision, not a default: the
/// budget in [`rewrite_to_fixpoint`] is the backstop if a goal's operands
/// make it reapply more than expected.
pub fn rule_right_distrib<D: NatOps>(p: &NatPrelude) -> Rule<D> {
    Rule {
        name: p.right_distrib,
        arity: 3,
        orientation: Orientation::Forward,
        build: r_right_distrib,
    }
}

// --- matching -----------------------------------------------------------

/// Mint `rule.arity` fresh pattern variables and instantiate `rule.build`
/// with them, returning `(vars, lhs_pattern, rhs_pattern)`.
fn instantiate<D: NatOps>(d: &mut D, rule: &Rule<D>) -> (Vec<ExprId>, ExprId, ExprId) {
    let vars: Vec<ExprId> = (0..rule.arity)
        .map(|_| {
            let fv = d.fresh_fvar();
            d.kernel().fvar(fv)
        })
        .collect();
    let (lhs, rhs) = (rule.build)(d, &vars);
    (vars, lhs, rhs)
}

/// Walk `pattern` against `target`, binding each of `pattern_vars` on first
/// occurrence and requiring the SAME matched `ExprId` on every later
/// occurrence of that same pattern variable. `bindings[i]` corresponds to
/// `pattern_vars[i]`.
fn try_match<D: NatOps>(
    d: &mut D,
    pattern_vars: &[ExprId],
    pattern: ExprId,
    target: ExprId,
    bindings: &mut [Option<ExprId>],
) -> bool {
    if let Some(pos) = pattern_vars.iter().position(|&v| v == pattern) {
        return if let Some(bound) = bindings[pos] {
            bound == target
        } else {
            bindings[pos] = Some(target);
            true
        };
    }
    if pattern == target {
        return true;
    }
    let pn = d.kernel().expr_node(pattern).clone();
    let tn = d.kernel().expr_node(target).clone();
    match (pn, tn) {
        (ExprNode::App(f1, a1), ExprNode::App(f2, a2)) => {
            try_match(d, pattern_vars, f1, f2, bindings)
                && try_match(d, pattern_vars, a1, a2, bindings)
        }
        _ => false,
    }
}

/// Try every rule at `e` itself (not its subterms). On the first match,
/// return `(new_e, proof: Eq e new_e)`.
fn try_rewrite_at<D: NatOps>(d: &mut D, rules: &[Rule<D>], e: ExprId) -> Option<(ExprId, ExprId)> {
    for rule in rules {
        let (vars, lhs_pat, rhs_pat) = instantiate(d, rule);
        let pattern = match rule.orientation {
            Orientation::Forward => lhs_pat,
            Orientation::Backward => rhs_pat,
        };
        let mut bindings: Vec<Option<ExprId>> = vec![None; rule.arity];
        if !try_match(d, &vars, pattern, e, &mut bindings) {
            continue;
        }
        let args: Vec<ExprId> = match bindings.into_iter().collect::<Option<Vec<_>>>() {
            Some(a) => a,
            // A pattern variable never occurring in `pattern` is a rule
            // authoring bug, not a match failure: every default/extra rule
            // here mentions every one of its variables, so this is
            // unreachable for them.
            None => continue,
        };
        let (lhs_c, rhs_c) = (rule.build)(d, &args);
        let lemma_proof = d.lemma(rule.name, &args);
        let (new_e, proof) = match rule.orientation {
            Orientation::Forward => {
                debug_assert_eq!(lhs_c, e, "matched pattern must reconstruct the target");
                (rhs_c, lemma_proof)
            }
            Orientation::Backward => {
                debug_assert_eq!(rhs_c, e, "matched pattern must reconstruct the target");
                (lhs_c, d.symm(lhs_c, rhs_c, lemma_proof))
            }
        };
        return Some((new_e, proof));
    }
    None
}

/// Outermost-first: try `e` itself, then descend into its arguments under
/// the one operator this fragment knows the *shape* of, lifting a child
/// rewrite back up via [`NatOps::congr`].
///
/// This does NOT do a blind generic `App`-spine descent: `NatOps::congr`
/// (like `NatOps::eq`/`refl`/`symm`/`trans`) is hardcoded to `Eq Nat _ _`
/// (it calls `self.nat_ty()` internally), so it is only well-typed between
/// two `Nat`-typed terms — never between two *partial applications* such as
/// `App(add_const, u)` (type `Nat -> Nat`). Recursing into an `App` node's
/// bare function slot would build exactly that ill-typed `Eq`, which the
/// procedure's own bookkeeping cannot see (it never checks a type) and only
/// the kernel would catch. So this dispatches on the operator at the head
/// of `e`'s spine (`add`/`mul`/`succ`/`pred`/`sub` — the only shapes any
/// [`Rule::build`] closure ever produces) and recurses only into its
/// `Nat`-typed ARGUMENT slots, exactly the pattern
/// `ring::nat::Problem::flatten_add`/`flatten_mul` already use for the same
/// reason.
fn rewrite_step<D: NatOps>(d: &mut D, rules: &[Rule<D>], e: ExprId) -> Option<(ExprId, ExprId)> {
    if let Some(step) = try_rewrite_at(d, rules, e) {
        return Some(step);
    }
    let p = d.prelude();
    let (head, args) = spine(d, e);
    let name = head_const(d, head)?;
    if name == p.add && args.len() == 2 {
        return rewrite_binary(d, rules, args[0], args[1], &|d, x, y| d.add(x, y));
    }
    if name == p.mul && args.len() == 2 {
        return rewrite_binary(d, rules, args[0], args[1], &|d, x, y| d.mul(x, y));
    }
    if name == p.sub && args.len() == 2 {
        return rewrite_binary(d, rules, args[0], args[1], &|d, x, y| d.sub(x, y));
    }
    if name == p.succ && args.len() == 1 {
        return rewrite_unary(d, rules, args[0], &|d, x| d.succ(x));
    }
    if name == p.pred && args.len() == 1 {
        return rewrite_unary(d, rules, args[0], &|d, x| d.pred(x));
    }
    None
}

/// Try rewriting `u` then `v` inside a binary operator `op(u, v)`, lifting
/// whichever side moves first via [`NatOps::congr`] with the OTHER side
/// held fixed in the context closure.
fn rewrite_binary<D: NatOps>(
    d: &mut D,
    rules: &[Rule<D>],
    u: ExprId,
    v: ExprId,
    op: &dyn Fn(&mut D, ExprId, ExprId) -> ExprId,
) -> Option<(ExprId, ExprId)> {
    if let Some((u2, hu)) = rewrite_step(d, rules, u) {
        let new_e = op(d, u2, v);
        let proof = d.congr(u, u2, hu, &|d, x| op(d, x, v));
        return Some((new_e, proof));
    }
    if let Some((v2, hv)) = rewrite_step(d, rules, v) {
        let new_e = op(d, u, v2);
        let proof = d.congr(v, v2, hv, &|d, x| op(d, u, x));
        return Some((new_e, proof));
    }
    None
}

/// As [`rewrite_binary`], for a unary operator `op(u)`.
fn rewrite_unary<D: NatOps>(
    d: &mut D,
    rules: &[Rule<D>],
    u: ExprId,
    op: &dyn Fn(&mut D, ExprId) -> ExprId,
) -> Option<(ExprId, ExprId)> {
    let (u2, hu) = rewrite_step(d, rules, u)?;
    let new_e = op(d, u2);
    let proof = d.congr(u, u2, hu, &|d, x| op(d, x));
    Some((new_e, proof))
}

/// Rewrite `start` to a fixed point under `rules`, returning
/// `(final_term, proof: Eq start final_term, steps_taken)`.
///
/// # Errors
///
/// [`Decline::BudgetExceeded`] when another rewrite is still available after
/// [`MAX_STEPS`] steps.
fn rewrite_to_fixpoint<D: NatOps>(
    d: &mut D,
    rules: &[Rule<D>],
    start: ExprId,
) -> Result<(ExprId, ExprId, usize), Decline> {
    let mut current = start;
    let mut steps: Vec<(ExprId, ExprId)> = Vec::new();
    for _ in 0..MAX_STEPS {
        if let Some((next, proof)) = rewrite_step(d, rules, current) {
            steps.push((next, proof));
            current = next;
        } else {
            let (_last, proof) = d.chain(start, &steps);
            return Ok((current, proof, steps.len()));
        }
    }
    if rewrite_step(d, rules, current).is_some() {
        return Err(Decline::BudgetExceeded);
    }
    let (_last, proof) = d.chain(start, &steps);
    Ok((current, proof, steps.len()))
}

/// Rewrite `start` to a fixed point under `rules`, returning
/// `(final_term, proof: Eq start final_term)` — [`rewrite_to_fixpoint`]
/// without the step count, which is all a caller needs when it does not
/// intend to prove an `Eq` goal itself but instead wants to hand the
/// **normalized** term to a different producer and glue the two proofs back
/// together (`crate::tactic`'s `Then(Simp, _)`, the only caller: `simp`'s
/// own `prove`/`prove_eq` always rewrite *both* sides of an already-`Eq`
/// goal and never need the normal form of a single, unpaired term).
///
/// # Errors
///
/// [`Decline::BudgetExceeded`], as [`rewrite_to_fixpoint`].
pub(crate) fn normalize<D: NatOps>(
    d: &mut D,
    rules: &[Rule<D>],
    start: ExprId,
) -> Result<(ExprId, ExprId), Decline> {
    let (final_term, proof, _steps) = rewrite_to_fixpoint(d, rules, start)?;
    Ok((final_term, proof))
}

// --- proving --------------------------------------------------------------

fn prove_eq_inner<D: NatOps>(
    d: &mut D,
    rules: &[Rule<D>],
    lhs: ExprId,
    rhs: ExprId,
    verify: bool,
) -> Result<ExprId, Decline> {
    let (lhs_final, lhs_proof, lhs_steps) = rewrite_to_fixpoint(d, rules, lhs)?;
    let (rhs_final, rhs_proof, rhs_steps) = rewrite_to_fixpoint(d, rules, rhs)?;
    if lhs_steps == 0 && rhs_steps == 0 {
        return Err(Decline::NoProgress);
    }
    if verify && lhs_final != rhs_final {
        return Err(Decline::SidesDiffer);
    }
    let rhs_back = d.symm(rhs, rhs_final, rhs_proof);
    // When `lhs_final != rhs_final` -- only reachable with `verify = false`,
    // i.e. only from the corrupted-certificate tests -- this splices an `Eq
    // rhs_final rhs`-shaped proof into a slot typed `Eq lhs_final rhs`, and
    // the KERNEL is what refuses it, exactly `ring::nat::prove_eq`'s
    // corrupted-certificate framing.
    Ok(d.trans(lhs, lhs_final, rhs, lhs_proof, rhs_back))
}

/// Prove `Eq Nat lhs rhs` by rewriting both sides to a fixed point under
/// `rules`, or decline.
///
/// # Errors
///
/// [`Decline::NoProgress`] when neither side matched any rule;
/// [`Decline::BudgetExceeded`] when one side did not reach a fixed point
/// within [`MAX_STEPS`]; [`Decline::SidesDiffer`] when both sides reached a
/// fixed point and the two differ.
pub fn prove_eq<D: NatOps>(
    d: &mut D,
    rules: &[Rule<D>],
    lhs: ExprId,
    rhs: ExprId,
) -> Result<ExprId, Decline> {
    prove_eq_inner(d, rules, lhs, rhs, true)
}

/// [`prove_eq`] with the procedure's own "did both sides converge" check
/// switched off — exposed only so the corrupted-certificate tests can ask
/// "does the KERNEL refuse this, or only our own bookkeeping?"
/// ([`Decline::SidesDiffer`] is otherwise unreachable from this entry
/// point). An `Ok` here is **not** a claim the term is well-typed.
///
/// # Errors
///
/// As [`prove_eq`], minus [`Decline::SidesDiffer`].
pub fn prove_eq_unverified<D: NatOps>(
    d: &mut D,
    rules: &[Rule<D>],
    lhs: ExprId,
    rhs: ExprId,
) -> Result<ExprId, Decline> {
    prove_eq_inner(d, rules, lhs, rhs, false)
}

fn spine<D: NatOps>(d: &mut D, e: ExprId) -> (ExprId, Vec<ExprId>) {
    let mut args = Vec::new();
    let mut head = e;
    loop {
        let node = d.kernel().expr_node(head).clone();
        let ExprNode::App(f, a) = node else { break };
        args.push(a);
        head = f;
    }
    args.reverse();
    (head, args)
}

fn head_const<D: NatOps>(d: &mut D, e: ExprId) -> Option<NameId> {
    match d.kernel().expr_node(e).clone() {
        ExprNode::Const(n, _) => Some(n),
        _ => None,
    }
}

/// `Eq Nat lhs rhs`, unpacked.
///
/// # Errors
///
/// [`Decline::GoalNotAtomic`] when the head is not `Eq` at `Nat`.
fn parse_eq_goal<D: NatOps>(
    d: &mut D,
    prelude: &NatPrelude,
    e: ExprId,
) -> Result<(ExprId, ExprId), Decline> {
    let (head, args) = spine(d, e);
    let name = head_const(d, head).ok_or(Decline::GoalNotAtomic)?;
    if name == prelude.logic.eq && args.len() == 3 {
        let nat = d.nat_ty();
        if args[0] == nat {
            return Ok((args[1], args[2]));
        }
    }
    Err(Decline::GoalNotAtomic)
}

/// Prove `goal` (`Eq Nat _ _`) by rewriting both sides to a fixed point
/// under `rules`, or decline.
///
/// # Errors
///
/// [`Decline::GoalNotAtomic`] when `goal`'s head is not `Eq` at `Nat`;
/// otherwise as [`prove_eq`].
pub fn prove<D: NatOps>(
    d: &mut D,
    prelude: &NatPrelude,
    rules: &[Rule<D>],
    goal: ExprId,
) -> Result<ExprId, Decline> {
    let (lhs, rhs) = parse_eq_goal(d, prelude, goal)?;
    prove_eq(d, rules, lhs, rhs)
}

/// Prove `Eq lhs(args) rhs(args)` by proving the identity **generically**
/// over fresh variables and instantiating the result at `args` via ordinary
/// application — the same route `ring::nat::prove_eq_at` uses, needed
/// whenever a retirement call site's actual arguments are themselves built
/// from an operation outside this fragment.
///
/// # Errors
///
/// As [`prove_eq`], applied to the **generic** (fresh-variable) goal `build`
/// states.
pub fn prove_eq_at<D: NatOps>(
    d: &mut D,
    rules: &[Rule<D>],
    args: &[ExprId],
    build: &dyn Fn(&mut D, &[ExprId]) -> (ExprId, ExprId),
) -> Result<ExprId, Decline> {
    let nat = d.nat_ty();
    let fvs: Vec<u64> = args.iter().map(|_| d.fresh_fvar()).collect();
    let vars: Vec<ExprId> = fvs.iter().map(|&f| d.kernel().fvar(f)).collect();
    let (lhs, rhs) = build(d, &vars);
    let proof = prove_eq(d, rules, lhs, rhs)?;
    let mut value = proof;
    for &fv in fvs.iter().rev() {
        value = d.lam_fv(fv, nat, value);
    }
    Ok(d.apply(value, args))
}

/// Why [`theorem`] produced no declaration.
#[derive(Debug)]
pub enum SimpError {
    /// The procedure declined.
    Declined(Decline),
    /// The procedure emitted a term and the **kernel** refused it.
    Rejected(crate::KernelError),
}

impl core::fmt::Display for SimpError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Declined(d) => write!(f, "simp declined: {d:?}"),
            Self::Rejected(e) => write!(f, "kernel rejected the emitted term: {e:?}"),
        }
    }
}

/// Declare `theorem name : ∀ x₀ … x_{arity−1}, concl`, with `build`
/// returning the (unconditional) conclusion and the proof searched for and
/// emitted, never written by hand.
///
/// # Errors
///
/// [`SimpError::Declined`] when the procedure found no term, or
/// [`SimpError::Rejected`] when the kernel refused the one it found.
pub fn theorem<D: NatOps>(
    d: &mut D,
    prelude: &NatPrelude,
    rules: &[Rule<D>],
    name: NameId,
    arity: usize,
    build: &dyn Fn(&mut D, &[ExprId]) -> ExprId,
) -> Result<ExprId, SimpError> {
    let nat = d.nat_ty();
    let fvs: Vec<u64> = (0..arity).map(|_| d.fresh_fvar()).collect();
    let vars: Vec<ExprId> = fvs.iter().map(|&f| d.kernel().fvar(f)).collect();
    let concl = build(d, &vars);

    let proof = prove(d, prelude, rules, concl).map_err(SimpError::Declined)?;

    let mut ty = concl;
    let mut value = proof;
    for &fv in fvs.iter().rev() {
        ty = d.pi_fv(fv, nat, ty);
        value = d.lam_fv(fv, nat, value);
    }
    d.declare_theorem(name, ty, value)
        .map_err(SimpError::Rejected)?;
    Ok(ty)
}

/// [`theorem`], with the outcome collapsed into the prelude build's own
/// error channel so a call site can use `?` alongside the hand-written
/// declarations around it — see `ring::nat::declare`'s docs for why the
/// `UnknownConst` mapping on decline is exact rather than approximate.
///
/// # Errors
///
/// The kernel's rejection when the emitted term was refused, or
/// `UnknownConst { name }` when the search declined and no term was built.
pub fn declare<D: NatOps>(
    d: &mut D,
    prelude: &NatPrelude,
    rules: &[Rule<D>],
    name: NameId,
    arity: usize,
    build: &dyn Fn(&mut D, &[ExprId]) -> ExprId,
) -> Result<(), crate::KernelError> {
    match theorem(d, prelude, rules, name, arity, build) {
        Ok(_) => Ok(()),
        Err(SimpError::Rejected(e)) => Err(e),
        Err(SimpError::Declined(_)) => Err(crate::KernelError::UnknownConst { name }),
    }
}

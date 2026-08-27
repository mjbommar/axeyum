//! Shape-indexed retrieval over `Kernel::environment()` — *"does a declaration
//! of this shape exist, anywhere, under any name?"*
//!
//! # The deficiency this closes
//!
//! Lanes in this repository repeatedly declare themselves blocked on a lemma
//! that already exists, proved, in the tree. The most expensive measured
//! instance is `CReal.congr_of_uniformly_continuous`: a lane needed exactly it,
//! searched `creal/uniform_continuity.rs` — the module where it belongs — found
//! nothing, and stopped. It lives in `creal/integral.rs`, because
//! `riemann_sum_split_exact_of_uc` consumed it first. **The search was
//! competent and its answer was correct.** You cannot find by name a thing
//! whose name you do not know.
//!
//! Every existing instrument answers *"is this name taken?"*. This one answers
//! *"is this statement already proved?"*, by indexing what a declaration's type
//! is **made of** rather than what it is called:
//!
//! - the head constant of its conclusion (`--concl`),
//! - the head constant of each hypothesis (`--hyp`),
//! - every constant occurring anywhere in the type (`--const`),
//! - and, opt-in, every constant occurring in its checked *value* — the proof
//!   term — which is the only handle this index has on a reusable step that was
//!   built inline and never given a name (`--value-const`).
//!
//! # Why it covers every declaration kind
//!
//! `prelude_theorem_inventory` filters to [`Declaration::Theorem`], which is
//! correct for counting theorems and catastrophic for the question lanes
//! actually ask. `Nat.add`, `CReal.integral`, `Rat.polyEval` and `Complex.conj`
//! return **zero rows** from it, while a prefix grep for `Rat.polyEval` returns
//! sixteen hits that are all lemmas *about* it and none the definition. So the
//! careless query confirms presence, the careful anchored query reports
//! absence, and both are wrong about the definition. This index carries every
//! kind the environment holds and records which one each row is.
//!
//! # Names here are KERNEL names, not export names
//!
//! Rows render through `Kernel::display_name`, so the naturals are `Nat`, not
//! `AxNat`. `AxNat` is `lean_pp`'s non-shadowing *export* root and appears only
//! in exported artefacts; querying this index for `AxNat.add` is a query about
//! a constant that does not exist here, and it is answered as **unanswerable**
//! rather than as absence. `AxReal` (the axiomatized ordered field, 30 axioms)
//! and `CReal` (the constructed reals, 0) are distinct roots and are never
//! matched by substring against each other: `--concl` / `--hyp` / `--const`
//! compare whole rendered names, never prefixes.
//!
//! # Absence is a finding, and an unanswerable query is not absence
//!
//! An empty answer and a wrong question are the same observation, so this index
//! refuses to report one as the other. Before any query runs, every constant it
//! names must resolve to a declaration in the built index, the queried
//! declaration kind must be represented, and the queried namespace root must be
//! populated. If any of those fails the run is **unanswerable**
//! ([`Outcome::Unanswerable`], exit status 3), distinct from a genuine zero
//! ([`Outcome::Absent`], exit status 1) — and the positive control is therefore
//! structural rather than advisory: it is not possible to receive "0 rows" from
//! a kind, namespace or vocabulary the index does not cover.
//!
//! # What it is structurally blind to
//!
//! A reusable step built **inline** inside a larger declaration has no
//! declaration, so no index over declared names can list it. `--value-const` is
//! a partial route and not a fix: it finds the *enclosing* declaration when you
//! can guess a lemma the inline step uses. See the module-level note in
//! `examples/shape_search.rs`.

use std::collections::{BTreeMap, BTreeSet};

use crate::env::Declaration;
use crate::expr::{ExprId, ExprNode};
use crate::{Kernel, NameId};

/// Which of the environment's declaration kinds a row is.
///
/// Carried explicitly because the retrieval question is kind-sensitive: a
/// theorem is not a positive control for a definition.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum DeclKind {
    /// `axiom name : ty`
    Axiom,
    /// `def name : ty := value`
    Definition,
    /// `theorem name : ty := value`
    Theorem,
    /// `opaque name : ty := value`
    Opaque,
    /// An inductive type former.
    Inductive,
    /// A constructor of an inductive type.
    Constructor,
    /// A recursor of an inductive type.
    Recursor,
    /// A member of the privileged quotient package.
    Quot,
}

impl DeclKind {
    /// The lowercase spelling accepted by `--kind` and printed in rows.
    #[must_use]
    pub const fn label(self) -> &'static str {
        match self {
            Self::Axiom => "axiom",
            Self::Definition => "definition",
            Self::Theorem => "theorem",
            Self::Opaque => "opaque",
            Self::Inductive => "inductive",
            Self::Constructor => "constructor",
            Self::Recursor => "recursor",
            Self::Quot => "quot",
        }
    }

    /// Parse a `--kind` spelling. Unknown spellings are a usage error, never a
    /// silent empty filter.
    #[must_use]
    pub fn parse(text: &str) -> Option<Self> {
        Some(match text {
            "axiom" => Self::Axiom,
            "definition" | "def" => Self::Definition,
            "theorem" | "thm" => Self::Theorem,
            "opaque" => Self::Opaque,
            "inductive" => Self::Inductive,
            "constructor" | "ctor" => Self::Constructor,
            "recursor" | "rec" => Self::Recursor,
            "quot" => Self::Quot,
            _ => return None,
        })
    }

    /// Every kind, for the census and for `--list-kinds`.
    #[must_use]
    pub const fn all() -> [Self; 8] {
        [
            Self::Axiom,
            Self::Definition,
            Self::Theorem,
            Self::Opaque,
            Self::Inductive,
            Self::Constructor,
            Self::Recursor,
            Self::Quot,
        ]
    }

    fn of(declaration: &Declaration) -> Self {
        match declaration {
            Declaration::Axiom { .. } => Self::Axiom,
            Declaration::Definition { .. } => Self::Definition,
            Declaration::Theorem { .. } => Self::Theorem,
            Declaration::Opaque { .. } => Self::Opaque,
            Declaration::Inductive { .. } => Self::Inductive,
            Declaration::Constructor { .. } => Self::Constructor,
            Declaration::Recursor { .. } => Self::Recursor,
            Declaration::Quotient { .. } => Self::Quot,
        }
    }
}

/// One indexed declaration: what it is called, what kind it is, and what its
/// type is made of.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Entry {
    /// `Kernel::display_name` of the declaration — a KERNEL name (`Nat.add`),
    /// never a `lean_pp` export name (`AxNat.add`).
    pub name: String,
    /// Which declaration kind this row is.
    pub kind: DeclKind,
    /// Number of leading `Pi` binders in the type.
    pub arity: usize,
    /// Head constant of each `Pi` binder's type, in order, taken UNDER that
    /// binder's own telescope: a hypothesis `(k : Nat) -> CReal.le (f k) (g k)`
    /// is headed by `CReal.le`, not by `Nat`. Recording only the outermost head
    /// would file every quantified hypothesis — which is most of the
    /// interesting ones, including every domination and modulus premise — under
    /// `None`, and `--hyp CReal.le` would then miss the lemmas a lane most
    /// needs. `None` remains for a binder headed by a `Sort` or a bound
    /// variable.
    pub hyp_heads: Vec<Option<String>>,
    /// Head constant of the type's conclusion, after stripping every binder.
    pub concl_head: Option<String>,
    /// Every constant occurring anywhere in the TYPE.
    pub type_consts: BTreeSet<String>,
    /// Every constant occurring in the declaration's checked VALUE and not in
    /// its type. `None` when value indexing was not requested — which is
    /// distinct from `Some(empty)` and is why `--value-const` without
    /// `--index-values` is unanswerable rather than empty.
    pub value_consts: Option<BTreeSet<String>>,
    /// Canonical rendering of the type with binder names and universe levels
    /// erased. Two declarations sharing this string state the same proposition
    /// up to binder naming, which is what `--duplicates` reports.
    pub shape: String,
    /// The prelude groups this declaration is visible in.
    pub groups: BTreeSet<String>,
}

impl Entry {
    /// The `hyp -> hyp -> concl` sketch printed beside each match.
    #[must_use]
    pub fn signature(&self) -> String {
        let mut parts: Vec<&str> = self
            .hyp_heads
            .iter()
            .map(|head| head.as_deref().unwrap_or("_"))
            .collect();
        parts.push(self.concl_head.as_deref().unwrap_or("_"));
        parts.join(" -> ")
    }

    /// The order-insensitive shape key used by `--like`: the sorted hypothesis
    /// heads plus the conclusion head. Deliberately coarser than
    /// [`Entry::shape`] — argument ORDER is the thing a lane most often gets
    /// wrong when guessing at a lemma it has not seen.
    #[must_use]
    pub fn like_key(&self) -> String {
        let mut heads: Vec<&str> = self
            .hyp_heads
            .iter()
            .map(|head| head.as_deref().unwrap_or("_"))
            .collect();
        heads.sort_unstable();
        format!(
            "{} |= {}",
            heads.join(","),
            self.concl_head.as_deref().unwrap_or("_")
        )
    }
}

/// The built index: every declaration of every kind, across the prelude groups
/// that were built.
#[derive(Debug, Clone, Default)]
pub struct ShapeIndex {
    entries: Vec<Entry>,
    /// Every declared name, for answerability checking.
    names: BTreeSet<String>,
    /// The prelude groups covered, in build order.
    groups: Vec<String>,
    /// Whether values were indexed at all.
    values_indexed: bool,
}

impl ShapeIndex {
    /// An empty index over the named groups.
    #[must_use]
    pub fn new(groups: Vec<String>, values_indexed: bool) -> Self {
        Self {
            entries: Vec::new(),
            names: BTreeSet::new(),
            groups,
            values_indexed,
        }
    }

    /// Add one row, merging group visibility when the same declaration is
    /// reached through more than one prelude group. Preludes nest, so most
    /// declarations are visible in several.
    pub fn insert(&mut self, entry: Entry) {
        if !self.names.insert(entry.name.clone())
            && let Some(existing) = self.entries.iter_mut().find(|row| row.name == entry.name)
        {
            existing.groups.extend(entry.groups);
            return;
        }
        self.entries.push(entry);
    }

    /// Sort rows by name so output is deterministic (no hash-map order).
    pub fn finish(&mut self) {
        self.entries.sort_by(|a, b| a.name.cmp(&b.name));
    }

    /// Every indexed row.
    #[must_use]
    pub fn entries(&self) -> &[Entry] {
        &self.entries
    }

    /// The prelude groups this index covers.
    #[must_use]
    pub fn groups(&self) -> &[String] {
        &self.groups
    }

    /// Whether declaration values were indexed.
    #[must_use]
    pub const fn values_indexed(&self) -> bool {
        self.values_indexed
    }

    /// How many rows carry each declaration kind. This is the positive control
    /// printed with every negative answer.
    #[must_use]
    pub fn kind_census(&self) -> BTreeMap<DeclKind, usize> {
        let mut census = BTreeMap::new();
        for entry in &self.entries {
            *census.entry(entry.kind).or_insert(0) += 1;
        }
        census
    }

    /// How many rows sit under each top-level namespace root (`Nat`, `CReal`,
    /// `AxReal`, …). A zero here is what distinguishes "this statement is not
    /// proved" from "you did not build the package it would live in".
    #[must_use]
    pub fn namespace_census(&self) -> BTreeMap<String, usize> {
        let mut census = BTreeMap::new();
        for entry in &self.entries {
            *census
                .entry(namespace_root(&entry.name).to_owned())
                .or_insert(0) += 1;
        }
        census
    }

    /// Whether a name is declared in this index.
    #[must_use]
    pub fn declares(&self, name: &str) -> bool {
        self.names.contains(name)
    }

    /// Declared names containing `name`'s last dotted component — the "did you
    /// mean" list printed with an unanswerable vocabulary error.
    #[must_use]
    pub fn nearest(&self, name: &str, limit: usize) -> Vec<String> {
        let needle = spelling_insensitive(name.rsplit('.').next().unwrap_or(name));
        if needle.is_empty() {
            return Vec::new();
        }
        self.names
            .iter()
            .filter(|candidate| spelling_insensitive(candidate).contains(&needle))
            .take(limit)
            .cloned()
            .collect()
    }

    /// Groups of two or more declarations whose types are identical up to
    /// binder naming. A duplicate is worse than a delay: it leaves two proofs
    /// of one fact that must stay in sync while the kernel happily verifies
    /// both.
    #[must_use]
    pub fn duplicate_shapes(&self) -> Vec<Vec<&Entry>> {
        self.duplicate_shapes_where(|entry| entry.kind == DeclKind::Theorem)
    }

    /// [`ShapeIndex::duplicate_shapes`] over the rows `keep` accepts.
    ///
    /// The default restriction to theorems is not cosmetic. For a DEFINITION
    /// the type is not the statement — `Nat.add` and `Nat.mul` are both
    /// `Nat -> Nat -> Nat` and are not duplicates of each other — so an
    /// unrestricted scan is dominated by rows that share an arity and nothing
    /// else. Measured over the constructed library on 2026-08-27: 67 groups
    /// unrestricted against 6 for theorems alone, and only the second set
    /// contains anything a lane should act on. A theorem duplicating a
    /// CONSTRUCTOR is a real duplicate this default hides — pass
    /// `--kind theorem --kind constructor` to see those too.
    #[must_use]
    pub fn duplicate_shapes_where(&self, keep: impl Fn(&Entry) -> bool) -> Vec<Vec<&Entry>> {
        let mut by_shape: BTreeMap<&str, Vec<&Entry>> = BTreeMap::new();
        for entry in self.entries.iter().filter(|entry| keep(entry)) {
            by_shape
                .entry(entry.shape.as_str())
                .or_default()
                .push(entry);
        }
        by_shape
            .into_values()
            .filter(|group| group.len() > 1)
            .collect()
    }
}

/// The first dotted component of a rendered name (`CReal.foo.bar` -> `CReal`).
#[must_use]
pub fn namespace_root(name: &str) -> &str {
    name.split('.').next().unwrap_or(name)
}

/// A name with its SPELLING removed: lowercased, with `_` and `.` dropped.
///
/// This repository has no single naming convention and cannot be searched as if
/// it did. Measured 2026-08-27 over the 464 `CReal` declarations in the built
/// environment: 315 contain an underscore, 200 contain an internal capital, and
/// **114 contain both** — `CReal.equiv_of_le_le` sits beside
/// `CReal.congrOfUniformlyContinuous`, and `CReal.abs_sumRange_le` mixes the two
/// inside one name. The Rust FIELD for the second is
/// `congr_of_uniformly_continuous`, which is also the spelling every design
/// document and brief uses, so a lane grepping the kernel inventory for it gets
/// zero rows for a declaration that exists.
///
/// Normalising both sides makes `--name-like congr_of_uniformly_continuous`
/// retrieve `CReal.congrOfUniformlyContinuous`, and is what the nearest-name
/// hint matches on.
#[must_use]
pub fn spelling_insensitive(name: &str) -> String {
    name.chars()
        .filter(|character| *character != '_' && *character != '.')
        .flat_map(char::to_lowercase)
        .collect()
}

/// A retrieval query. Every populated field is a conjunct.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Query {
    /// Head constant of the conclusion must equal this.
    pub concl: Option<String>,
    /// Each of these must head a DISTINCT hypothesis binder.
    pub hyps: Vec<String>,
    /// Each must occur somewhere in the type.
    pub consts: Vec<String>,
    /// Each must occur in the declaration's value.
    pub value_consts: Vec<String>,
    /// Exact rendered name.
    pub name: Option<String>,
    /// Substring of the rendered name.
    pub name_contains: Option<String>,
    /// Substring of the rendered name after [`spelling_insensitive`] on both
    /// sides, so a `snake_case` guess retrieves a `camelCase` declaration.
    pub name_like: Option<String>,
    /// Restrict to these kinds (empty = every kind).
    pub kinds: Vec<DeclKind>,
    /// Restrict to this namespace root.
    pub namespace: Option<String>,
    /// Exact binder count.
    pub arity: Option<usize>,
    /// Shape-alike of an existing declaration.
    pub like: Option<String>,
}

impl Query {
    /// Whether this query constrains anything at all. An unconstrained query
    /// would match the whole index and answer "yes" to every question.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.concl.is_none()
            && self.hyps.is_empty()
            && self.consts.is_empty()
            && self.value_consts.is_empty()
            && self.name.is_none()
            && self.name_contains.is_none()
            && self.name_like.is_none()
            && self.kinds.is_empty()
            && self.namespace.is_none()
            && self.arity.is_none()
            && self.like.is_none()
    }

    /// Every constant name this query asserts exists. Each must resolve in the
    /// index or the run is unanswerable.
    #[must_use]
    pub fn vocabulary(&self) -> Vec<String> {
        let mut vocabulary = Vec::new();
        vocabulary.extend(self.concl.clone());
        vocabulary.extend(self.hyps.iter().cloned());
        vocabulary.extend(self.consts.iter().cloned());
        vocabulary.extend(self.value_consts.iter().cloned());
        vocabulary.extend(self.like.clone());
        vocabulary
    }

    fn matches(&self, entry: &Entry, like_key: Option<&str>) -> bool {
        if let Some(concl) = &self.concl
            && entry.concl_head.as_deref() != Some(concl.as_str())
        {
            return false;
        }
        // A repeated `--hyp X` demands X heading that many DISTINCT binders.
        let mut available: Vec<&str> = entry
            .hyp_heads
            .iter()
            .filter_map(|head| head.as_deref())
            .collect();
        for wanted in &self.hyps {
            match available.iter().position(|head| *head == wanted.as_str()) {
                Some(position) => {
                    available.swap_remove(position);
                }
                None => return false,
            }
        }
        for wanted in &self.consts {
            if !entry.type_consts.contains(wanted) {
                return false;
            }
        }
        if !self.value_consts.is_empty() {
            let Some(values) = &entry.value_consts else {
                return false;
            };
            for wanted in &self.value_consts {
                if !values.contains(wanted) {
                    return false;
                }
            }
        }
        if let Some(name) = &self.name
            && &entry.name != name
        {
            return false;
        }
        if let Some(fragment) = &self.name_contains
            && !entry.name.contains(fragment.as_str())
        {
            return false;
        }
        if let Some(fragment) = &self.name_like
            && !spelling_insensitive(&entry.name).contains(&spelling_insensitive(fragment))
        {
            return false;
        }
        if !self.kinds.is_empty() && !self.kinds.contains(&entry.kind) {
            return false;
        }
        if let Some(namespace) = &self.namespace
            && namespace_root(&entry.name) != namespace
        {
            return false;
        }
        if let Some(arity) = self.arity
            && entry.arity != arity
        {
            return false;
        }
        if let Some(key) = like_key
            && entry.like_key() != key
        {
            return false;
        }
        true
    }
}

/// What a query run concluded. The three cases are deliberately distinct: a
/// tool that cannot tell "absent" from "I was never pointed at your subject"
/// manufactures negative results.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Outcome {
    /// At least one row matched; the matching names, in index order.
    Found(Vec<String>),
    /// The query was answerable and nothing matched.
    Absent,
    /// The query could not be answered; each string is a reason.
    Unanswerable(Vec<String>),
}

impl Outcome {
    /// The process exit status this outcome maps to: 0 found, 1 absent,
    /// 3 unanswerable. `--expect-absent` inverts the first two; nothing
    /// inverts 3.
    #[must_use]
    pub const fn status(&self) -> u8 {
        match self {
            Self::Found(_) => 0,
            Self::Absent => 1,
            Self::Unanswerable(_) => 3,
        }
    }
}

/// Run `query` against `index`.
///
/// Answerability is checked FIRST and unconditionally: a query naming a
/// constant, kind or namespace the index does not carry is never answered with
/// a row count.
#[must_use]
pub fn run(index: &ShapeIndex, query: &Query) -> Outcome {
    let mut reasons = Vec::new();

    if index.entries().is_empty() {
        reasons.push("the index is empty: no prelude group was built".to_owned());
    }
    if query.is_empty() {
        reasons.push(
            "the query constrains nothing, so every declaration would match and no \
             absence could ever be reported"
                .to_owned(),
        );
    }
    if !query.value_consts.is_empty() && !index.values_indexed() {
        reasons.push(
            "--value-const needs --index-values; without it every declaration's value \
             is unread and the answer would be a vacuous zero"
                .to_owned(),
        );
    }
    for wanted in query.vocabulary() {
        if !index.declares(&wanted) {
            let nearest = index.nearest(&wanted, 6);
            let hint = if nearest.is_empty() {
                String::from("no declared name contains that component")
            } else {
                format!("nearest declared: {}", nearest.join(", "))
            };
            reasons.push(format!(
                "no declaration is named {wanted:?} in the built index, so a query \
                 mentioning it cannot distinguish absence from a typo or an unbuilt \
                 package ({hint})"
            ));
        }
    }
    let kinds = index.kind_census();
    for kind in &query.kinds {
        if kinds.get(kind).copied().unwrap_or(0) == 0 {
            reasons.push(format!(
                "the index carries zero {} declarations, so it cannot report the \
                 absence of one",
                kind.label()
            ));
        }
    }
    let namespaces = index.namespace_census();
    let mut roots: Vec<String> = query.namespace.clone().into_iter().collect();
    if let Some(name) = &query.name {
        roots.push(namespace_root(name).to_owned());
    }
    for root in roots {
        if namespaces.get(&root).copied().unwrap_or(0) == 0 {
            // The hint matters most for the export-name trap: `AxNat.add` is
            // `lean_pp`'s rendering and the kernel name is `Nat.add`, so the
            // nearest list turns an unanswerable query into a fixed one.
            let nearest = query
                .name
                .as_ref()
                .map(|name| index.nearest(name, 6))
                .unwrap_or_default();
            let hint = if nearest.is_empty() {
                String::new()
            } else {
                format!(" (nearest declared: {})", nearest.join(", "))
            };
            reasons.push(format!(
                "the index carries zero declarations under namespace {root:?}; build \
                 the package that owns it before reading a zero as absence{hint}"
            ));
        }
    }

    if !reasons.is_empty() {
        return Outcome::Unanswerable(reasons);
    }

    let like_key = query.like.as_ref().and_then(|name| {
        index
            .entries()
            .iter()
            .find(|entry| &entry.name == name)
            .map(Entry::like_key)
    });
    let matched: Vec<String> = index
        .entries()
        .iter()
        .filter(|entry| query.matches(entry, like_key.as_deref()))
        .map(|entry| entry.name.clone())
        .collect();

    if matched.is_empty() {
        Outcome::Absent
    } else {
        Outcome::Found(matched)
    }
}

// ---------------------------------------------------------------------------
// Extraction from a built kernel
// ---------------------------------------------------------------------------

/// Strip leading `Pi` binders, returning each binder's type and the conclusion.
fn telescope(kernel: &Kernel, ty: ExprId) -> (Vec<ExprId>, ExprId) {
    let mut binders = Vec::new();
    let mut current = ty;
    // Bounded so a pathological type cannot spin: no kernel declaration here
    // has a telescope anywhere near this long.
    for _ in 0..4096 {
        match kernel.expr_node(current) {
            ExprNode::Pi(_, domain, body, _) => {
                binders.push(*domain);
                current = *body;
            }
            _ => break,
        }
    }
    (binders, current)
}

/// The head constant of an application spine, if it has one.
fn head_const(kernel: &Kernel, expr: ExprId) -> Option<NameId> {
    let mut current = expr;
    loop {
        match kernel.expr_node(current) {
            ExprNode::App(function, _) => current = *function,
            ExprNode::Const(name, _) => return Some(*name),
            _ => return None,
        }
    }
}

/// A canonical string for `expr` with binder names, binder info and universe
/// levels erased, so two statements differing only in what their variables are
/// called produce the same key.
fn shape_of(kernel: &Kernel, expr: ExprId, out: &mut String) {
    use std::fmt::Write as _;
    match kernel.expr_node(expr) {
        ExprNode::BVar(index) => {
            let _ = write!(out, "#{index}");
        }
        ExprNode::FVar(id) => {
            let _ = write!(out, "f{id}");
        }
        ExprNode::Sort(_) => out.push('S'),
        ExprNode::Const(name, _) => {
            out.push('c');
            let _ = write!(out, "{}", kernel.display_name(*name));
        }
        ExprNode::Proj(name, field, value) => {
            let _ = write!(out, "(J{} {field} ", kernel.display_name(*name));
            shape_of(kernel, *value, out);
            out.push(')');
        }
        ExprNode::App(function, argument) => {
            out.push('(');
            shape_of(kernel, *function, out);
            out.push(' ');
            shape_of(kernel, *argument, out);
            out.push(')');
        }
        ExprNode::Lam(_, domain, body, _) => {
            out.push_str("(L ");
            shape_of(kernel, *domain, out);
            out.push(' ');
            shape_of(kernel, *body, out);
            out.push(')');
        }
        ExprNode::Pi(_, domain, body, _) => {
            out.push_str("(P ");
            shape_of(kernel, *domain, out);
            out.push(' ');
            shape_of(kernel, *body, out);
            out.push(')');
        }
        ExprNode::Let(_, ty, value, body) => {
            out.push_str("(T ");
            shape_of(kernel, *ty, out);
            out.push(' ');
            shape_of(kernel, *value, out);
            out.push(' ');
            shape_of(kernel, *body, out);
            out.push(')');
        }
        ExprNode::Lit(literal) => {
            let _ = write!(out, "K{literal:?}");
        }
    }
}

/// Index every declaration in `kernel`'s environment under the label `group`.
///
/// `index_values` controls whether the checked proof/definition VALUE is read
/// as well as the type. It is opt-in because reading values walks proof terms
/// that are orders of magnitude larger than the statements they prove.
pub fn index_kernel(kernel: &Kernel, group: &str, index: &mut ShapeIndex, index_values: bool) {
    for (_, declaration) in kernel.environment().iter() {
        let name = declaration.name();
        let ty = declaration.ty();
        let (binders, conclusion) = telescope(kernel, ty);
        let hyp_heads = binders
            .iter()
            .map(|&domain| {
                let (_, inner) = telescope(kernel, domain);
                head_const(kernel, inner).map(|head| kernel.display_name(head).to_string())
            })
            .collect();
        let concl_head =
            head_const(kernel, conclusion).map(|head| kernel.display_name(head).to_string());
        let type_consts: BTreeSet<String> = kernel
            .declaration_type_dependencies(name)
            .into_iter()
            .map(|dependency| kernel.display_name(dependency).to_string())
            .collect();
        let value_consts = if index_values {
            let mut all: BTreeSet<String> = kernel
                .declaration_dependencies(name)
                .into_iter()
                .map(|dependency| kernel.display_name(dependency).to_string())
                .collect();
            all.retain(|constant| !type_consts.contains(constant));
            Some(all)
        } else {
            None
        };
        let mut shape = String::new();
        shape_of(kernel, ty, &mut shape);
        index.insert(Entry {
            name: kernel.display_name(name).to_string(),
            kind: DeclKind::of(declaration),
            arity: binders.len(),
            hyp_heads,
            concl_head,
            type_consts,
            value_consts,
            shape,
            groups: [group.to_owned()].into_iter().collect(),
        });
    }
}

#[cfg(test)]
mod shape_index_tests;

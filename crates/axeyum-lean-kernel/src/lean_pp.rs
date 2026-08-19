//! Render kernel terms to Lean 4 source syntax — a readable, *human-inspectable*
//! projection of the in-tree kernel's `Expr`/`Name`/`Level`.
//!
//! It renders proof *terms* (the trusted-checking witnesses produced by
//! `axeyum-solver`'s reconstruction) so that a refutation the in-tree
//! [`Kernel`](crate::Kernel) accepts can be read and diffed. It is pure
//! pretty-printing — it never affects type checking.
//!
//! # This output is NOT an external re-checking route
//!
//! Do not read the rendered module as evidence that an independent kernel would
//! accept the term. Measured on 2026-08-13 against the pinned toolchain
//! (`lean-toolchain`, Lean 4.30.0): the Rado shell-bound module rendered by this
//! writer is **rejected by `lean` in 0.175 s with 22 errors**. Three causes,
//! only one of which is cosmetic:
//!
//! * recursor-based `def`s fail codegen and would need `noncomputable`;
//! * the self-reference in an inductive's own constructor is emitted with
//!   explicit universe arguments (`Eq.{u}` inside `Eq`), which Lean rejects,
//!   and the cascade accounts for 19 of the 22 errors;
//! * inductives are declared with every argument as an *index* while the
//!   emitted `Eq.rec` applications assume *parameters*. The in-tree kernel
//!   generates a recursor consistent with its own declaration form and so
//!   accepts the module; Lean generates a different recursor and does not.
//!
//! Even with all three repaired, `lean file.lean` runs the **elaborator**, not
//! the kernel — it re-infers implicit arguments and universes and reaches for
//! coercions, none of which bear on whether the proof term is well-typed.
//!
//! The external re-checking route is the official `lean4export` format, which
//! `axeyum-lean-import` already consumes fail-closed at version 3.1.0; emitting
//! it makes the round-trip through our own importer a differential test and
//! lets `leanchecker` (shipped in the pinned toolchain) check the terms. Until
//! that writer exists, this module's output is for people, not for kernels.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt::Write as _;

use crate::{Declaration, ExprId, ExprNode, Kernel, LevelId, LevelNode, Lit, NameId, NameNode};

const COMPACT_SHARE_MIN_TREE_NODES: u64 = 8;
const COMPACT_CHUNK_TREE_NODES: u64 = 512;

/// The identity of a **binder scope**: a hash chain folded over the chain of
/// binder occurrences enclosing a position in the rendered term.
///
/// A hash-consed proof DAG is printed as a *tree*, and that is where a
/// self-contained module's size goes: measured 2026-08-18 on the constructed
/// reals, `CReal.mul_assoc` is 1,296 kernel nodes and 324,609 printed ones.
/// Sharing repeated nodes fixes that, but only **closed** nodes could be
/// shared, and a proof body is mostly open — every subterm under a `fun` has
/// loose de Bruijn variables. Hoisting those is not merely awkward, it is
/// wrong in general: two occurrences of one node under two different binders
/// denote two different terms.
///
/// A scope id is exactly the condition that makes it right. Two occurrences
/// carrying the same id sit under the same chain of binder *occurrences*, so
/// their loose variables denote the same binders and one `let` may serve both;
/// occurrences under different binders get different ids and are never
/// conflated. The chain is folded from the binder nodes themselves, so it is
/// deterministic — module text is a public API promise.
type ScopeId = u64;

/// The scope at a declaration's own top level. No binder is open there, so
/// every node keyed at `ROOT_SCOPE` is closed and one binding serves all of
/// its occurrences.
const ROOT_SCOPE: ScopeId = 0;

/// Extend a scope by one binder occurrence.
fn scope_child(scope: ScopeId, binder: ExprId) -> ScopeId {
    let mixed = scope
        .rotate_left(17)
        .wrapping_mul(0x9E37_79B9_7F4A_7C15)
        .wrapping_add(u64::from(binder.0).wrapping_add(1));
    let mixed = mixed ^ (mixed >> 29);
    // `0` is reserved for the root, so a child scope must never collide with
    // it: a child that hashed to `ROOT_SCOPE` would let an open node be keyed
    // as if it were closed.
    if mixed == ROOT_SCOPE { 1 } else { mixed }
}

/// A share key: the node, plus the scope its loose variables are read in.
/// Closed nodes are normalized to [`ROOT_SCOPE`].
type ShareKey = (ExprId, ScopeId);

#[derive(Debug, Default)]
struct LeanSharePlan {
    names: BTreeMap<ShareKey, String>,
    /// Keys hoisted to **top-level `def`s**. Always closed, so always keyed at
    /// [`ROOT_SCOPE`].
    order: Vec<ExprId>,
    /// Keys hoisted to a `let` at the top of the body a binder opens, indexed
    /// by that body's scope and held in dependency order.
    blocks: BTreeMap<ScopeId, Vec<ShareKey>>,
}

/// The share map plus *where* rendering currently is: which scope, and which
/// key (if any) is being expanded rather than referenced by name.
#[derive(Clone, Copy)]
struct ShareView<'a> {
    names: &'a BTreeMap<ShareKey, String>,
    blocks: &'a BTreeMap<ScopeId, Vec<ShareKey>>,
    scope: ScopeId,
    expand: Option<ShareKey>,
}

impl<'a> ShareView<'a> {
    fn new(plan: &'a LeanSharePlan) -> Self {
        Self {
            names: &plan.names,
            blocks: &plan.blocks,
            scope: ROOT_SCOPE,
            expand: None,
        }
    }

    /// The name standing for `expression` here, if one does.
    ///
    /// A node is looked up at the current scope first and at [`ROOT_SCOPE`]
    /// second. The second lookup is what shares closed nodes across scopes;
    /// it cannot capture an open one, because the planner keys a node at
    /// `ROOT_SCOPE` only when it has no loose variables.
    fn lookup(&self, expression: ExprId) -> Option<&'a str> {
        for key in [(expression, self.scope), (expression, ROOT_SCOPE)] {
            if self.expand == Some(key) {
                return None;
            }
            if let Some(name) = self.names.get(&key) {
                return Some(name.as_str());
            }
        }
        None
    }

    /// Move into a binder body's scope (a fresh position, so nothing is being
    /// expanded there).
    fn at(self, scope: ScopeId) -> Self {
        Self {
            scope,
            expand: None,
            ..self
        }
    }

    /// Render `key`'s definition rather than a reference to it.
    fn expanding(self, key: ShareKey) -> Self {
        Self {
            scope: key.1,
            expand: Some(key),
            ..self
        }
    }
}

trait LeanModuleOutput: std::fmt::Write {
    fn append_owned(&mut self, text: String);
}

impl LeanModuleOutput for String {
    fn append_owned(&mut self, text: String) {
        self.push_str(&text);
    }
}

/// A **shared prelude module**: the development a family of query modules cites,
/// emitted once as its own Lean module instead of inlined into every one of
/// them.
///
/// # Why this exists
///
/// A refutation over the constructed reals inlines the whole ℕ/ℤ/ℚ/setoid
/// development with every proof body. Measured 2026-08-18 on the shipped front
/// door: the emitted module is 1,304,276 bytes, of which **the refutation's own
/// theorem term is 4,193** — 0.16%. The other 99.84% is identical for every
/// query over the same carrier. Emitting it once and `import`ing it takes the
/// per-query module to single-digit kilobytes.
///
/// # What a third party has to do
///
/// This is a strictly weaker artefact than the self-contained module it
/// replaces, and the difference is worth stating rather than hiding behind the
/// byte count: a single file is checked by `lean Query.lean` and nothing else,
/// whereas the split needs the prelude compiled first and found on `LEAN_PATH`.
///
/// ```text
/// lean -o <dir>/<Name>.olean <dir>/<Name>.lean
/// LEAN_PATH=<dir> lean <dir>/Query.lean
/// ```
///
/// [`Self::check_script`] emits exactly those two lines for a given directory,
/// so the recipe is generated from the artefact rather than copied from prose.
/// `#print axioms` traverses imported proofs, so the axiom-freedom claim is
/// unchanged — the query module's `#print axioms` reports the same footprint it
/// reported when the development was inlined.
#[derive(Clone, Debug)]
pub struct LeanPreludeModule {
    name: String,
    source: String,
    provided: BTreeSet<NameId>,
}

impl LeanPreludeModule {
    /// The Lean module name a query module `import`s. This must also be the
    /// artefact's file stem: Lean resolves `import Foo.Bar` to `Foo/Bar.olean`
    /// under a `LEAN_PATH` entry.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The module source.
    #[must_use]
    pub fn source(&self) -> &str {
        &self.source
    }

    /// The file name this module must be written to for `import` to resolve.
    #[must_use]
    pub fn file_name(&self) -> String {
        format!("{}.lean", self.name.replace('.', "/"))
    }

    /// The declaration names this module supplies — what a query module must
    /// **not** re-declare.
    #[must_use]
    pub fn provided(&self) -> &BTreeSet<NameId> {
        &self.provided
    }

    /// How many declarations this module supplies.
    #[must_use]
    pub fn provided_len(&self) -> usize {
        self.provided.len()
    }

    /// The two commands a third party runs to check a query module against this
    /// prelude, given the directory both files were written to. Generated from
    /// the artefact so the recipe cannot drift from the module name.
    ///
    /// `--root` is not optional. Lean derives a file's module name from its path
    /// relative to the root directory, which defaults to the working directory,
    /// so without it `lean -o /tmp/x/M.olean /tmp/x/M.lean` run from anywhere
    /// else fails with `input file ... must be contained in root directory`.
    #[must_use]
    pub fn check_script(&self, directory: &str, query_file: &str) -> String {
        format!(
            "lean --root {directory} -o {directory}/{name}.olean {directory}/{name}.lean\n\
             LEAN_PATH={directory} lean --root {directory} {directory}/{query_file}\n",
            name = self.name
        )
    }
}

/// Which of the three module shapes a banner opens.
///
/// The three differ only in their header comment, whether an `import` line
/// follows `prelude`, and whether they declare Lean's compiler-internal
/// constants -- which must appear exactly once across a module set.
#[derive(Clone, Copy)]
enum BannerKind<'a> {
    /// One file that declares everything it cites (the historical shape, and
    /// still what the shipped front door emits).
    SelfContained,
    /// The shared development a family of query modules imports.
    SharedPrelude,
    /// A query module whose shared development is `import`ed by module name.
    Importing(&'a str),
}

/// The exact fixed preamble a **self-contained** module opens with — every byte
/// [`Kernel::render_lean_module`] writes before the first declaration.
///
/// Public because the banner is *shared text under many pins*, and that is the
/// shape of a recurring defect rather than a convenience. `b760fd6ae` (+863
/// bytes, the codegen constants) and `46724faec` (+777 bytes, `maxRecDepth`)
/// each added banner text and re-pinned only the golden module that happened to
/// sit in a gate; the same +1,640 landed unannounced on four others and `main`
/// was red for a day. That was the third recurrence.
///
/// With the banner nameable, a byte pin over a rendered module can pin the part
/// the producer of a *proof* change actually owns — see [`split_module_banner`],
/// which is what the golden suites assert against. The banner keeps its own pin,
/// in one place, where a header diff is read and waved through deliberately.
#[must_use]
pub fn self_contained_module_banner() -> String {
    let mut out = String::new();
    Kernel::write_module_banner(&mut out, BannerKind::SelfContained);
    out
}

/// The preamble of the **shared development** a family of query modules imports
/// ([`Kernel::render_lean_prelude_module`]). See [`self_contained_module_banner`].
#[must_use]
pub fn shared_prelude_module_banner() -> String {
    let mut out = String::new();
    Kernel::write_module_banner(&mut out, BannerKind::SharedPrelude);
    out
}

/// The preamble of a **query** module that `import`s `module`
/// ([`Kernel::render_lean_module_compact_importing`]). It omits the
/// compiler-internal constants, which the imported module already declares.
/// See [`self_contained_module_banner`].
#[must_use]
pub fn importing_module_banner(module: &str) -> String {
    let mut out = String::new();
    Kernel::write_module_banner(&mut out, BannerKind::Importing(module));
    out
}

/// Split a rendered Lean module into `(banner, body)`.
///
/// Returns `None` when `source` does not begin with a banner **this** kernel
/// emits — a mangled, hand-edited, or foreign module is not silently accepted as
/// a body-only pin, so the banner is still checked byte for byte on every use.
///
/// The shape is read from the source itself: an `import` line inside the
/// preamble names the shared development, and the two unimported shapes are
/// distinguished by trying each. Deliberately not a `starts_with("--")` scan or
/// a search for the last banner line: those would let banner text drift into the
/// "body" half and re-create the very coupling this exists to break.
#[must_use]
pub fn split_module_banner(source: &str) -> Option<(&str, &str)> {
    // The `import` line is written inside the preamble, before any declaration,
    // so a hit in the first handful of lines is the banner's own.
    let imported = source
        .lines()
        .take(16)
        .find_map(|line| line.strip_prefix("import "))
        .map(str::trim);
    let candidates = match imported {
        Some(module) => vec![importing_module_banner(module)],
        None => vec![
            self_contained_module_banner(),
            shared_prelude_module_banner(),
        ],
    };
    candidates.iter().find_map(|banner| {
        source
            .strip_prefix(banner.as_str())
            .map(|body| (&source[..banner.len()], body))
    })
}

struct IoLeanModuleOutput<'a, W: std::io::Write + ?Sized> {
    writer: &'a mut W,
    error: Option<std::io::Error>,
}

impl<W: std::io::Write + ?Sized> IoLeanModuleOutput<'_, W> {
    fn write(&mut self, text: &[u8]) {
        if self.error.is_none()
            && let Err(error) = self.writer.write_all(text)
        {
            self.error = Some(error);
        }
    }
}

impl<W: std::io::Write + ?Sized> std::fmt::Write for IoLeanModuleOutput<'_, W> {
    fn write_str(&mut self, text: &str) -> std::fmt::Result {
        self.write(text.as_bytes());
        Ok(())
    }
}

impl<W: std::io::Write + ?Sized> LeanModuleOutput for IoLeanModuleOutput<'_, W> {
    fn append_owned(&mut self, text: String) {
        self.write(text.as_bytes());
    }
}

impl Kernel {
    /// Render `expr` as a Lean 4 source string. De Bruijn variables are resolved to
    /// their binder names (anonymous binders get generated `x<depth>` names); the
    /// output is parenthesized enough to re-parse with Lean's standard precedence.
    #[must_use]
    pub fn render_lean(&self, expr: ExprId) -> String {
        let mut binders: Vec<String> = Vec::new();
        self.render_expr(
            expr,
            &mut binders,
            &std::collections::BTreeSet::new(),
            &std::collections::BTreeSet::new(),
        )
    }

    /// Whether [`Declaration::Theorem`] renders with the `def` keyword rather
    /// than `theorem` (ADR-0489). Off unless [`Self::set_render_proofs_as_def`]
    /// turned it on.
    #[must_use]
    pub const fn render_proofs_as_def(&self) -> bool {
        self.render_proofs_as_def
    }

    /// Render every environment [`Declaration::Theorem`] with the `def` keyword.
    ///
    /// **This changes only the keyword.** No term, no type, no binder, no share
    /// name and no module banner moves; the emitted bytes differ from the
    /// default rendering exactly by the prefix of the lines that open a theorem.
    /// The module's *root* `theorem <name> : <goal> := <proof>` is deliberately
    /// NOT affected — nothing reduces through the root, so re-spelling it would
    /// cost honesty and buy nothing.
    ///
    /// # Why the option exists
    ///
    /// Lean has two checkers and they disagree about a proof's opacity
    /// (ADR-0488). Lean's *kernel* unfolds anything carrying a value and accepts
    /// the whole constructed-real carrier; Lean's *elaborator* refuses to unfold
    /// a `theorem` while reducing, so a declaration whose type-checking must
    /// compute through `Nat.gcd` — whose Euclidean descent is justified by the
    /// theorem `Nat.mod_lt` — is refused from `.lean` source. Spelling proofs as
    /// `def` removes that opacity and the elaborator accepts them too.
    ///
    /// It is off by default because a `def` is a weaker statement about the
    /// artefact than a `theorem` is, and because it costs elaboration time; the
    /// numbers and the recommendation are in ADR-0489.
    pub fn set_render_proofs_as_def(&mut self, render_as_def: bool) {
        self.render_proofs_as_def = render_as_def;
    }

    /// The keyword that opens an environment theorem: `theorem`, or `def` under
    /// [`Self::set_render_proofs_as_def`].
    const fn proof_keyword(&self) -> &'static str {
        if self.render_proofs_as_def {
            "def"
        } else {
            "theorem"
        }
    }

    /// Render a [`Declaration`] as a Lean 4 top-level command. The directly-emittable
    /// kinds (`axiom`/`def`/`theorem`/`opaque`) render verbatim; an
    /// `Inductive`/`Constructor`/`Recursor` renders as a comment, since Lean
    /// regenerates those from a single `inductive` command (a later export slice).
    #[must_use]
    pub fn render_lean_decl(&self, decl: &Declaration) -> String {
        match decl {
            Declaration::Axiom { name, uparams, ty } => format!(
                "axiom {}{} : {}",
                self.render_name(*name),
                self.render_uparams(uparams),
                self.render_lean(*ty)
            ),
            Declaration::Definition {
                name,
                uparams,
                ty,
                value,
                ..
            } => format!(
                "def {}{} : {} :=\n  {}",
                self.render_name(*name),
                self.render_uparams(uparams),
                self.render_lean(*ty),
                self.render_lean(*value)
            ),
            Declaration::Theorem {
                name,
                uparams,
                ty,
                value,
            } => format!(
                "{} {}{} : {} :=\n  {}",
                self.proof_keyword(),
                self.render_name(*name),
                self.render_uparams(uparams),
                self.render_lean(*ty),
                self.render_lean(*value)
            ),
            Declaration::Opaque {
                name,
                uparams,
                ty,
                value,
            } => format!(
                "opaque {}{} : {} :=\n  {}",
                self.render_name(*name),
                self.render_uparams(uparams),
                self.render_lean(*ty),
                self.render_lean(*value)
            ),
            Declaration::Inductive { name, .. }
            | Declaration::Constructor { name, .. }
            | Declaration::Recursor { name, .. } => format!(
                "-- `{}` is regenerated by Lean's `inductive` command (export slice TODO)",
                self.render_name(*name)
            ),
            Declaration::Quotient { name, .. } => format!(
                "-- `{}` is provided by Lean's built-in quotient package",
                self.render_name(*name)
            ),
        }
    }

    /// Render a **self-contained Lean 4 module** that re-checks a reconstructed
    /// refutation: every environment declaration reachable from `goal`/`proof`,
    /// in dependency order, followed by `theorem <theorem_name> : <goal> := <proof>`
    /// and a `#print axioms <theorem_name>` audit command.
    ///
    /// The module opens with `prelude` (no `import Init`), so the re-declared
    /// logical constants (`True`/`False`/`And`/`Eq`/…) do not clash with Lean's
    /// core: it is checked against *axeyum's own* declarations, exactly the
    /// obligation the in-tree [`Kernel`] discharged. Inductives, their
    /// constructors, and their generated recursors are emitted as `axiom`s carrying
    /// the kernel's stored types (so Lean re-checks the proof term against those
    /// signatures); definitions/theorems/opaques and the uninterpreted/`em` axioms
    /// render verbatim. A real `lean` binary that accepts this module — and reports
    /// (via `#print axioms`) only the expected uninterpreted/`em`/`propext`-class
    /// axioms — independently confirms the refutation.
    ///
    /// `theorem_name` must be a valid Lean identifier (e.g. `axeyum_refutation`).
    #[must_use]
    pub fn render_lean_module(&self, theorem_name: &str, goal: ExprId, proof: ExprId) -> String {
        self.render_lean_module_with_inductives(theorem_name, goal, proof, &[])
    }

    /// Render a self-contained module while preserving repeated **closed** proof
    /// DAG nodes as deterministic top-level definitions and bounding single-use
    /// closed regions with serialization chunks.
    ///
    /// This is semantically equivalent to [`Self::render_lean_module`], but can
    /// be substantially smaller for hash-consed proofs whose ordinary source
    /// rendering expands shared subterms as a tree. Expressions containing loose
    /// de Bruijn variables or free variables are never hoisted.
    #[must_use]
    pub fn render_lean_module_compact(
        &self,
        theorem_name: &str,
        goal: ExprId,
        proof: ExprId,
    ) -> String {
        self.render_lean_module_compact_with_inductives(theorem_name, goal, proof, &[])
    }

    /// Like [`Self::render_lean_module`], but renders each inductive named in
    /// `real_inductives` as a **real Lean `inductive` command** (so Lean
    /// regenerates its constructors and recursor, *with* their ι-reduction rules),
    /// instead of opaque `axiom`s. The auto-generated constructor/recursor
    /// declarations of those inductives are then **skipped** (Lean provides them).
    ///
    /// This is required when the reconstructed proof relies on **Lean-side
    /// ι-reduction** of a custom inductive's recursor — e.g. the `QF_DT` is-tester
    /// fold `is_C (C x) ≡ Bool.true`, whose `Eq.refl` proof only type-checks if
    /// Lean can compute the recursor application. Inductives *not* listed keep the
    /// axiom rendering byte-for-byte (so the logical-prelude connectives — whose
    /// proofs never need their recursors to *compute* in Lean — are unchanged).
    ///
    /// Parametric and indexed inductives are emitted with their parameter
    /// telescope **before** the colon and their indices after it, matching Lean's
    /// own `inductive I (p : P) : Idx -> Sort u` form, so Lean regenerates the
    /// same recursor the in-tree kernel generated. A listed inductive whose shape
    /// this writer cannot express — a member of a **mutual** group, or a
    /// declaration whose stored type does not open `num_params` parameter binders
    /// — falls back to the axiom rendering.
    ///
    /// Until 2026-08-13 this comment claimed a flatness guard that the writer
    /// never implemented: a parametric/indexed
    /// inductive was rendered with its whole telescope after the colon (so every
    /// parameter became an *index*) and Lean then generated a different recursor
    /// and rejected every application. The cross-check corpus could not reach the
    /// defect because every fixture inductive is a flat enum
    /// (`add_inductive(two, &[], 0, …)`).
    ///
    /// `theorem_name` must be a valid Lean identifier.
    #[must_use]
    pub fn render_lean_module_with_inductives(
        &self,
        theorem_name: &str,
        goal: ExprId,
        proof: ExprId,
        real_inductives: &[NameId],
    ) -> String {
        self.render_lean_module_impl(theorem_name, goal, proof, real_inductives, false)
    }

    /// Compact counterpart of [`Self::render_lean_module_with_inductives`].
    /// Repeated closed proof nodes and large single-use closed regions are
    /// hoisted, while declaration expressions receive scoped local chunks and
    /// listed inductives retain Lean-side recursor computation.
    #[must_use]
    pub fn render_lean_module_compact_with_inductives(
        &self,
        theorem_name: &str,
        goal: ExprId,
        proof: ExprId,
        real_inductives: &[NameId],
    ) -> String {
        self.render_lean_module_impl(theorem_name, goal, proof, real_inductives, true)
    }

    /// Streams the same compact module to an I/O writer without accumulating it
    /// beside the checked expression arena.
    ///
    /// Output is byte-for-byte identical to
    /// [`Self::render_lean_module_compact_with_inductives`]. Streaming is useful
    /// when a corpus-scale proof and its final source module cannot safely coexist
    /// in one bounded address space.
    ///
    /// # Errors
    ///
    /// Returns the first error reported by `writer`.
    pub fn write_lean_module_compact_with_inductives<W: std::io::Write + ?Sized>(
        &self,
        writer: &mut W,
        theorem_name: &str,
        goal: ExprId,
        proof: ExprId,
        real_inductives: &[NameId],
    ) -> std::io::Result<()> {
        let mut output = IoLeanModuleOutput {
            writer,
            error: None,
        };
        self.write_lean_module_impl(
            &mut output,
            theorem_name,
            goal,
            proof,
            real_inductives,
            true,
        );
        if let Some(error) = output.error {
            Err(error)
        } else {
            Ok(())
        }
    }

    /// Render the **shared prelude module** holding every declaration reachable
    /// from `roots`, to be compiled once and `import`ed by the query modules
    /// [`Self::render_lean_module_compact_importing`] renders.
    ///
    /// `roots` are declaration names, typically every name in the carrier
    /// context's environment before any query-specific symbol was admitted
    /// (`kernel.environment().iter().map(|(n, _)| *n)`). Rendering is
    /// deterministic, so two contexts built the same way produce a byte-identical
    /// prelude — which is what makes "emit once, import many" sound rather than
    /// merely convenient.
    ///
    /// `module_name` must be a valid Lean module name and must match the file
    /// stem the source is written to.
    ///
    /// The returned module carries no theorem and no `#print axioms`: it is a
    /// development, not a claim.
    #[must_use]
    pub fn render_lean_prelude_module(
        &self,
        module_name: &str,
        roots: &[NameId],
    ) -> LeanPreludeModule {
        let order = self.reachable_decl_order_from_names(roots);
        let mut source = String::new();
        Self::write_module_banner(&mut source, BannerKind::SharedPrelude);
        let (owned_by_lean, at_consts, real_inductives) = self.lean_owned_constants(&order, &[]);
        self.write_decl_blocks(
            &mut source,
            &order,
            &real_inductives,
            &owned_by_lean,
            &at_consts,
            &BTreeSet::new(),
            true,
        );
        // Everything in `order` is supplied by this module once compiled --
        // including the constructors and recursors it did NOT write out, because
        // Lean regenerates those from the `inductive` commands it did.
        let provided: BTreeSet<NameId> = order.into_iter().collect();
        LeanPreludeModule {
            name: module_name.to_owned(),
            source,
            provided,
        }
    }

    /// Render a **query module** that `import`s `prelude_module` instead of
    /// inlining the development it supplies.
    ///
    /// Semantically this is [`Self::render_lean_module_compact_with_inductives`]
    /// with the shared declarations removed and an `import` line in their place;
    /// the theorem term, the `@`-application decisions, and the `#print axioms`
    /// tail are identical. Checking it requires the prelude compiled to an
    /// `.olean` on `LEAN_PATH` — see [`LeanPreludeModule::check_script`].
    ///
    /// `prelude_module` must have been rendered from **this** kernel: names are
    /// interned per kernel, so a [`LeanPreludeModule`] from another one would
    /// suppress the wrong declarations.
    #[must_use]
    pub fn render_lean_module_compact_importing(
        &self,
        theorem_name: &str,
        goal: ExprId,
        proof: ExprId,
        real_inductives: &[NameId],
        prelude_module: &LeanPreludeModule,
    ) -> String {
        let mut out = String::new();
        self.write_lean_module_shaped(
            &mut out,
            theorem_name,
            goal,
            proof,
            real_inductives,
            true,
            &prelude_module.provided,
            Some(&prelude_module.name),
        );
        out
    }

    fn render_lean_module_impl(
        &self,
        theorem_name: &str,
        goal: ExprId,
        proof: ExprId,
        real_inductives: &[NameId],
        compact: bool,
    ) -> String {
        let mut out = String::new();
        self.write_lean_module_impl(
            &mut out,
            theorem_name,
            goal,
            proof,
            real_inductives,
            compact,
        );
        out
    }

    /// The fixed module preamble: `prelude` mode, an optional `import` of a
    /// separately-compiled shared module, the codegen section, the
    /// recursion-depth option, and Lean's compiler-internal constants.
    ///
    /// `import_module` is `Some(name)` for a **query** module in the split
    /// layout ([`Kernel::render_lean_module_compact_importing`]). Lean requires
    /// `prelude` and every `import` to precede all other commands, so the import
    /// is written immediately after `prelude`. The compiler-internal constants
    /// are then **omitted**, because the imported module already declares them
    /// and Lean rejects a redeclaration -- the option lines are module-scoped and
    /// are repeated.
    ///
    /// Its own function because it is long, fixed text and
    /// [`Self::write_lean_module_impl`] is over `clippy::too_many_lines`
    /// with it inline -- a lint that fires on STABLE and not on nightly.
    fn write_module_banner<O: LeanModuleOutput>(out: &mut O, kind: BannerKind<'_>) {
        let _ = out.write_str(match kind {
            BannerKind::SelfContained => {
                "-- Auto-generated by axeyum-lean-kernel: a self-contained re-check of a\n\
                 -- reconstructed refutation. `prelude` avoids clashing with Lean core.\n\
                 prelude\n"
            }
            BannerKind::SharedPrelude => {
                "-- Auto-generated by axeyum-lean-kernel: the SHARED development a family\n\
                 -- of query modules imports. It proves nothing on its own; it carries the\n\
                 -- declarations every refutation over this carrier cites. Compile it to an\n\
                 -- `.olean` and put its directory on `LEAN_PATH`.\n\
                 -- `prelude` avoids clashing with Lean core.\n\
                 prelude\n"
            }
            BannerKind::Importing(_) => {
                "-- Auto-generated by axeyum-lean-kernel: a re-check of a reconstructed\n\
                 -- refutation against a separately-compiled shared development.\n\
                 -- `prelude` avoids clashing with Lean core.\n\
                 prelude\n"
            }
        });
        if let BannerKind::Importing(module) = kind {
            let _ = write!(
                out,
                "-- The shared development is emitted once by\n\
                 -- `Kernel::render_lean_prelude_module`. Build it to `{module}.olean`\n\
                 -- first and point `LEAN_PATH` at the directory holding it.\n\
                 import {module}\n"
            );
        }
        let _ = out.write_str(
            "set_option linter.unusedVariables false\n\
         -- These declarations are proofs, not programs: a recursor-based `def`\n\
         -- has no compiled code and Lean's code generator declines it\n\
         -- (\"code generator does not support recursor `T.rec` yet\"). The section\n\
         -- suppresses codegen only; it does not weaken type checking.\n\
         noncomputable section\n\
         -- Scope-aware sharing (see `ScopeId`) binds repeated subterms with\n\
         -- `let`, and a `let` chain is NESTED syntax: one binding per level.\n\
         -- Measured 2026-08-18, the constructed-carrier module binds 2,897\n\
         -- of them inside one distributivity lemma alone, and Lean 4.30.0\n\
         -- rejected the file at that declaration with `maximum recursion\n\
         -- depth has been reached` -- the default limit is 512. (No carrier\n\
         -- name appears in this banner on purpose: a sibling guard asserts a\n\
         -- module over the constructed carrier never spells the axiomatized\n\
         -- package's name, and it reads the whole file as one string.) This\n\
         -- raises the\n\
         -- ELABORATOR's recursion counter and nothing else: the kernel still\n\
         -- checks every term, and `#print axioms` is unaffected.\n\
         set_option maxRecDepth 65536\n\n",
        );
        // The compiler-internal constants are declared exactly ONCE across a
        // module set: an importing module gets them from the import, and Lean
        // rejects a redeclaration ("has already been declared").
        if matches!(kind, BannerKind::Importing(_)) {
            return;
        }
        let _ = out.write_str(
            "-- Lean's own compiler-internal constants, which `Init.Prelude` declares\n\
         -- (`unsafe axiom lcErased : Type`) and `prelude` mode therefore omits.\n\
         -- Lean 4.34 runs code generation over a Prop-valued inductive that\n\
         -- carries data -- `Or`, `Exists`, `Nat.le` -- and its IR names these, so\n\
         -- without them the module dies on `Unknown constant lcErased` before any\n\
         -- proof is checked. Measured 2026-08-17: 21 of 77 crosscheck families were\n\
         -- rejected by 4.34.0-rc1 and accepted by 4.30.0, which is why the gate's\n\
         -- verdict depended on which toolchain happened to be installed.\n\
         --\n\
         -- They are compiler-only: no proof term mentions them, so they do NOT\n\
         -- enter any `#print axioms` footprint. Asserted, not assumed, by\n\
         -- `codegen_constants_are_declared_but_never_in_the_footprint`.\n\
         unsafe axiom lcErased : Type\n\
         unsafe axiom lcAny : Type\n\
         unsafe axiom lcVoid : Type\n\n",
        );
    }

    fn write_lean_module_impl<O: LeanModuleOutput>(
        &self,
        out: &mut O,
        theorem_name: &str,
        goal: ExprId,
        proof: ExprId,
        real_inductives: &[NameId],
        compact: bool,
    ) {
        self.write_lean_module_shaped(
            out,
            theorem_name,
            goal,
            proof,
            real_inductives,
            compact,
            &BTreeSet::new(),
            None,
        );
    }

    /// The one module writer, in the three shapes [`BannerKind`] names.
    ///
    /// `provided` is the set of declaration names a separately-compiled imported
    /// module already supplies: they are **skipped** here (Lean rejects a
    /// redeclaration) but still counted when deciding which constants need an
    /// `@`-application, because that is a property of the constant and not of
    /// which file declares it. `import_module` is `Some` exactly when `provided`
    /// is non-empty in the intended use, but the two are independent parameters
    /// so a test can vary one without the other.
    #[allow(clippy::too_many_arguments)]
    fn write_lean_module_shaped<O: LeanModuleOutput>(
        &self,
        out: &mut O,
        theorem_name: &str,
        goal: ExprId,
        proof: ExprId,
        real_inductives: &[NameId],
        compact: bool,
        provided: &BTreeSet<NameId>,
        import_module: Option<&str>,
    ) {
        let order = self.reachable_decl_order(&[goal, proof]);
        let (owned_by_lean, at_consts, all_inductives) =
            self.lean_owned_constants(&order, real_inductives);
        let real_inductives: &[NameId] = &all_inductives;
        Self::write_module_banner(
            out,
            match import_module {
                Some(module) => BannerKind::Importing(module),
                None => BannerKind::SelfContained,
            },
        );
        self.write_decl_blocks(
            out,
            &order,
            real_inductives,
            &owned_by_lean,
            &at_consts,
            provided,
            compact,
        );
        let shares = if compact {
            self.compact_share_plan(&[goal, proof], theorem_name, &at_consts)
        } else {
            LeanSharePlan::default()
        };
        let view = ShareView::new(&shares);
        for &expression in &shares.order {
            let key = (expression, ROOT_SCOPE);
            let name = &shares.names[&key];
            let _ = write!(out, "\ndef {name} :=\n  ");
            self.write_lean_with_shares(out, expression, &at_consts, view.expanding(key));
            let _ = out.write_char('\n');
        }
        let _ = write!(out, "\ntheorem {theorem_name} : ");
        if compact {
            self.write_lean_with_shares(out, goal, &at_consts, view);
        } else {
            self.write_lean_without_shares(out, goal, &at_consts);
        }
        let _ = out.write_str(" :=\n  ");
        if compact {
            self.write_lean_with_shares(out, proof, &at_consts, view);
        } else {
            self.write_lean_without_shares(out, proof, &at_consts);
        }
        let _ = write!(out, "\n\n#print axioms {theorem_name}\n");
    }

    /// The constants Lean itself owns in a module covering `order`, and the ones
    /// that must be applied with `@`.
    ///
    /// Every reachable inductive is rendered as a real Lean `inductive`, not as
    /// an opaque `axiom`. An axiomatized family has no ι-reduction rule on the
    /// Lean side, so Lean's definitional equality is strictly weaker than the
    /// kernel's and any proof whose `Eq.refl` needs a recursor to *compute* is
    /// rejected — see [`Self::render_lean_module_with_inductives`].
    /// `requested` remains an explicit request (it is what a caller uses to state
    /// the dependency), but it is a subset of what is emitted.
    ///
    /// Returns `(owned_by_lean, at_consts, inductives)`: the constructor and
    /// recursor names Lean auto-generates (emit nothing for them), the
    /// `@`-application set — Lean makes an inductive's parameters and a
    /// recursor's motive **implicit**, so the kernel's positional applications
    /// must be written with `@` — and the inductives themselves in a stable
    /// order.
    ///
    /// This is computed over the WHOLE reachable set, never over the subset a
    /// particular module writes out: whether a constant needs `@` is a property
    /// of the constant, not of which file declares it, and a query module that
    /// imports its inductives must still apply their constructors with `@`.
    fn lean_owned_constants(
        &self,
        order: &[NameId],
        requested: &[NameId],
    ) -> (BTreeSet<NameId>, BTreeSet<NameId>, Vec<NameId>) {
        let mut all_inductives: BTreeSet<NameId> = order
            .iter()
            .copied()
            .filter(|n| {
                matches!(
                    self.environment().get(*n),
                    Some(Declaration::Inductive { .. })
                )
            })
            .collect();
        all_inductives.extend(requested.iter().copied());
        let all_inductives: Vec<NameId> = all_inductives.into_iter().collect();

        let mut owned_by_lean: BTreeSet<NameId> = BTreeSet::new();
        let mut at_consts: BTreeSet<NameId> = BTreeSet::new();
        for &ind in &all_inductives {
            if let Some(Declaration::Inductive { ctor_names, .. }) = self.environment().get(ind) {
                for &c in ctor_names {
                    owned_by_lean.insert(c);
                    at_consts.insert(c);
                }
                let rec = self.name_of_rec(ind);
                owned_by_lean.insert(rec);
                at_consts.insert(rec);
            }
        }
        (owned_by_lean, at_consts, all_inductives)
    }

    /// Emit one top-level command per declaration in `order`, skipping the
    /// constructors/recursors Lean regenerates from an emitted `inductive`
    /// (`owned_by_lean`) and anything an imported module already supplies
    /// (`provided`).
    #[allow(clippy::too_many_arguments)]
    fn write_decl_blocks<O: LeanModuleOutput>(
        &self,
        out: &mut O,
        order: &[NameId],
        real_inductives: &[NameId],
        owned_by_lean: &BTreeSet<NameId>,
        at_consts: &BTreeSet<NameId>,
        provided: &BTreeSet<NameId>,
        compact: bool,
    ) {
        for name in order {
            if owned_by_lean.contains(name) || provided.contains(name) {
                continue;
            }
            if real_inductives.contains(name)
                && let Some(block) = self.render_real_inductive(*name)
            {
                out.append_owned(block);
                let _ = out.write_char('\n');
                continue;
            }
            if let Some(decl) = self.environment().get(*name) {
                self.write_decl_command_with_at(out, decl, at_consts, compact);
                let _ = out.write_char('\n');
            }
        }
    }

    /// The recursor name `I.rec` an inductive `I` generates: the `Recursor`
    /// declaration whose name's parent is `ind`. Falls back to `ind` itself if no
    /// recursor is registered (then nothing extra is skipped).
    fn name_of_rec(&self, ind: NameId) -> NameId {
        self.environment()
            .iter()
            .find_map(|(&n, decl)| {
                if matches!(decl, Declaration::Recursor { .. })
                    && matches!(self.name_node(n), NameNode::Str(parent, s)
                        if *parent == ind && s == "rec")
                {
                    Some(n)
                } else {
                    None
                }
            })
            .unwrap_or(ind)
    }

    /// Render an inductive `I` as a real Lean
    /// `inductive I (p₀ : P₀) … : <indices → Sort u> where | c₀ : <ty₀> | …`
    /// command, so Lean regenerates its constructors and recursor (with ι).
    ///
    /// The kernel stores an inductive's parameters and indices in **one**
    /// telescope plus a `num_params` count (`Declaration::Inductive::num_params`).
    /// Lean's surface syntax needs them separated: binders written before the
    /// colon are parameters, everything after it is indices. Emitting the whole
    /// telescope after the colon makes every parameter an index, and Lean then
    /// generates a recursor whose argument order does not match the kernel's —
    /// every `I.rec` application in the module fails. So the first `num_params`
    /// binders are opened as parameter binders here, and each constructor type
    /// has that same parameter prefix **stripped** and is rendered with the
    /// inductive's parameter binders in scope (Lean re-adds them, implicitly,
    /// which is why the caller must apply constructors with `@`).
    ///
    /// A reference to `I` inside its own constructor types is a *local* during
    /// elaboration, so it is rendered bare — without `@` and without explicit
    /// universe arguments (`Eq.{u}` inside `Eq` is rejected by Lean with
    /// "invalid use of explicit universe parameters, `Eq` is a local variable").
    ///
    /// Returns [`None`] — keeping the caller's axiom rendering — when the
    /// declaration is not an `Inductive`, when it belongs to a **mutual** group
    /// (Lean needs one `inductive … where … and …` command for the whole group,
    /// which this writer does not emit), when its stored type does not open
    /// `num_params` parameter binders, or when a constructor type does not open
    /// the same parameter prefix.
    fn render_real_inductive(&self, ind: NameId) -> Option<String> {
        let Some(Declaration::Inductive {
            name,
            uparams,
            ty,
            num_params,
            ctor_names,
            ..
        }) = self.environment().get(ind).cloned()
        else {
            return None;
        };
        if self
            .environment()
            .inductive_group(ind)
            .is_some_and(|group| group.len() > 1)
        {
            return None;
        }
        let num_params = usize::from(num_params);
        let no_at_consts = BTreeSet::new();
        // `I` itself is a local variable inside its own declaration block.
        let locals: BTreeSet<NameId> = std::iter::once(ind).collect();

        let mut parameter_binders: Vec<String> = Vec::new();
        let mut parameters = String::new();
        let mut result = ty;
        for _ in 0..num_params {
            let (binder_name, binder_ty, body) = match self.expr_node(result) {
                ExprNode::Pi(binder_name, binder_ty, body, _) => (*binder_name, *binder_ty, *body),
                _ => return None,
            };
            let binder = self.binder_name(binder_name, parameter_binders.len());
            let rendered =
                self.render_expr(binder_ty, &mut parameter_binders, &no_at_consts, &locals);
            let _ = write!(parameters, " ({binder} : {rendered})");
            parameter_binders.push(binder);
            result = body;
        }
        let mut block = format!(
            "inductive {}{}{} : {} where",
            self.render_name(name),
            self.render_uparams(&uparams),
            parameters,
            self.render_expr(
                result,
                &mut parameter_binders.clone(),
                &no_at_consts,
                &locals
            )
        );
        for &ctor in &ctor_names {
            let Some(Declaration::Constructor { ty: ctor_ty, .. }) = self.environment().get(ctor)
            else {
                return None;
            };
            let mut ctor_result = *ctor_ty;
            for _ in 0..num_params {
                match self.expr_node(ctor_result) {
                    ExprNode::Pi(_, _, body, _) => ctor_result = *body,
                    _ => return None,
                }
            }
            let mut binders = parameter_binders.clone();
            let _ = write!(
                block,
                "\n  | {} : {}",
                self.render_short_ctor_name(ctor),
                self.render_expr(ctor_result, &mut binders, &no_at_consts, &locals)
            );
        }
        Some(block)
    }

    /// A constructor's **leaf** name (the last `.`-segment), as Lean's `inductive`
    /// syntax expects (`| true : …`, not `| Bool.true : …`).
    fn render_short_ctor_name(&self, ctor: NameId) -> String {
        match self.name_node(ctor) {
            NameNode::Str(_, s) => s.clone(),
            _ => self.render_name(ctor),
        }
    }

    /// Render a declaration as a self-contained `prelude`-mode command: inductives,
    /// constructors, and recursors become `axiom`s (carrying their kernel type),
    /// since `prelude` mode has no `inductive`-generated recursors to rely on; all
    /// other kinds render through [`Self::render_lean_decl`].
    fn render_decl_command(&self, decl: &Declaration) -> String {
        match decl {
            Declaration::Inductive {
                name, uparams, ty, ..
            }
            | Declaration::Constructor {
                name, uparams, ty, ..
            }
            | Declaration::Recursor {
                name, uparams, ty, ..
            } => format!(
                "axiom {}{} : {}",
                self.render_name(*name),
                self.render_uparams(uparams),
                self.render_lean(*ty)
            ),
            Declaration::Quotient { name, .. } => format!(
                "-- `{}` is provided by Lean's built-in quotient package",
                self.render_name(*name)
            ),
            _ => self.render_lean_decl(decl),
        }
    }

    /// Like [`Self::render_decl_command`], but renders the declaration's type (and
    /// a definition/theorem/opaque value) with the `@`-application set `at_consts`,
    /// so any reference to a real-inductive recursor inside an axiom *type* (e.g.
    /// the is-tester hypothesis `h : ¬(Eq Bool (is_C …) true)`, whose `is_C` is a
    /// recursor application) applies it positionally with `@` — matching Lean's
    /// implicit-motive recursor. When `at_consts` is empty this is byte-identical to
    /// [`Self::render_decl_command`].
    fn write_decl_command_with_at<O: LeanModuleOutput>(
        &self,
        out: &mut O,
        decl: &Declaration,
        at_consts: &std::collections::BTreeSet<NameId>,
        compact: bool,
    ) {
        if at_consts.is_empty() && !compact {
            out.append_owned(self.render_decl_command(decl));
            return;
        }
        match decl {
            // Inductives/constructors/recursors keep the `axiom` rendering (carrying
            // their kernel type); a plain `Axiom` renders the same way. The only
            // difference from [`Self::render_decl_command`] is `@`-aware type rendering.
            Declaration::Inductive {
                name, uparams, ty, ..
            }
            | Declaration::Constructor {
                name, uparams, ty, ..
            }
            | Declaration::Recursor {
                name, uparams, ty, ..
            }
            | Declaration::Axiom { name, uparams, ty } => {
                let _ = write!(
                    out,
                    "axiom {}{} : ",
                    self.render_name(*name),
                    self.render_uparams(uparams)
                );
                self.write_lean_for_module(out, *ty, at_consts, compact);
            }
            Declaration::Quotient { name, .. } => {
                let _ = write!(
                    out,
                    "-- `{}` is provided by Lean's built-in quotient package",
                    self.render_name(*name)
                );
            }
            Declaration::Definition {
                name,
                uparams,
                ty,
                value,
                ..
            } => {
                let _ = write!(
                    out,
                    "def {}{} : ",
                    self.render_name(*name),
                    self.render_uparams(uparams)
                );
                self.write_lean_for_module(out, *ty, at_consts, compact);
                let _ = out.write_str(" :=\n  ");
                self.write_lean_for_module(out, *value, at_consts, compact);
            }
            Declaration::Theorem {
                name,
                uparams,
                ty,
                value,
            }
            | Declaration::Opaque {
                name,
                uparams,
                ty,
                value,
            } => {
                let kw = if matches!(decl, Declaration::Opaque { .. }) {
                    "opaque"
                } else {
                    self.proof_keyword()
                };
                let _ = write!(
                    out,
                    "{kw} {}{} : ",
                    self.render_name(*name),
                    self.render_uparams(uparams)
                );
                self.write_lean_for_module(out, *ty, at_consts, compact);
                let _ = out.write_str(" :=\n  ");
                self.write_lean_for_module(out, *value, at_consts, compact);
            }
        }
    }

    fn write_lean_for_module<O: LeanModuleOutput>(
        &self,
        out: &mut O,
        expression: ExprId,
        at_consts: &BTreeSet<NameId>,
        compact: bool,
    ) {
        if compact {
            self.write_lean_with_local_shares(out, expression, at_consts);
        } else {
            self.write_lean_without_shares(out, expression, at_consts);
        }
    }

    /// Every declaration `name` rests on that was admitted **without** a checked
    /// proof — this kernel's answer to Lean's `#print axioms`.
    ///
    /// Walks the transitive constant closure from `name` (through each reachable
    /// declaration's type, and its value for definitions/theorems/opaques) and
    /// keeps those admitted on trust: [`Declaration::Axiom`],
    /// [`Declaration::Opaque`] (no proof body to check) and
    /// [`Declaration::Quotient`] (the quotient primitives — `Quot.sound` is one
    /// of the three axioms Lean itself reports). An empty result means axiom-free,
    /// which is the strongest claim this project makes about a theorem.
    ///
    /// # Why this is per-theorem and not per-environment
    ///
    /// The only footprint available before this was "enumerate the trusted
    /// declarations in the whole environment" (the `nat_axiom_inventory` example).
    /// That bounds a theorem's footprint — a proof cannot depend on a declaration
    /// the environment does not contain — but only bounds it, and the bound is
    /// useless exactly where it matters: in the `Int` and `Real` preludes, where
    /// the environment-wide answer is "all 34" or "all 30" for every theorem
    /// alike. A fact ledger cannot record an honest `axiom_footprint` for a
    /// non-`Nat` proposition from a bound like that, so an extraction lane
    /// declined to record ANY integer or real fact rather than guess. This closes
    /// that: the answer is now specific to the theorem asked about.
    ///
    /// Names are returned sorted by rendered name, so the result is stable across
    /// runs and interning orders and can be committed to an artifact.
    ///
    /// A `name` absent from the environment has no dependencies and yields an
    /// empty footprint; callers wanting to distinguish "axiom-free" from "not
    /// declared" should check the environment first.
    pub fn axiom_footprint(&self, name: NameId) -> Vec<NameId> {
        let mut seen: BTreeSet<NameId> = BTreeSet::new();
        let mut work = vec![name];
        seen.insert(name);
        while let Some(n) = work.pop() {
            for d in self.decl_deps(n) {
                if seen.insert(d) {
                    work.push(d);
                }
            }
        }
        let mut trusted: Vec<NameId> = seen
            .into_iter()
            .filter(|&n| {
                matches!(
                    self.environment().get(n),
                    Some(
                        Declaration::Axiom { .. }
                            | Declaration::Opaque { .. }
                            | Declaration::Quotient { .. }
                    )
                )
            })
            .collect();
        trusted.sort_by_key(|&n| self.display_name(n).to_string());
        trusted
    }

    /// The environment declarations reachable from `roots` — every constant a
    /// module rendering `roots` would have to declare, in dependency order.
    ///
    /// Public because a **shared prelude module** is defined by a root set the
    /// caller chooses, and the obvious choice — "every declaration in the carrier
    /// context" — is the wrong one. Measured 2026-08-18 on the constructed-real
    /// carrier: the context holds 445 declarations, a refutation reaches 280 of
    /// them, and two of the 165 it does not reach (`CReal.Equiv.not_zero_one`,
    /// `CReal.not_le_one_zero`) are **rejected by Lean 4.30.0's ELABORATOR**
    /// although the in-tree kernel admits them. Rooting a shared module at the
    /// whole environment therefore produces a file `lean Module.lean` will not
    /// compile, for reasons that have nothing to do with the refutations
    /// importing it. Intersecting this answer with the carrier snapshot gives a
    /// root set that is both shared and checkable.
    ///
    /// **Elaborator, not kernel** — this said "Lean" until ADR-0488, and the
    /// difference is the whole diagnosis. Lean's *kernel* accepts all four, and
    /// the whole carrier with them (`real_lean_creal_carrier_kernel_replay`
    /// replays 470 of 470 through `Environment.addDeclCore` in 1.4 s). The
    /// elaborator's reducer treats a `theorem` as opaque, and these proofs must
    /// compute through `Nat.gcd`, whose descent rests on the theorem
    /// `Nat.mod_lt`; re-spelling every `theorem` as `def` in the same file makes
    /// the elaborator accept it.
    #[must_use]
    pub fn declarations_reached(&self, roots: &[ExprId]) -> Vec<NameId> {
        self.reachable_decl_order(roots)
    }

    /// The environment declarations reachable from `roots` (transitively through
    /// each declaration's type and — for definitions/theorems/opaques — value),
    /// in dependency order (a declaration appears after every declaration it
    /// references). Names not present in the environment are skipped.
    fn reachable_decl_order(&self, roots: &[ExprId]) -> Vec<NameId> {
        let mut seed = Vec::new();
        for &r in roots {
            self.collect_const_deps(r, &mut seed);
        }
        self.decl_order_from_seed(seed)
    }

    /// [`Self::reachable_decl_order`] rooted at declaration **names** rather than
    /// at expressions — what a shared prelude module is defined by, since it has
    /// no goal or proof term to walk from.
    fn reachable_decl_order_from_names(&self, roots: &[NameId]) -> Vec<NameId> {
        self.decl_order_from_seed(roots.to_vec())
    }

    fn decl_order_from_seed(&self, seed: Vec<NameId>) -> Vec<NameId> {
        // Reachability closure over constant references.
        let mut needed: std::collections::BTreeSet<NameId> = std::collections::BTreeSet::new();
        let mut work: Vec<NameId> = Vec::new();
        for n in seed {
            if needed.insert(n) {
                work.push(n);
            }
        }
        while let Some(n) = work.pop() {
            for d in self.render_deps(n) {
                if needed.insert(d) {
                    work.push(d);
                }
            }
        }
        // Deterministic post-order DFS topological sort over the reachable set.
        let mut visited: std::collections::BTreeSet<NameId> = std::collections::BTreeSet::new();
        let mut order: Vec<NameId> = Vec::new();
        for &n in &needed {
            self.topo_visit(n, &needed, &mut visited, &mut order);
        }
        order
    }

    /// The constants a declaration references (in its type, plus its value for
    /// `Definition`/`Theorem`/`Opaque`).
    /// The **theorems** `name`'s statement and proof directly reference.
    ///
    /// The dependency walk this shares with [`Self::axiom_footprint`] already
    /// computes the whole constant closure; that method keeps only the trusted
    /// declarations and throws the rest away. This keeps the other half, because
    /// the discarded half is what a fact ledger's `depends_on` is supposed to be.
    ///
    /// # Why derive it rather than write it down
    ///
    /// ADR-0465 settles that the axiom ledger is derived, not transcribed. The
    /// same argument applies here and the evidence is stronger: measured
    /// 2026-08-17, 65 of 109 ledger facts declare no dependency and have no
    /// dependent, so proving one usually unlocks nothing — the arrow CLAUDE.md
    /// calls *"the concept DAG and the fact ledger say what to prove next"* has
    /// little to work with. Some of that isolation is honest (an SMT-LIB
    /// propositional refutation really does not rest on a Nat lemma), but a
    /// kernel-route fact whose proof cites four prelude theorems and declares
    /// none is simply unrecorded, and nothing could tell the two apart.
    ///
    /// DIRECT references only, not the transitive closure: `depends_on` is meant
    /// to say what a proposition immediately rests on, and the transitive set of
    /// a late theorem is most of the prelude.
    ///
    /// Definitions, inductives and axioms are filtered out — a proof of
    /// `Nat.add_comm` references `Nat` and `Nat.add`, and recording those as
    /// dependencies would say nothing about which *propositions* it needs.
    /// Self-reference is dropped. Names are sorted by rendered name, so the
    /// result is stable across runs and interning orders and can be committed.
    #[must_use]
    pub fn theorem_dependencies(&self, name: NameId) -> Vec<NameId> {
        let mut deps: Vec<NameId> = self
            .decl_deps(name)
            .into_iter()
            .filter(|&d| d != name)
            .filter(|&d| matches!(self.environment().get(d), Some(Declaration::Theorem { .. })))
            .collect();
        deps.sort_by_key(|&n| self.display_name(n).to_string());
        deps.dedup();
        deps
    }

    fn decl_deps(&self, name: NameId) -> Vec<NameId> {
        let mut deps = Vec::new();
        if let Some(decl) = self.environment().get(name) {
            self.collect_const_deps(decl.ty(), &mut deps);
            match decl {
                Declaration::Definition { value, .. }
                | Declaration::Theorem { value, .. }
                | Declaration::Opaque { value, .. } => {
                    self.collect_const_deps(*value, &mut deps);
                }
                _ => {}
            }
        }
        deps
    }

    /// [`Self::decl_deps`] plus, for an **inductive**, the constants its
    /// CONSTRUCTORS' types mention.
    ///
    /// Used only by the module renderer, and deliberately not by
    /// [`Self::axiom_footprint`]: a footprint is what a proof *rests on*, and a
    /// constructor's type is not that. But a rendered `inductive` command writes
    /// its constructors inline, so a module needs everything those types mention
    /// **before** the family, and `decl_deps` of an inductive sees only its own
    /// type — for the constructed reals that is `Sort 1`, which depends on
    /// nothing at all.
    ///
    /// Measured 2026-08-18: without this, a module carrying the constructed ℚ
    /// emits `inductive Rat` at line 255 with a constructor mentioning
    /// `Int.natAbs`, which the same module defines at line 365, and real Lean
    /// rejects it with `Unknown constant Int.natAbs`. Five of the 77
    /// `lean_crosscheck` families failed exactly this way. The `Real` package
    /// never exposed it because its only inductives are the propositional
    /// connectives, whose constructors mention nothing that is not already
    /// above them.
    fn render_deps(&self, name: NameId) -> Vec<NameId> {
        let mut deps = self.decl_deps(name);
        if let Some(Declaration::Inductive { ctor_names, .. }) = self.environment().get(name) {
            for &ctor in ctor_names {
                deps.extend(self.decl_deps(ctor));
            }
        }
        deps
    }

    fn topo_visit(
        &self,
        name: NameId,
        needed: &std::collections::BTreeSet<NameId>,
        visited: &mut std::collections::BTreeSet<NameId>,
        order: &mut Vec<NameId>,
    ) {
        if !visited.insert(name) {
            return;
        }
        for d in self.render_deps(name) {
            if needed.contains(&d) {
                self.topo_visit(d, needed, visited, order);
            }
        }
        order.push(name);
    }

    /// Collect (iteratively, to avoid deep recursion on large proof terms) every
    /// `Const` name referenced anywhere inside `root`.
    fn collect_const_deps(&self, root: ExprId, out: &mut Vec<NameId>) {
        let mut visited = HashSet::new();
        let mut stack = vec![root];
        while let Some(e) = stack.pop() {
            if !visited.insert(e) {
                continue;
            }
            match self.expr_node(e) {
                ExprNode::Const(n, _) => out.push(*n),
                ExprNode::Proj(type_name, _, structure) => {
                    out.push(*type_name);
                    stack.push(*structure);
                }
                ExprNode::App(f, a) => {
                    stack.push(*f);
                    stack.push(*a);
                }
                ExprNode::Lam(_, t, b, _) | ExprNode::Pi(_, t, b, _) => {
                    stack.push(*t);
                    stack.push(*b);
                }
                ExprNode::Let(_, t, v, b) => {
                    stack.push(*t);
                    stack.push(*v);
                    stack.push(*b);
                }
                ExprNode::BVar(_) | ExprNode::FVar(_) | ExprNode::Sort(_) | ExprNode::Lit(_) => {}
            }
        }
    }

    /// The universe-parameter suffix `.{u, v}` for a declaration head (empty when
    /// the declaration is universe-monomorphic).
    fn render_uparams(&self, uparams: &[NameId]) -> String {
        if uparams.is_empty() {
            String::new()
        } else {
            let names: Vec<String> = uparams.iter().map(|n| self.render_name(*n)).collect();
            format!(".{{{}}}", names.join(", "))
        }
    }

    /// A hierarchical [`NameId`] as a dotted Lean name (`a.b.1`); the anonymous root
    /// renders empty.
    ///
    /// The kernel's **computational `Nat`** (root segment `Nat`, with children
    /// `Nat.zero`/`Nat.succ`/`Nat.rec`/…) is rendered under the non-shadowing root
    /// **`AxNat`** instead. Lean's builtin `Nat` has special kernel support (literal
    /// `OfNat`/`HAdd` elaboration, `Nat.casesOn`/`T.ctorIdx` codegen); emitting our
    /// own `inductive Nat` *shadows* that builtin and a real `lean` binary rejects it
    /// (`failed to construct T.ctorIdx for Nat`, `Unknown constant HAdd.hAdd`). A
    /// user datatype never carries the bare root name `Nat` (datatype families render
    /// as `axeyum.reconstruct.dtrec._N`), so remapping the root `Nat` segment is
    /// unambiguous and affects only the prelude's computational naturals — the
    /// in-tree kernel and its stored names are untouched (this is pure rendering).
    /// A name **as an emitted Lean module spells it**, which is not the same
    /// string as [`Self::display_name`].
    ///
    /// Two rules diverge, and both bite anything that tries to match a
    /// `#print axioms` footprint against `axiom` lines in a module: a numeric
    /// name component is not a legal Lean identifier on its own, so
    /// `axeyum.reconstruct.x.0` is emitted as `axeyum.reconstruct.x._0`; and the
    /// kernel's computational naturals are rooted at `AxNat` so they do not
    /// shadow Lean's `Nat`. Comparing display names to module text silently
    /// reports "not covered" for an artefact that is perfectly correct.
    #[must_use]
    pub fn lean_name(&self, id: NameId) -> String {
        self.render_name(id)
    }

    fn render_name(&self, id: NameId) -> String {
        match self.name_node(id) {
            NameNode::Anonymous => String::new(),
            NameNode::Str(parent, s) => {
                let p = self.render_name(*parent);
                if p.is_empty() {
                    if s == "Nat" {
                        // Non-shadowing root for the kernel's computational naturals.
                        "AxNat".to_owned()
                    } else {
                        s.clone()
                    }
                } else {
                    format!("{p}.{s}")
                }
            }
            NameNode::Num(parent, n) => {
                // A numeric name component is not a legal Lean identifier component
                // on its own (`foo.0` parses as projection); prefix it with `_` so
                // generated names like `axeyum.reconstruct.atom.0` export as the
                // valid hierarchical name `axeyum.reconstruct.atom._0`.
                let p = self.render_name(*parent);
                if p.is_empty() {
                    format!("_{n}")
                } else {
                    format!("{p}._{n}")
                }
            }
        }
    }

    /// A universe [`LevelId`] in Lean level syntax. A `Succ` chain over a base is
    /// collapsed into the `base+n` (or a bare numeral `n` when the base is `Zero`)
    /// form Lean's level grammar expects — e.g. `Sort 1` rather than `Sort (0+1)`.
    fn render_level(&self, id: LevelId) -> String {
        let mut offset: u32 = 0;
        let mut cur = id;
        while let LevelNode::Succ(l) = self.level_node(cur) {
            offset += 1;
            cur = *l;
        }
        let base = match self.level_node(cur) {
            LevelNode::Zero => return offset.to_string(),
            LevelNode::Param(n) => self.render_name(*n),
            LevelNode::Max(a, b) => {
                format!("(max {} {})", self.render_level(*a), self.render_level(*b))
            }
            LevelNode::IMax(a, b) => {
                format!("(imax {} {})", self.render_level(*a), self.render_level(*b))
            }
            LevelNode::Succ(_) => unreachable!("Succ chain already consumed"),
        };
        if offset == 0 {
            base
        } else {
            format!("{base}+{offset}")
        }
    }

    /// The binder name to print for a binder declared with [`NameId`] `name` opened
    /// at de Bruijn `depth`; anonymous binders become a generated `x<depth>`.
    fn binder_name(&self, name: NameId, depth: usize) -> String {
        let rendered = self.render_name(name);
        if rendered.is_empty() {
            format!("x{depth}")
        } else {
            rendered
        }
    }

    fn expr_children(&self, id: ExprId) -> Vec<ExprId> {
        match self.expr_node(id) {
            ExprNode::Proj(_, _, structure) => vec![*structure],
            ExprNode::App(function, argument) => vec![*function, *argument],
            ExprNode::Lam(_, ty, body, _) | ExprNode::Pi(_, ty, body, _) => {
                vec![*ty, *body]
            }
            ExprNode::Let(_, ty, value, body) => vec![*ty, *value, *body],
            ExprNode::BVar(_)
            | ExprNode::FVar(_)
            | ExprNode::Sort(_)
            | ExprNode::Const(_, _)
            | ExprNode::Lit(_) => Vec::new(),
        }
    }

    fn expr_postorder(&self, roots: &[ExprId]) -> Vec<ExprId> {
        let mut visited = HashSet::new();
        let mut order = Vec::new();
        let mut stack = roots
            .iter()
            .rev()
            .copied()
            .map(|root| (root, false))
            .collect::<Vec<_>>();
        while let Some((expression, expanded)) = stack.pop() {
            if expanded {
                order.push(expression);
                continue;
            }
            if !visited.insert(expression) {
                continue;
            }
            stack.push((expression, true));
            let children = self.expr_children(expression);
            for child in children.into_iter().rev() {
                stack.push((child, false));
            }
        }
        order
    }

    /// The number of leading `Pi` binders in the kernel type of `name`, i.e. how
    /// many arguments saturate it. `None` when the name is not in the
    /// environment.
    fn decl_binder_arity(&self, name: NameId) -> Option<usize> {
        let mut ty = self.environment().get(name)?.ty();
        let mut arity = 0_usize;
        while let ExprNode::Pi(_, _, body, _) = self.expr_node(ty) {
            ty = *body;
            arity += 1;
        }
        Some(arity)
    }

    /// The head and argument count of `expression`'s full application spine,
    /// without materializing the arguments.
    fn spine_head_and_len(&self, expression: ExprId) -> (ExprId, usize) {
        let mut head = expression;
        let mut len = 0_usize;
        while let ExprNode::App(function, _) = self.expr_node(head) {
            head = *function;
            len += 1;
        }
        (head, len)
    }

    /// True when hoisting `expression` into a top-level `def` (or a `let`) would
    /// change how Lean reads its *reference sites*.
    ///
    /// A `def` inherits the leading binders of the term it is bound to, and a
    /// **bare** reference to a `def` whose type starts with *implicit* binders
    /// makes Lean insert metavariables for them — so the next positional
    /// argument lands in the wrong slot. The kernel term is a flat spine with
    /// every argument explicit; hoisting a *proper prefix* of that spine is what
    /// introduces the implicit binders, because it is exactly the constants in
    /// `at_consts` (the constructors and recursors Lean regenerates for a real
    /// `inductive`) whose parameters, motive and indices Lean makes implicit.
    ///
    /// Measured on 2026-08-14: `def axeyum_proof_share_149 := @Or.rec P` gets
    /// type `{x1 : Prop} → {motive : Or P x1 → Prop} → …`, so
    /// `axeyum_proof_share_149 Q` type-checks `Q` against the `inl` minor
    /// premise and Lean rejects the module — while the kernel term
    /// `Or.rec P Q motive m₁ m₂ t` is well typed and the in-tree kernel accepts
    /// it. Saturated spines carry no leading binders at all, so they stay
    /// shareable and the chunking that bounds module size is preserved.
    fn hoisting_exposes_implicit_binders(
        &self,
        expression: ExprId,
        at_consts: &BTreeSet<NameId>,
    ) -> bool {
        if at_consts.is_empty() || !matches!(self.expr_node(expression), ExprNode::App(_, _)) {
            return false;
        }
        let (head, arguments) = self.spine_head_and_len(expression);
        let ExprNode::Const(name, _) = self.expr_node(head) else {
            return false;
        };
        if !at_consts.contains(name) {
            return false;
        }
        self.decl_binder_arity(*name)
            .is_none_or(|arity| arguments < arity)
    }

    fn compact_share_candidates(
        &self,
        postorder: &[ExprId],
        roots: &[ExprId],
        at_consts: &BTreeSet<NameId>,
    ) -> HashSet<ExprId> {
        let mut occurrences = HashMap::<ExprId, u64>::with_capacity(postorder.len());
        for &root in roots {
            *occurrences.entry(root).or_default() = occurrences
                .get(&root)
                .copied()
                .unwrap_or_default()
                .saturating_add(1);
        }
        for &expression in postorder.iter().rev() {
            let count = occurrences.get(&expression).copied().unwrap_or_default();
            if count == 0 {
                continue;
            }
            for child in self.expr_children(expression) {
                let current = occurrences.get(&child).copied().unwrap_or_default();
                occurrences.insert(child, current.saturating_add(count));
            }
        }

        let mut tree_sizes = HashMap::<ExprId, u64>::with_capacity(postorder.len());
        for &expression in postorder {
            let mut size = 1_u64;
            for child in self.expr_children(expression) {
                size = size.saturating_add(tree_sizes.get(&child).copied().unwrap_or(1));
            }
            tree_sizes.insert(expression, size);
        }

        let candidates = postorder
            .iter()
            .copied()
            .filter(|&expression| {
                occurrences.get(&expression).copied().unwrap_or_default() >= 2
                    && tree_sizes.get(&expression).copied().unwrap_or_default()
                        >= COMPACT_SHARE_MIN_TREE_NODES
                    && self.num_loose_bvars(expression) == 0
                    && !self.has_fvars(expression)
                    && matches!(
                        self.expr_node(expression),
                        ExprNode::App(_, _)
                            | ExprNode::Proj(..)
                            | ExprNode::Lam(..)
                            | ExprNode::Pi(..)
                            | ExprNode::Let(..)
                    )
                    && !self.hoisting_exposes_implicit_binders(expression, at_consts)
            })
            .collect::<Vec<_>>();
        let mut selected = candidates.into_iter().collect::<HashSet<_>>();
        // The occurrence and expanded-tree tables are no longer needed once the
        // repeated-node candidates are selected. Corpus-scale proofs contain
        // millions of expressions, so retaining both while allocating the chunk
        // table needlessly doubles peak serialization memory.
        drop(occurrences);
        drop(tree_sizes);

        // Repetition is not the only way a proof term can become impractical to
        // render.  Resolution commonly produces a long, single-use closed chain;
        // recursively formatting that chain as one surface term creates enormous
        // intermediate strings even though the kernel representation is linear.
        // Add deterministic cut points so every closed region between selected
        // definitions remains bounded.  Open subterms still cannot escape their
        // binder and are therefore never selected here.
        let mut chunk_sizes = HashMap::<ExprId, u64>::with_capacity(postorder.len());
        for &expression in postorder {
            let mut size = 1_u64;
            for child in self.expr_children(expression) {
                size = size.saturating_add(chunk_sizes.get(&child).copied().unwrap_or(1));
            }
            let shareable = self.num_loose_bvars(expression) == 0
                && !self.has_fvars(expression)
                && matches!(
                    self.expr_node(expression),
                    ExprNode::App(_, _)
                        | ExprNode::Proj(..)
                        | ExprNode::Lam(..)
                        | ExprNode::Pi(..)
                        | ExprNode::Let(..)
                )
                && !self.hoisting_exposes_implicit_binders(expression, at_consts);
            if selected.contains(&expression) || (shareable && size >= COMPACT_CHUNK_TREE_NODES) {
                selected.insert(expression);
                size = 1;
            }
            chunk_sizes.insert(expression, size);
        }
        drop(chunk_sizes);
        selected
    }

    fn compact_share_plan(
        &self,
        roots: &[ExprId],
        theorem_name: &str,
        at_consts: &BTreeSet<NameId>,
    ) -> LeanSharePlan {
        let postorder = self.expr_postorder(roots);
        let selected = self.compact_share_candidates(&postorder, roots, at_consts);

        let mut reserved = self
            .environment()
            .iter()
            .map(|(&name, _)| self.render_name(name))
            .collect::<BTreeSet<_>>();
        for &expression in &postorder {
            let binder = match self.expr_node(expression) {
                ExprNode::Lam(name, ..) | ExprNode::Pi(name, ..) | ExprNode::Let(name, ..) => {
                    self.render_name(*name)
                }
                _ => continue,
            };
            if !binder.is_empty() {
                reserved.insert(binder);
            }
        }
        reserved.insert(theorem_name.to_owned());
        let mut names = BTreeMap::new();
        let mut order = Vec::new();
        let mut suffix = 0_u64;
        for expression in postorder {
            if !selected.contains(&expression) {
                continue;
            }
            let name = loop {
                let candidate = format!("axeyum_proof_share_{suffix}");
                suffix += 1;
                if reserved.insert(candidate.clone()) {
                    break candidate;
                }
            };
            names.insert((expression, ROOT_SCOPE), name);
            order.push(expression);
        }
        LeanSharePlan {
            names,
            order,
            blocks: BTreeMap::new(),
        }
    }

    /// The scope a binder node's body is read in.
    ///
    /// A **closed** binder normalizes to [`ROOT_SCOPE`] first, so every
    /// occurrence of it opens the same body scope and its interior stays
    /// shareable across all of them. Planner and writer both call this, which
    /// is what keeps their scope ids in step: a reference that resolved in one
    /// and not the other would silently lose sharing, and a `let` emitted in a
    /// scope no reference reaches would be dead text.
    fn body_scope(&self, binder: ExprId, scope: ScopeId) -> ScopeId {
        let outer = if self.num_loose_bvars(binder) == 0 {
            ROOT_SCOPE
        } else {
            scope
        };
        scope_child(outer, binder)
    }

    /// A key's children, each carried into the scope it is read in.
    fn share_children(&self, key: ShareKey) -> Vec<ShareKey> {
        let (expression, scope) = key;
        let normalize = |child: ExprId, at: ScopeId| -> ShareKey {
            if self.num_loose_bvars(child) == 0 {
                (child, ROOT_SCOPE)
            } else {
                (child, at)
            }
        };
        match self.expr_node(expression) {
            ExprNode::App(function, argument) => {
                vec![normalize(*function, scope), normalize(*argument, scope)]
            }
            ExprNode::Lam(_, ty, body, _) | ExprNode::Pi(_, ty, body, _) => vec![
                normalize(*ty, scope),
                normalize(*body, self.body_scope(expression, scope)),
            ],
            ExprNode::Let(_, ty, value, body) => vec![
                normalize(*ty, scope),
                normalize(*value, scope),
                normalize(*body, self.body_scope(expression, scope)),
            ],
            ExprNode::Proj(_, _, structure) => vec![normalize(*structure, scope)],
            ExprNode::BVar(_)
            | ExprNode::FVar(_)
            | ExprNode::Sort(_)
            | ExprNode::Const(_, _)
            | ExprNode::Lit(_) => Vec::new(),
        }
    }

    /// A **scope-correct** share plan for one expression: which repeated nodes
    /// become a `let`, and in which binder body each `let` is emitted.
    ///
    /// [`Self::compact_share_plan`] hoists to top-level `def`s, so it can only
    /// ever select **closed** nodes — and a proof body is almost entirely open
    /// ones. Measured 2026-08-18 on the shipped constructed-reals front door,
    /// that restriction is why compact rendering saved 0.6% of a 2.6 MB module.
    /// This selects open nodes too, keyed by [`ScopeId`], and homes each `let`
    /// at the top of the innermost body whose binders it reads.
    fn scoped_share_plan(
        &self,
        root: ExprId,
        expression_name: &str,
        at_consts: &BTreeSet<NameId>,
    ) -> LeanSharePlan {
        let (postorder, lam_scopes) = self.scoped_key_postorder(root);
        let selected = self.scoped_share_candidates(root, &postorder, &lam_scopes, at_consts);

        let mut reserved = self
            .environment()
            .iter()
            .map(|(&name, _)| self.render_name(name))
            .collect::<BTreeSet<_>>();
        for key in &postorder {
            let binder = match self.expr_node(key.0) {
                ExprNode::Lam(name, ..) | ExprNode::Pi(name, ..) | ExprNode::Let(name, ..) => {
                    self.render_name(*name)
                }
                _ => continue,
            };
            if !binder.is_empty() {
                reserved.insert(binder);
            }
        }
        reserved.insert(expression_name.to_owned());

        let mut names = BTreeMap::new();
        let mut blocks: BTreeMap<ScopeId, Vec<ShareKey>> = BTreeMap::new();
        let mut suffix = 0_u64;
        // Post-order, so a `let` is always emitted after everything it names.
        for key in postorder {
            if !selected.contains(&key) {
                continue;
            }
            // SHORT on purpose. A share pays for itself only when the name is
            // cheaper than the term it replaces, and these are references, not
            // documentation: measured 2026-08-18 on the constructed-reals front
            // door, `axeyum_proof_share_NNNNN` at ~21 bytes a reference ate most
            // of the saving, and shortening the prefix alone took the shipped
            // module from 1,877,436 bytes to 1,303,499. The top-level `def`
            // names keep the long spelling: there are few of them and they are
            // what a reader greps for.
            let name = loop {
                let candidate = format!("_s{suffix}");
                suffix += 1;
                if reserved.insert(candidate.clone()) {
                    break candidate;
                }
            };
            names.insert(key, name);
            blocks.entry(key.1).or_default().push(key);
        }
        LeanSharePlan {
            names,
            order: Vec::new(),
            blocks,
        }
    }

    /// The key DAG reachable from `root`, in post-order, plus the scopes a
    /// `let` may be opened in.
    ///
    /// A `Pi` or a `Let` body is deliberately not one of them: `let` is a term
    /// form, and this writer will not put one inside a type arrow, so a key
    /// homed there would be referenced by a name nothing ever binds.
    fn scoped_key_postorder(&self, root: ExprId) -> (Vec<ShareKey>, HashSet<ScopeId>) {
        let mut postorder: Vec<ShareKey> = Vec::new();
        let mut visited: HashSet<ShareKey> = HashSet::new();
        let mut lam_scopes: HashSet<ScopeId> = HashSet::new();
        let mut stack: Vec<(ShareKey, bool)> = vec![((root, ROOT_SCOPE), false)];
        while let Some((key, expanded)) = stack.pop() {
            if expanded {
                postorder.push(key);
                continue;
            }
            if !visited.insert(key) {
                continue;
            }
            if matches!(self.expr_node(key.0), ExprNode::Lam(..)) {
                lam_scopes.insert(self.body_scope(key.0, key.1));
            }
            stack.push((key, true));
            for child in self.share_children(key).into_iter().rev() {
                stack.push((child, false));
            }
        }
        drop(visited);
        (postorder, lam_scopes)
    }

    /// Which keys become a binding: repeated ones, plus deterministic cut
    /// points so a long single-use chain stays bounded.
    fn scoped_share_candidates(
        &self,
        root: ExprId,
        postorder: &[ShareKey],
        lam_scopes: &HashSet<ScopeId>,
        at_consts: &BTreeSet<NameId>,
    ) -> HashSet<ShareKey> {
        let mut occurrences: HashMap<ShareKey, u64> = HashMap::with_capacity(postorder.len());
        occurrences.insert((root, ROOT_SCOPE), 1);
        for key in postorder.iter().rev() {
            let count = occurrences.get(key).copied().unwrap_or_default();
            if count == 0 {
                continue;
            }
            for child in self.share_children(*key) {
                let current = occurrences.get(&child).copied().unwrap_or_default();
                occurrences.insert(child, current.saturating_add(count));
            }
        }

        let mut tree_sizes: HashMap<ShareKey, u64> = HashMap::with_capacity(postorder.len());
        for key in postorder {
            let mut size = 1_u64;
            for child in self.share_children(*key) {
                size = size.saturating_add(tree_sizes.get(&child).copied().unwrap_or(1));
            }
            tree_sizes.insert(*key, size);
        }

        let shareable = |key: ShareKey| -> bool {
            (key.1 == ROOT_SCOPE || lam_scopes.contains(&key.1))
                && !self.has_fvars(key.0)
                && matches!(
                    self.expr_node(key.0),
                    ExprNode::App(_, _)
                        | ExprNode::Proj(..)
                        | ExprNode::Lam(..)
                        | ExprNode::Pi(..)
                        | ExprNode::Let(..)
                )
                && !self.hoisting_exposes_implicit_binders(key.0, at_consts)
        };

        let mut selected: HashSet<ShareKey> = postorder
            .iter()
            .copied()
            .filter(|&key| {
                occurrences.get(&key).copied().unwrap_or_default() >= 2
                    && tree_sizes.get(&key).copied().unwrap_or_default()
                        >= COMPACT_SHARE_MIN_TREE_NODES
                    && shareable(key)
            })
            .collect();
        drop(occurrences);
        drop(tree_sizes);

        // Deterministic cut points, so a long single-use chain stays bounded
        // even when nothing in it repeats (see [`Self::compact_share_plan`]).
        let mut chunk_sizes: HashMap<ShareKey, u64> = HashMap::with_capacity(postorder.len());
        for key in postorder {
            let mut size = 1_u64;
            for child in self.share_children(*key) {
                size = size.saturating_add(chunk_sizes.get(&child).copied().unwrap_or(1));
            }
            if selected.contains(key) || (shareable(*key) && size >= COMPACT_CHUNK_TREE_NODES) {
                selected.insert(*key);
                size = 1;
            }
            chunk_sizes.insert(*key, size);
        }
        drop(chunk_sizes);
        selected
    }

    fn write_lean_without_shares<O: LeanModuleOutput>(
        &self,
        out: &mut O,
        expression: ExprId,
        at_consts: &BTreeSet<NameId>,
    ) {
        let empty = LeanSharePlan::default();
        self.write_lean_with_shares(out, expression, at_consts, ShareView::new(&empty));
    }

    fn write_lean_with_shares<O: LeanModuleOutput>(
        &self,
        out: &mut O,
        expression: ExprId,
        at_consts: &BTreeSet<NameId>,
        view: ShareView<'_>,
    ) {
        let mut binders = Vec::new();
        self.write_expr_with_shares(out, expression, &mut binders, at_consts, view);
    }

    fn write_lean_with_local_shares<O: LeanModuleOutput>(
        &self,
        out: &mut O,
        expression: ExprId,
        at_consts: &BTreeSet<NameId>,
    ) {
        let plan = self.scoped_share_plan(expression, "axeyum_local_expression", at_consts);
        if plan.names.is_empty() {
            self.write_lean_without_shares(out, expression, at_consts);
            return;
        }
        let view = ShareView::new(&plan);
        let mut binders = Vec::new();
        self.write_scope_lets(out, ROOT_SCOPE, &mut binders, at_consts, view);
        self.write_expr_with_shares(out, expression, &mut binders, at_consts, view);
    }

    /// Emit the `let` bindings the plan homes at `scope`, in dependency order.
    ///
    /// Called at the top of the body a binder opens (and once at `ROOT_SCOPE`
    /// for the whole expression), which is exactly where every loose variable
    /// a homed key reads is already bound.
    fn write_scope_lets<O: LeanModuleOutput>(
        &self,
        out: &mut O,
        scope: ScopeId,
        binders: &mut Vec<String>,
        at_consts: &BTreeSet<NameId>,
        view: ShareView<'_>,
    ) {
        let Some(keys) = view.blocks.get(&scope) else {
            return;
        };
        for &key in keys {
            let name = &view.names[&key];
            let _ = write!(out, "let {name} := ");
            self.write_expr_with_shares(out, key.0, binders, at_consts, view.expanding(key));
            let _ = out.write_str("; ");
        }
    }

    fn write_expr_with_shares_atom<O: LeanModuleOutput>(
        &self,
        out: &mut O,
        expression: ExprId,
        binders: &mut Vec<String>,
        at_consts: &BTreeSet<NameId>,
        view: ShareView<'_>,
    ) {
        if let Some(name) = view.lookup(expression) {
            let _ = out.write_str(name);
            return;
        }
        match self.expr_node(expression) {
            ExprNode::BVar(_)
            | ExprNode::FVar(_)
            | ExprNode::Const(_, _)
            | ExprNode::Sort(_)
            | ExprNode::Proj(..)
            | ExprNode::Lit(_) => {
                self.write_expr_with_shares(out, expression, binders, at_consts, view);
            }
            ExprNode::App(_, _) | ExprNode::Lam(..) | ExprNode::Pi(..) | ExprNode::Let(..) => {
                let _ = out.write_char('(');
                self.write_expr_with_shares(out, expression, binders, at_consts, view);
                let _ = out.write_char(')');
            }
        }
    }

    fn write_projection_with_shares<O: LeanModuleOutput>(
        &self,
        out: &mut O,
        structure: ExprId,
        field_index: u32,
        binders: &mut Vec<String>,
        at_consts: &BTreeSet<NameId>,
        view: ShareView<'_>,
    ) {
        let _ = out.write_char('(');
        self.write_expr_with_shares(out, structure, binders, at_consts, view);
        let _ = write!(out, ").{}", u64::from(field_index) + 1);
    }

    fn write_literal<O: LeanModuleOutput>(out: &mut O, literal: &Lit) {
        match literal {
            Lit::Nat(value) => {
                let _ = write!(out, "{value}");
            }
            Lit::Str(value) => {
                let _ = write!(out, "{value:?}");
            }
        }
    }

    fn write_application_with_shares<O: LeanModuleOutput>(
        &self,
        out: &mut O,
        expression: ExprId,
        binders: &mut Vec<String>,
        at_consts: &BTreeSet<NameId>,
        view: ShareView<'_>,
    ) {
        // One flat left-associated spine: see [`Self::app_spine`]. A shared
        // node inside the spine ends it (it prints as its name).
        let (head, arguments) = self.app_spine(expression, |node| view.lookup(node).is_some());
        self.write_expr_with_shares_atom(out, head, binders, at_consts, view);
        for argument in arguments {
            let _ = out.write_char(' ');
            self.write_expr_with_shares_atom(out, argument, binders, at_consts, view);
        }
    }

    fn write_expr_with_shares<O: LeanModuleOutput>(
        &self,
        out: &mut O,
        expression: ExprId,
        binders: &mut Vec<String>,
        at_consts: &BTreeSet<NameId>,
        view: ShareView<'_>,
    ) {
        if let Some(name) = view.lookup(expression) {
            let _ = out.write_str(name);
            return;
        }
        match self.expr_node(expression) {
            ExprNode::BVar(index) => {
                if let Some(position) = binders.len().checked_sub(1 + *index as usize) {
                    let _ = out.write_str(&binders[position]);
                } else {
                    let _ = write!(out, "#{index}");
                }
            }
            ExprNode::FVar(id) => {
                let _ = write!(out, "_fvar.{id}");
            }
            ExprNode::Sort(level) => {
                let rendered = self.render_level(*level);
                if rendered == "0" {
                    let _ = out.write_str("Prop");
                } else {
                    let _ = write!(out, "Sort ({rendered})");
                }
            }
            ExprNode::Const(name, levels) => {
                let at = if at_consts.contains(name) { "@" } else { "" };
                let _ = write!(out, "{at}{}", self.render_name(*name));
                if !levels.is_empty() {
                    let levels = levels
                        .iter()
                        .map(|level| self.render_level(*level))
                        .collect::<Vec<_>>();
                    let _ = write!(out, ".{{{}}}", levels.join(", "));
                }
            }
            ExprNode::Proj(_, field_index, structure) => {
                self.write_projection_with_shares(
                    out,
                    *structure,
                    *field_index,
                    binders,
                    at_consts,
                    view,
                );
            }
            ExprNode::App(_, _) => {
                self.write_application_with_shares(out, expression, binders, at_consts, view);
            }
            ExprNode::Lam(name, ty, body, _) => {
                let binder = self.binder_name(*name, binders.len());
                let _ = write!(out, "fun ({binder} : ");
                self.write_expr_with_shares(out, *ty, binders, at_consts, view);
                let _ = out.write_str(") => ");
                binders.push(binder.clone());
                let inner = view.at(self.body_scope(expression, view.scope));
                self.write_scope_lets(out, inner.scope, binders, at_consts, inner);
                self.write_expr_with_shares(out, *body, binders, at_consts, inner);
                binders.pop();
            }
            ExprNode::Pi(name, ty, body, _) => {
                let binder = self.binder_name(*name, binders.len());
                let _ = write!(out, "(({binder} : ");
                self.write_expr_with_shares(out, *ty, binders, at_consts, view);
                let _ = out.write_str(") -> ");
                binders.push(binder.clone());
                let inner = view.at(self.body_scope(expression, view.scope));
                self.write_expr_with_shares(out, *body, binders, at_consts, inner);
                binders.pop();
                let _ = out.write_char(')');
            }
            ExprNode::Let(name, ty, value, body) => {
                let binder = self.binder_name(*name, binders.len());
                let _ = write!(out, "let {binder} : ");
                self.write_expr_with_shares(out, *ty, binders, at_consts, view);
                let _ = out.write_str(" := ");
                self.write_expr_with_shares(out, *value, binders, at_consts, view);
                let _ = out.write_str("; ");
                binders.push(binder.clone());
                let inner = view.at(self.body_scope(expression, view.scope));
                self.write_expr_with_shares(out, *body, binders, at_consts, inner);
                binders.pop();
            }
            ExprNode::Lit(literal) => Self::write_literal(out, literal),
        }
    }

    /// Render an expression, wrapping it in parentheses when it is a compound form
    /// (so it can sit as a function head or argument without re-association).
    fn render_expr_atom(
        &self,
        id: ExprId,
        binders: &mut Vec<String>,
        at_consts: &std::collections::BTreeSet<NameId>,
        locals: &std::collections::BTreeSet<NameId>,
    ) -> String {
        match self.expr_node(id) {
            ExprNode::BVar(_)
            | ExprNode::FVar(_)
            | ExprNode::Const(_, _)
            | ExprNode::Sort(_)
            | ExprNode::Proj(..)
            | ExprNode::Lit(_) => self.render_expr(id, binders, at_consts, locals),
            ExprNode::App(_, _) | ExprNode::Lam(..) | ExprNode::Pi(..) | ExprNode::Let(..) => {
                format!("({})", self.render_expr(id, binders, at_consts, locals))
            }
        }
    }

    /// The head and (outermost-last) arguments of an application spine.
    ///
    /// Lean's elaborator inserts a constant's *implicit* arguments as soon as a
    /// parenthesized application is complete, so `(@Eq.refl α) a` elaborates
    /// `@Eq.refl α`'s pending implicit and then tries to apply a non-function
    /// (measured against Lean 4.30.0: `Unknown constant CoeFun`). Applications
    /// are left-associative, so the same kernel term written flat — `@Eq.refl α a`
    /// — is accepted. Every application is therefore printed as one flat spine.
    fn app_spine(
        &self,
        expression: ExprId,
        stop: impl Fn(ExprId) -> bool,
    ) -> (ExprId, Vec<ExprId>) {
        let mut arguments = Vec::new();
        let mut head = expression;
        while let ExprNode::App(function, argument) = self.expr_node(head) {
            arguments.push(*argument);
            head = *function;
            if stop(head) {
                break;
            }
        }
        arguments.reverse();
        (head, arguments)
    }

    fn render_expr(
        &self,
        id: ExprId,
        binders: &mut Vec<String>,
        at_consts: &std::collections::BTreeSet<NameId>,
        locals: &std::collections::BTreeSet<NameId>,
    ) -> String {
        match self.expr_node(id) {
            ExprNode::BVar(i) => binders
                .len()
                .checked_sub(1 + *i as usize)
                .map_or_else(|| format!("#{i}"), |k| binders[k].clone()),
            ExprNode::FVar(fid) => format!("_fvar.{fid}"),
            ExprNode::Sort(l) => {
                let ls = self.render_level(*l);
                if ls == "0" {
                    "Prop".to_owned()
                } else {
                    format!("Sort ({ls})")
                }
            }
            ExprNode::Const(name, levels) => {
                // A constant that is a *local* in the command being rendered (an
                // inductive inside its own declaration block) takes neither `@`
                // nor explicit universe arguments.
                if locals.contains(name) {
                    return self.render_name(*name);
                }
                let at = if at_consts.contains(name) { "@" } else { "" };
                let n = format!("{at}{}", self.render_name(*name));
                if levels.is_empty() {
                    n
                } else {
                    let ls: Vec<String> = levels.iter().map(|l| self.render_level(*l)).collect();
                    format!("{n}.{{{}}}", ls.join(", "))
                }
            }
            ExprNode::Proj(_, field_index, structure) => {
                let structure = self.render_expr(*structure, binders, at_consts, locals);
                format!("({structure}).{}", u64::from(*field_index) + 1)
            }
            ExprNode::App(_, _) => {
                let (head, arguments) = self.app_spine(id, |_| false);
                let mut rendered = self.render_expr_atom(head, binders, at_consts, locals);
                for argument in arguments {
                    rendered.push(' ');
                    rendered.push_str(&self.render_expr_atom(argument, binders, at_consts, locals));
                }
                rendered
            }
            ExprNode::Lam(name, ty, body, _) => {
                let bn = self.binder_name(*name, binders.len());
                let tys = self.render_expr(*ty, binders, at_consts, locals);
                binders.push(bn.clone());
                let bs = self.render_expr(*body, binders, at_consts, locals);
                binders.pop();
                format!("fun ({bn} : {tys}) => {bs}")
            }
            ExprNode::Pi(name, ty, body, _) => {
                let bn = self.binder_name(*name, binders.len());
                let tys = self.render_expr(*ty, binders, at_consts, locals);
                binders.push(bn.clone());
                let bs = self.render_expr(*body, binders, at_consts, locals);
                binders.pop();
                format!("(({bn} : {tys}) -> {bs})")
            }
            ExprNode::Let(name, ty, val, body) => {
                let bn = self.binder_name(*name, binders.len());
                let tys = self.render_expr(*ty, binders, at_consts, locals);
                let vs = self.render_expr(*val, binders, at_consts, locals);
                binders.push(bn.clone());
                let bs = self.render_expr(*body, binders, at_consts, locals);
                binders.pop();
                format!("let {bn} : {tys} := {vs}; {bs}")
            }
            ExprNode::Lit(Lit::Nat(n)) => n.to_string(),
            ExprNode::Lit(Lit::Str(s)) => format!("{s:?}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::{ROOT_SCOPE, ScopeId};
    use crate::{ExprId, Kernel};

    /// `fun (p : Prop) => p` renders to readable Lean with the de Bruijn variable
    /// resolved to its binder name, and the round-trip parses structurally.
    #[test]
    fn renders_identity_on_prop() {
        let mut k = Kernel::new();
        let prop = {
            let zero = k.level_zero();
            k.sort(zero)
        };
        let anon = k.anon();
        let p = k.name_str(anon, "p");
        let body = k.bvar(0);
        let lam = k.lam(p, prop, body, crate::BinderInfo::Default);
        assert_eq!(k.render_lean(lam), "fun (p : Prop) => p");
    }

    /// A rendered `inductive` command must come **after** everything its
    /// CONSTRUCTORS mention, not merely after what its own type mentions.
    ///
    /// The renderer writes constructors inline inside the `inductive` block, so a
    /// constructor referring to a definition emitted later produces a module real
    /// Lean rejects with `Unknown constant`. The topological sort used to order
    /// an inductive by `decl_deps`, which for a `Sort 1`-valued family is
    /// *nothing*, and no in-tree kernel test noticed: the whole class is
    /// invisible unless a constructor's type mentions a definition, which the
    /// propositional connectives never do and the constructed ℚ does
    /// (`Rat.mk` mentions `Int.natAbs`).
    ///
    /// This test is deliberately synthetic and cheap. The end-to-end evidence is
    /// `tests/lean_crosscheck.rs`, which feeds the modules to a real `lean` — but
    /// that suite **skips itself** when no `lean` binary is installed, so on most
    /// hosts it proves nothing and this test is the only thing standing here.
    #[test]
    fn an_inductive_is_emitted_after_what_its_constructors_mention() {
        let mut k = Kernel::new();
        let anon = k.anon();
        let prop = k.sort_zero();

        // INTERNED FIRST, on purpose. The topological walk starts from a
        // `BTreeSet<NameId>`, so with the bug present the emitted order still
        // happens to be right whenever the dependency was interned earlier —
        // and the first version of this test proved nothing for exactly that
        // reason. Interning the inductive before the definition it depends on
        // reproduces the real case, where `Rat` is interned by the rational
        // prelude before the `Int.natAbs` that same prelude needs.
        let later = k.name_str(anon, "Later");
        let later_mk = k.name_str(later, "mk");

        // `inductive Seed : Prop | intro : Seed`, so there is something for a
        // definition to be about.
        let seed = k.name_str(anon, "Seed");
        let seed_intro = k.name_str(seed, "intro");
        let seed_ty = k.const_(seed, vec![]);
        k.add_inductive(seed, &[], 0, prop, &[(seed_intro, seed_ty)])
            .expect("Seed admits");

        // `def Marker : Prop := Seed` — a DEFINITION, which is what an
        // inductive's own type can never depend on.
        let marker = k.name_str(anon, "Marker");
        let marker_value = k.const_(seed, vec![]);
        k.add_declaration(crate::Declaration::Definition {
            name: marker,
            uparams: vec![],
            ty: prop,
            value: marker_value,
            hint: crate::ReducibilityHint::Regular(0),
        })
        .expect("Marker admits");

        // `inductive Later : Prop | mk : Marker -> Later`. Its own type is
        // `Prop`; only the CONSTRUCTOR mentions `Marker`.
        let later_ty = k.const_(later, vec![]);
        let marker_const = k.const_(marker, vec![]);
        let mk_ty = {
            let hole = k.name_str(anon, "x");
            k.pi(hole, marker_const, later_ty, crate::BinderInfo::Default)
        };
        k.add_inductive(later, &[], 0, prop, &[(later_mk, mk_ty)])
            .expect("Later admits");

        // A goal/proof pair reaching `Later` through its constructor.
        let goal = k.const_(later, vec![]);
        let proof = {
            let mk = k.const_(later_mk, vec![]);
            let seed_proof = k.const_(seed_intro, vec![]);
            k.app(mk, seed_proof)
        };
        let source = k.render_lean_module("probe", goal, proof);

        let marker_at = source
            .find("def Marker")
            .expect("the definition must be emitted");
        let later_at = source
            .find("inductive Later")
            .expect("the inductive must be emitted");
        assert!(
            marker_at < later_at,
            "`inductive Later` is emitted at byte {later_at} but its constructor \
             mentions `Marker`, emitted at byte {marker_at} -- Lean reads a module \
             top to bottom and rejects the forward reference:\n{source}"
        );
    }

    /// A constant that only a rendered constructor mentions must still be
    /// **emitted**, not merely ordered.
    ///
    /// The sibling test above covers the ordering half of the fix; this covers
    /// the reachability half, and the two are independent. Here the proof never
    /// touches the constructor, so nothing else in the module pulls its
    /// dependency in — yet the `inductive` block writes the constructor's type
    /// out regardless, and a module naming a constant it never declares is one
    /// Lean rejects.
    #[test]
    fn a_constant_only_a_constructor_mentions_is_still_emitted() {
        let mut k = Kernel::new();
        let anon = k.anon();
        let prop = k.sort_zero();

        let seed = k.name_str(anon, "Seed");
        let seed_intro = k.name_str(seed, "intro");
        let seed_ty = k.const_(seed, vec![]);
        k.add_inductive(seed, &[], 0, prop, &[(seed_intro, seed_ty)])
            .expect("Seed admits");

        let marker = k.name_str(anon, "Marker");
        let marker_value = k.const_(seed, vec![]);
        k.add_declaration(crate::Declaration::Definition {
            name: marker,
            uparams: vec![],
            ty: prop,
            value: marker_value,
            hint: crate::ReducibilityHint::Regular(0),
        })
        .expect("Marker admits");

        let later = k.name_str(anon, "Later");
        let later_mk = k.name_str(later, "mk");
        let later_ty = k.const_(later, vec![]);
        let marker_const = k.const_(marker, vec![]);
        let mk_ty = {
            let hole = k.name_str(anon, "x");
            k.pi(hole, marker_const, later_ty, crate::BinderInfo::Default)
        };
        k.add_inductive(later, &[], 0, prop, &[(later_mk, mk_ty)])
            .expect("Later admits");

        // The proof is an OPAQUE inhabitant, so `Later.mk` -- and therefore
        // `Marker` -- is reachable only through the inductive block itself.
        let witness = k.name_str(anon, "witness");
        let goal = k.const_(later, vec![]);
        k.add_declaration(crate::Declaration::Axiom {
            name: witness,
            uparams: vec![],
            ty: goal,
        })
        .expect("witness admits");
        let proof = k.const_(witness, vec![]);

        let source = k.render_lean_module("probe", goal, proof);
        assert!(
            source.contains("inductive Later"),
            "the inductive under test was not emitted at all:\n{source}"
        );
        assert!(
            source.contains("def Marker"),
            "`inductive Later`'s constructor mentions `Marker`, which the module \
             never declares -- Lean rejects it with `Unknown constant`:\n{source}"
        );
    }

    /// Core projections use Lean's 1-based field-index surface syntax while
    /// retaining the 0-based index in the interned node. Both the ordinary and
    /// streaming renderers must make the same conversion, and dependency/DAG
    /// traversal must retain the structure type and structure-valued child.
    #[test]
    fn renders_and_traverses_projection() {
        let mut k = Kernel::new();
        let anon = k.anon();
        let pair = k.name_str(anon, "Pair");
        let self_name = k.name_str(anon, "self");
        let prop = k.sort_zero();
        let self_value = k.bvar(0);
        let second = k.proj(pair, 1, self_value);
        let projection = k.lam(self_name, prop, second, crate::BinderInfo::Default);

        assert_eq!(k.render_lean(projection), "fun (self : Prop) => (self).2");
        let mut streamed = String::new();
        k.write_lean_without_shares(
            &mut streamed,
            projection,
            &std::collections::BTreeSet::new(),
        );
        assert_eq!(streamed, "fun (self : Prop) => (self).2");

        let source_name = k.name_str(anon, "source");
        let source = k.const_(source_name, vec![]);
        let root = k.proj(pair, 0, source);
        let mut dependencies = Vec::new();
        k.collect_const_deps(root, &mut dependencies);
        assert_eq!(dependencies, [pair, source_name]);
        assert_eq!(k.expr_postorder(&[root]), [source, root]);
    }

    /// A `Pi` (dependent arrow) and a nested application render with the binder name
    /// and parenthesized argument.
    #[test]
    fn renders_pi_and_application() {
        let mut k = Kernel::new();
        let prop = {
            let zero = k.level_zero();
            k.sort(zero)
        };
        let anon = k.anon();
        let a = k.name_str(anon, "a");
        // (a : Prop) -> a
        let body = k.bvar(0);
        let pi = k.pi(a, prop, body, crate::BinderInfo::Default);
        assert_eq!(k.render_lean(pi), "((a : Prop) -> a)");
    }

    /// Declarations render as Lean top-level commands: a plain `axiom`, a
    /// universe-polymorphic `axiom h.{u} : Sort (u)`, and a `theorem` carrying a
    /// proof value.
    #[test]
    fn renders_declarations_as_commands() {
        use crate::Declaration;

        let mut k = Kernel::new();
        let prop = {
            let zero = k.level_zero();
            k.sort(zero)
        };
        let anon = k.anon();
        let h = k.name_str(anon, "h");
        let t = k.name_str(anon, "t");
        let u = k.name_str(anon, "u");

        let ax = Declaration::Axiom {
            name: h,
            uparams: vec![],
            ty: prop,
        };
        assert_eq!(k.render_lean_decl(&ax), "axiom h : Prop");

        let sort_u = {
            let lvl = k.level_param(u);
            k.sort(lvl)
        };
        let ax_poly = Declaration::Axiom {
            name: h,
            uparams: vec![u],
            ty: sort_u,
        };
        assert_eq!(k.render_lean_decl(&ax_poly), "axiom h.{u} : Sort (u)");

        let thm = Declaration::Theorem {
            name: t,
            uparams: vec![],
            ty: prop,
            value: prop,
        };
        assert_eq!(k.render_lean_decl(&thm), "theorem t : Prop :=\n  Prop");
    }

    /// A self-contained module renders the `prelude` header, only the declarations
    /// reachable from the goal/proof (here `False` and the hypothesis axiom — not
    /// the unrelated `And`/`Or`/… prelude inductives), the `theorem`, and the
    /// `#print axioms` audit; every referenced declaration precedes the theorem.
    #[test]
    fn renders_self_contained_module() {
        use crate::{Declaration, build_logic_prelude};

        let mut k = Kernel::new();
        let prelude = build_logic_prelude(&mut k).expect("logic prelude must build");
        let anon = k.anon();
        // axiom h : False, then `theorem g : False := h`.
        let false_const = k.const_(prelude.false_, vec![]);
        let h = k.name_str(anon, "h");
        k.add_declaration(Declaration::Axiom {
            name: h,
            uparams: vec![],
            ty: false_const,
        })
        .expect("h : False admits");
        let proof = k.const_(h, vec![]);

        let module = k.render_lean_module("g", false_const, proof);

        assert!(module.starts_with("-- Auto-generated"), "{module}");
        assert!(module.contains("\nprelude\n"), "{module}");
        // `False` and `h` are reachable and declared. `False` is an inductive, and
        // since `a5975725f` every *reachable* inductive is emitted as a real Lean
        // `inductive` rather than an opaque `axiom` — an axiomatized family has no
        // ι-rule on the Lean side, so Lean's defeq would be strictly weaker than
        // the kernel's. This assertion still read `axiom False : Prop` on HEAD and
        // was the only failing test in this crate.
        assert!(module.contains("inductive False : Prop where"), "{module}");
        assert!(module.contains("axiom h : False"), "{module}");
        // Unrelated prelude inductives are NOT pulled in.
        assert!(!module.contains("axiom And "), "{module}");
        assert!(!module.contains("inductive And "), "{module}");
        // The theorem and audit close the module.
        assert!(module.contains("theorem g : False :=\n  h"), "{module}");
        assert!(module.trim_end().ends_with("#print axioms g"), "{module}");
        // `False` is declared before the theorem that uses it.
        let false_at = module.find("inductive False").unwrap();
        let thm_at = module.find("theorem g").unwrap();
        assert!(
            false_at < thm_at,
            "False must precede the theorem\n{module}"
        );
    }

    #[test]
    fn compact_module_shares_repeated_closed_proof_terms() {
        use crate::{Declaration, build_logic_prelude};

        let mut k = Kernel::new();
        let logic = build_logic_prelude(&mut k).expect("logic prelude must build");
        let anon = k.anon();
        let prop = k.sort_zero();
        let p_name = k.name_str(anon, "P");
        k.add_declaration(Declaration::Axiom {
            name: p_name,
            uparams: Vec::new(),
            ty: prop,
        })
        .unwrap();
        let p = k.const_(p_name, Vec::new());
        let h_name = k.name_str(anon, "h");
        k.add_declaration(Declaration::Axiom {
            name: h_name,
            uparams: Vec::new(),
            ty: p,
        })
        .unwrap();
        let h = k.const_(h_name, Vec::new());

        let and = k.const_(logic.and, Vec::new());
        let pair_prop = {
            let expression = k.app(and, p);
            k.app(expression, p)
        };
        let pair = {
            let intro = k.const_(logic.and_intro, Vec::new());
            let expression = k.app(intro, p);
            let expression = k.app(expression, p);
            let expression = k.app(expression, h);
            k.app(expression, h)
        };
        let goal = {
            let expression = k.app(and, pair_prop);
            k.app(expression, pair_prop)
        };
        let proof = {
            let intro = k.const_(logic.and_intro, Vec::new());
            let expression = k.app(intro, pair_prop);
            let expression = k.app(expression, pair_prop);
            let expression = k.app(expression, pair);
            k.app(expression, pair)
        };
        let inferred = k.infer(proof).unwrap();
        assert!(k.def_eq(inferred, goal));

        let ordinary = k.render_lean_module("closed_pair", goal, proof);
        let compact = k.render_lean_module_compact("closed_pair", goal, proof);
        assert!(
            compact.contains("def axeyum_proof_share_0 :=\n"),
            "{compact}"
        );
        // One flat left-associated spine, not `(((f a) b) c) d`: a parenthesized
        // partial application makes Lean insert a constant's pending implicit
        // arguments early (see [`Kernel::app_spine`]).
        let repeated = "And.intro P P h h";
        assert_eq!(ordinary.matches(repeated).count(), 2, "{ordinary}");
        assert_eq!(compact.matches(repeated).count(), 1, "{compact}");
        assert_eq!(
            compact,
            k.render_lean_module_compact("closed_pair", goal, proof)
        );
        assert_eq!(ordinary, k.render_lean_module("closed_pair", goal, proof));

        let arena_lengths = (k.names.len(), k.levels.len(), k.exprs.len());
        assert!(!k.name_intern.is_empty());
        assert!(!k.level_intern.is_empty());
        assert!(!k.expr_intern.is_empty());
        k.release_transient_tables_for_export();
        assert_eq!(
            arena_lengths,
            (k.names.len(), k.levels.len(), k.exprs.len())
        );
        assert!(k.name_intern.is_empty());
        assert!(k.level_intern.is_empty());
        assert!(k.expr_intern.is_empty());
        assert!(k.infer_closed_cache.is_empty());
        assert!(k.whnf_cache.1.is_empty());
        assert_eq!(
            compact,
            k.render_lean_module_compact("closed_pair", goal, proof)
        );
        let mut streamed = Vec::new();
        k.write_lean_module_compact_with_inductives(&mut streamed, "closed_pair", goal, proof, &[])
            .unwrap();
        assert_eq!(compact.as_bytes(), streamed);
    }

    #[test]
    fn streaming_module_output_propagates_writer_failure() {
        struct AlwaysFails;

        impl std::io::Write for AlwaysFails {
            fn write(&mut self, _buffer: &[u8]) -> std::io::Result<usize> {
                Err(std::io::Error::other("expected writer failure"))
            }

            fn flush(&mut self) -> std::io::Result<()> {
                Ok(())
            }
        }

        let mut k = Kernel::new();
        let expression = k.sort_zero();
        let error = k
            .write_lean_module_compact_with_inductives(
                &mut AlwaysFails,
                "writer_failure",
                expression,
                expression,
                &[],
            )
            .unwrap_err();
        assert_eq!(error.kind(), std::io::ErrorKind::Other);
    }

    #[test]
    fn compact_module_chunks_large_declaration_types_locally() {
        use crate::{Declaration, build_logic_prelude};

        let mut k = Kernel::new();
        let logic = build_logic_prelude(&mut k).expect("logic prelude must build");
        let anon = k.anon();
        let prop = k.sort_zero();
        let p_name = k.name_str(anon, "P");
        k.add_declaration(Declaration::Axiom {
            name: p_name,
            uparams: Vec::new(),
            ty: prop,
        })
        .unwrap();
        let p = k.const_(p_name, Vec::new());
        let and = k.const_(logic.and, Vec::new());
        let mut goal = p;
        for _ in 0..300 {
            let applied = k.app(and, p);
            goal = k.app(applied, goal);
        }
        let h_name = k.name_str(anon, "h");
        k.add_declaration(Declaration::Axiom {
            name: h_name,
            uparams: Vec::new(),
            ty: goal,
        })
        .unwrap();
        let proof = k.const_(h_name, Vec::new());

        let module = k.render_lean_module_compact("large_axiom", goal, proof);
        assert!(
            module.contains("axiom h : let _s"),
            "large declaration types must retain DAG chunks in their own scope"
        );
        assert!(module.contains("theorem large_axiom"));
        assert_eq!(
            module,
            k.render_lean_module_compact("large_axiom", goal, proof)
        );
    }

    #[test]
    fn compact_plan_never_hoists_open_binder_dependent_terms() {
        use crate::{BinderInfo, Declaration, build_logic_prelude};

        let mut k = Kernel::new();
        let logic = build_logic_prelude(&mut k).expect("logic prelude must build");
        let anon = k.anon();
        let prop = k.sort_zero();
        let function_ty = k.pi(anon, prop, prop, BinderInfo::Default);
        let function_name = k.name_str(anon, "F");
        k.add_declaration(Declaration::Axiom {
            name: function_name,
            uparams: Vec::new(),
            ty: function_ty,
        })
        .unwrap();
        let function = k.const_(function_name, Vec::new());
        let bound = k.bvar(0);
        let once = k.app(function, bound);
        let repeated_open = k.app(function, once);
        let and = k.const_(logic.and, Vec::new());
        let body = {
            let expression = k.app(and, repeated_open);
            k.app(expression, repeated_open)
        };
        let lambda = k.lam(anon, prop, body, BinderInfo::Default);
        assert_eq!(k.num_loose_bvars(repeated_open), 1);

        let plan = k.compact_share_plan(&[lambda], "open_term", &BTreeSet::new());
        assert!(plan.names.is_empty(), "open terms must not be hoisted");
    }

    /// A `F (F … #0)` chain repeated inside one lambda, plus the pieces every
    /// scoped-sharing test needs.
    #[cfg(test)]
    fn open_chain_fixture(chain: usize) -> (Kernel, ExprId, ExprId, ExprId) {
        use crate::{BinderInfo, Declaration, build_logic_prelude};

        let mut k = Kernel::new();
        let logic = build_logic_prelude(&mut k).expect("logic prelude must build");
        let anon = k.anon();
        let prop = k.sort_zero();
        let function_ty = k.pi(anon, prop, prop, BinderInfo::Default);
        let function_name = k.name_str(anon, "F");
        k.add_declaration(Declaration::Axiom {
            name: function_name,
            uparams: Vec::new(),
            ty: function_ty,
        })
        .unwrap();
        let function = k.const_(function_name, Vec::new());
        let mut open = k.bvar(0);
        for _ in 0..chain {
            open = k.app(function, open);
        }
        let and = k.const_(logic.and, Vec::new());
        let repeated = {
            let expression = k.app(and, open);
            k.app(expression, open)
        };
        (k, repeated, prop, and)
    }

    /// The saving this whole scheme exists for: a repeated **open** term is
    /// shared, and its binding sits inside the binder that binds its loose
    /// variable rather than being hoisted out of it.
    #[test]
    fn scoped_plan_shares_open_terms_inside_the_binder_that_binds_them() {
        use crate::BinderInfo;

        let (mut k, repeated, prop, _and) = open_chain_fixture(8);
        let anon = k.anon();
        let lambda = k.lam(anon, prop, repeated, BinderInfo::Default);

        let plan = k.scoped_share_plan(lambda, "scoped", &BTreeSet::new());
        assert!(
            !plan.names.is_empty(),
            "a repeated open term must be shared: that is the entire point"
        );
        for &(expression, scope) in plan.names.keys() {
            assert!(
                scope != ROOT_SCOPE || k.num_loose_bvars(expression) == 0,
                "an OPEN term keyed at the root scope would be bound outside \
                 the binder that binds it"
            );
        }
        // The top-level `def` planner must still refuse it -- a `def` has no
        // enclosing binder to read the loose variable in.
        assert!(
            k.compact_share_plan(&[lambda], "scoped", &BTreeSet::new())
                .names
                .is_empty()
        );
    }

    /// The soundness guard. One hash-consed open node under **two different
    /// binders** is two different terms, so it must be bound twice, once in
    /// each scope. Keying shares by node alone would bind it once, outside
    /// both, and silently change what the module says.
    #[test]
    fn one_open_node_under_two_binders_is_bound_once_per_binder() {
        use crate::BinderInfo;

        let (mut k, repeated, prop, and) = open_chain_fixture(8);
        let anon = k.anon();
        let x = k.name_str(anon, "x");
        let y = k.name_str(anon, "y");
        // Two distinct lambda NODES over one shared body node.
        let first = k.lam(x, prop, repeated, BinderInfo::Default);
        let second = k.lam(y, prop, repeated, BinderInfo::Default);
        assert_ne!(first, second);
        let root = {
            let expression = k.app(and, first);
            k.app(expression, second)
        };

        let plan = k.scoped_share_plan(root, "two_binders", &BTreeSet::new());
        let scopes: BTreeSet<ScopeId> = plan.names.keys().map(|key| key.1).collect();
        assert_eq!(
            scopes.len(),
            2,
            "the shared body must be bound separately under each binder, got {:?}",
            plan.names
        );
        assert!(!scopes.contains(&ROOT_SCOPE));
    }

    /// `let` is a term form and this writer will not put one inside a type
    /// arrow, so a key homed at a `Pi` body's scope would be referenced by a
    /// name nothing ever binds. The plan must not select it.
    #[test]
    fn a_repeated_term_under_a_pi_binder_is_not_shared() {
        use crate::BinderInfo;

        let (mut k, repeated, prop, _and) = open_chain_fixture(8);
        let anon = k.anon();
        let pi = k.pi(anon, prop, repeated, BinderInfo::Default);

        let plan = k.scoped_share_plan(pi, "pi_body", &BTreeSet::new());
        assert!(
            plan.names.is_empty(),
            "nothing may be homed in a Pi body: no `let` is ever emitted there"
        );
    }

    #[test]
    fn compact_local_share_names_do_not_collide_with_binders() {
        let mut k = Kernel::new();
        let anon = k.anon();
        let binder = k.name_str(anon, "axeyum_proof_share_0");
        let prop = k.sort_zero();
        let mut closed = prop;
        for value in 0..600_u128 {
            let argument = k.lit(crate::Lit::nat(value));
            closed = k.app(closed, argument);
        }
        let body = k.app(closed, closed);
        let lambda = k.lam(binder, prop, body, crate::BinderInfo::Default);

        let plan = k.compact_share_plan(&[lambda], "binder_collision", &BTreeSet::new());
        assert!(!plan.names.is_empty());
        assert!(
            plan.names
                .values()
                .all(|name| name != "axeyum_proof_share_0"),
            "a local share must not be captured by a source binder"
        );
    }

    #[test]
    fn compact_plan_does_not_drop_large_closed_dags() {
        let mut k = Kernel::new();
        let mut chain = k.sort_zero();
        // This deliberately exceeds the former 16,384-share ceiling.  The
        // expression need not be well typed: the sharing planner is a pure
        // serializer pass and must preserve every repeated closed DAG node
        // regardless of the source proof's size.
        for value in 0..16_500_u128 {
            let argument = k.lit(crate::Lit::nat(value));
            chain = k.app(chain, argument);
        }
        let root = k.app(chain, chain);

        let plan = k.compact_share_plan(&[root], "large_closed_dag", &BTreeSet::new());
        assert!(
            plan.names.len() > 16_384,
            "large proof DAGs must not fall back to tree expansion: {} shares",
            plan.names.len()
        );
        assert_eq!(plan.names.len(), plan.order.len());
    }

    #[test]
    fn declaration_dependency_walk_visits_shared_dags_once() {
        use crate::Declaration;

        let mut k = Kernel::new();
        let anon = k.anon();
        let prop = k.sort_zero();
        let p_name = k.name_str(anon, "P");
        k.add_declaration(Declaration::Axiom {
            name: p_name,
            uparams: Vec::new(),
            ty: prop,
        })
        .unwrap();
        let mut shared = k.const_(p_name, Vec::new());
        // Tree walking this 20-level DAG reaches the same leaf 2^20 times.
        // Dependency discovery only needs each interned expression once.
        for _ in 0..20 {
            shared = k.app(shared, shared);
        }

        let mut dependencies = Vec::new();
        k.collect_const_deps(shared, &mut dependencies);
        assert_eq!(dependencies, vec![p_name]);
    }

    #[test]
    fn compact_plan_chunks_single_use_closed_chains() {
        let mut k = Kernel::new();
        let mut chain = k.sort_zero();
        for value in 0..20_000_u128 {
            let argument = k.lit(crate::Lit::nat(value));
            chain = k.app(chain, argument);
        }

        let plan = k.compact_share_plan(&[chain], "single_use_chain", &BTreeSet::new());
        assert!(
            plan.names.len() >= 4,
            "single-use proof chains need bounded serialization chunks: {} shares",
            plan.names.len()
        );
        assert_eq!(plan.names.len(), plan.order.len());
    }

    // ---------------------------------------------------------------------
    // The shared prelude module (`render_lean_prelude_module` +
    // `render_lean_module_compact_importing`).
    // ---------------------------------------------------------------------

    /// A kernel carrying the logical prelude plus a query on top of it: `hna`
    /// refutes `ha`, and the shared development is everything the prelude
    /// builder admitted.
    ///
    /// Returns `(kernel, carrier_names, goal, proof)`. `carrier_names` is the
    /// environment snapshot taken BEFORE the query symbols were admitted — the
    /// definition of "shared" a caller has to supply.
    fn split_fixture() -> (Kernel, Vec<crate::NameId>, ExprId, ExprId) {
        let mut k = Kernel::new();
        let logic = crate::build_logic_prelude(&mut k).expect("logic prelude must build");
        let carrier: Vec<crate::NameId> = k.environment().iter().map(|(n, _)| *n).collect();

        let anon = k.anon();
        let prop = k.sort_zero();
        let false_ = k.const_(logic.false_, vec![]);

        let a_name = k.name_str(anon, "A");
        k.add_declaration(crate::Declaration::Axiom {
            name: a_name,
            uparams: vec![],
            ty: prop,
        })
        .expect("A admits");
        let a = k.const_(a_name, vec![]);

        let ha_name = k.name_str(anon, "ha");
        k.add_declaration(crate::Declaration::Axiom {
            name: ha_name,
            uparams: vec![],
            ty: a,
        })
        .expect("ha admits");

        let not_a = k.pi(anon, a, false_, crate::BinderInfo::Default);
        let refutes = k.name_str(anon, "hna");
        k.add_declaration(crate::Declaration::Axiom {
            name: refutes,
            uparams: vec![],
            ty: not_a,
        })
        .expect("hna admits");

        let ha = k.const_(ha_name, vec![]);
        let hna = k.const_(refutes, vec![]);
        let proof = k.app(hna, ha);
        (k, carrier, false_, proof)
    }

    /// The split is a partition, not a duplication: every declaration the
    /// self-contained module writes out is written by exactly one of the two
    /// halves.
    ///
    /// This is the property that makes the byte saving real rather than a
    /// relabelling, and the property Lean enforces from the other side — a
    /// declaration emitted twice is `has already been declared`.
    #[test]
    fn a_shared_prelude_and_its_query_module_declare_disjoint_names() {
        let (k, carrier, goal, proof) = split_fixture();
        let shared = k.render_lean_prelude_module("AxeyumShared", &carrier);
        let query = k.render_lean_module_compact_importing("q", goal, proof, &[], &shared);

        let declared = |source: &str| -> BTreeSet<String> {
            source
                .lines()
                .filter_map(|line| {
                    let rest = line
                        .strip_prefix("axiom ")
                        .or_else(|| line.strip_prefix("def "))
                        .or_else(|| line.strip_prefix("theorem "))
                        .or_else(|| line.strip_prefix("opaque "))
                        .or_else(|| line.strip_prefix("inductive "))?;
                    Some(rest.split([' ', '.']).next()?.to_owned())
                })
                .collect()
        };
        let shared_names = declared(shared.source());
        let query_names = declared(&query);
        assert!(
            !shared_names.is_empty() && !query_names.is_empty(),
            "both halves must declare something, or the disjointness below is vacuous"
        );
        let both: Vec<&String> = shared_names.intersection(&query_names).collect();
        assert!(
            both.is_empty(),
            "the query module re-declares names the import supplies: {both:?}"
        );
        // The query's OWN symbols are in the query half and nowhere else.
        for symbol in ["A", "ha", "hna"] {
            assert!(
                query_names.contains(symbol),
                "the query module must declare its own `{symbol}`:\n{query}"
            );
        }
        // And the shared half carries the development.
        assert!(
            shared_names.contains("False"),
            "the shared module must carry the logical prelude:\n{}",
            shared.source()
        );
    }

    /// The query module names its import, and only its import, as the source of
    /// the shared development.
    #[test]
    fn a_query_module_imports_the_shared_module_by_name() {
        let (k, carrier, goal, proof) = split_fixture();
        let shared = k.render_lean_prelude_module("AxeyumShared", &carrier);
        let query = k.render_lean_module_compact_importing("q", goal, proof, &[], &shared);

        let prelude_line = query
            .lines()
            .position(|line| line == "prelude")
            .expect("a `prelude` line");
        let import_line = query
            .lines()
            .position(|line| line == "import AxeyumShared")
            .unwrap_or_else(|| panic!("the query module must import the shared module:\n{query}"));
        assert!(
            import_line > prelude_line,
            "Lean requires `prelude` before any `import`:\n{query}"
        );
        // Lean rejects an `import` that follows any other command.
        let first_command = query
            .lines()
            .position(|line| {
                !line.is_empty()
                    && !line.starts_with("--")
                    && line != "prelude"
                    && !line.starts_with("import ")
            })
            .expect("some command");
        assert!(
            import_line < first_command,
            "every `import` must precede every command:\n{query}"
        );
        assert_eq!(shared.file_name(), "AxeyumShared.lean");
        assert!(shared.check_script("/d", "Q.lean").contains("LEAN_PATH=/d"));
    }

    /// Lean's compiler-internal constants are declared exactly ONCE across the
    /// module set. Declaring them in both halves is `has already been declared`;
    /// declaring them in neither is `Unknown constant lcErased` under a
    /// toolchain that runs codegen over a Prop-valued inductive carrying data.
    #[test]
    fn the_codegen_constants_are_declared_in_exactly_one_half() {
        let (k, carrier, goal, proof) = split_fixture();
        let shared = k.render_lean_prelude_module("AxeyumShared", &carrier);
        let query = k.render_lean_module_compact_importing("q", goal, proof, &[], &shared);
        for constant in ["lcErased", "lcAny", "lcVoid"] {
            let declaration = format!("unsafe axiom {constant} : Type");
            assert!(
                shared.source().contains(&declaration),
                "the shared module must declare `{constant}`"
            );
            assert!(
                !query.contains(&declaration),
                "the query module must not RE-declare `{constant}`; Lean rejects that:\n{query}"
            );
        }
    }

    /// The elaborator options are module-scoped in Lean and do NOT travel
    /// through an `import`, so both halves must set them. `maxRecDepth` in
    /// particular: the shared development binds thousands of nested `let`s and
    /// the query module's own theorem term does too.
    #[test]
    fn both_halves_set_the_module_scoped_elaborator_options() {
        let (k, carrier, goal, proof) = split_fixture();
        let shared = k.render_lean_prelude_module("AxeyumShared", &carrier);
        let query = k.render_lean_module_compact_importing("q", goal, proof, &[], &shared);
        for option in ["set_option maxRecDepth 65536", "noncomputable section"] {
            assert!(shared.source().contains(option), "shared module: {option}");
            assert!(query.contains(option), "query module: {option}");
        }
    }

    /// The claim the split is FOR. Everything but the query's own declarations
    /// and its theorem term moves out of the per-query module.
    #[test]
    fn the_query_module_is_much_smaller_than_the_self_contained_one() {
        let (k, carrier, goal, proof) = split_fixture();
        let whole = k.render_lean_module_compact("q", goal, proof);
        let shared = k.render_lean_prelude_module("AxeyumShared", &carrier);
        let query = k.render_lean_module_compact_importing("q", goal, proof, &[], &shared);
        // At this fixture's scale the fixed banner dominates both files, so the
        // measurable claim is that the DEVELOPMENT left the query module, not a
        // ratio. The ratio is measured where the development is large:
        // `examples/shared_prelude_module.rs` on the constructed-real carrier.
        assert!(
            query.len() < whole.len(),
            "whole {} B, query {} B, shared {} B",
            whole.len(),
            query.len(),
            shared.source().len()
        );
        assert!(
            whole.contains("inductive False") && !query.contains("inductive False"),
            "the development must be in the shared half only:\n{query}"
        );
        // The audit command still closes the query module: `#print axioms`
        // traverses imported proofs, so the footprint claim is unmoved.
        assert!(query.trim_end().ends_with("#print axioms q"), "{query}");
    }

    /// A shared module has no theorem and makes no claim; it is a development.
    #[test]
    fn a_shared_prelude_module_states_no_theorem() {
        let (k, carrier, _, _) = split_fixture();
        let shared = k.render_lean_prelude_module("AxeyumShared", &carrier);
        assert!(
            !shared
                .source()
                .lines()
                .any(|line| line.starts_with("#print axioms")),
            "a development module must not carry an audit command"
        );
        assert!(
            !shared.source().contains("\nimport "),
            "the shared module is the root of the import graph"
        );
        assert!(shared.provided_len() > 10, "{}", shared.provided_len());
    }

    /// Rendering is deterministic, which is what makes "emit once, import many"
    /// sound: two contexts built the same way must produce a byte-identical
    /// shared module, or a per-query prelude would be needed after all.
    #[test]
    fn two_identically_built_contexts_render_the_same_shared_module() {
        let (first, first_names, _, _) = split_fixture();
        let (second, second_names, _, _) = split_fixture();
        assert_eq!(
            first
                .render_lean_prelude_module("AxeyumShared", &first_names)
                .source(),
            second
                .render_lean_prelude_module("AxeyumShared", &second_names)
                .source()
        );
    }
}

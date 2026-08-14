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

#[derive(Debug, Default)]
struct LeanSharePlan {
    names: BTreeMap<ExprId, String>,
    order: Vec<ExprId>,
}

trait LeanModuleOutput: std::fmt::Write {
    fn append_owned(&mut self, text: String);
}

impl LeanModuleOutput for String {
    fn append_owned(&mut self, text: String) {
        self.push_str(&text);
    }
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
                "theorem {}{} : {} :=\n  {}",
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

    fn write_lean_module_impl<O: LeanModuleOutput>(
        &self,
        out: &mut O,
        theorem_name: &str,
        goal: ExprId,
        proof: ExprId,
        real_inductives: &[NameId],
        compact: bool,
    ) {
        let order = self.reachable_decl_order(&[goal, proof]);
        let _ = out.write_str(
            "-- Auto-generated by axeyum-lean-kernel: a self-contained re-check of a\n\
             -- reconstructed refutation. `prelude` avoids clashing with Lean core.\n\
             prelude\n\
             set_option linter.unusedVariables false\n\
             -- These declarations are proofs, not programs: a recursor-based `def`\n\
             -- has no compiled code and Lean's code generator declines it\n\
             -- (\"code generator does not support recursor `T.rec` yet\"). The section\n\
             -- suppresses codegen only; it does not weaken type checking.\n\
             noncomputable section\n\n",
        );
        // The constructor/recursor names Lean will auto-generate for the real
        // inductives — emit nothing for them (Lean owns them). The recursor names
        // are also the `@`-application set: Lean makes their `motive` implicit, so
        // the kernel's explicit-motive recursor term must apply them with `@`.
        let mut owned_by_lean: std::collections::BTreeSet<NameId> =
            std::collections::BTreeSet::new();
        let mut at_consts: std::collections::BTreeSet<NameId> = std::collections::BTreeSet::new();
        for &ind in real_inductives {
            if let Some(Declaration::Inductive { ctor_names, .. }) = self.environment().get(ind) {
                for &c in ctor_names {
                    owned_by_lean.insert(c);
                    // Lean makes an inductive's parameters **implicit** in its
                    // constructors regardless of how the parameter binders were
                    // written (`@List.nil : {α : Type u} → List α`). The kernel
                    // term applies them positionally, so every regenerated
                    // constructor must be applied with `@`. For a parameterless
                    // family this is a no-op.
                    at_consts.insert(c);
                }
                let rec = self.name_of_rec(ind);
                owned_by_lean.insert(rec);
                at_consts.insert(rec);
            }
        }
        for name in &order {
            if owned_by_lean.contains(name) {
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
                self.write_decl_command_with_at(out, decl, &at_consts, compact);
                let _ = out.write_char('\n');
            }
        }
        let shares = if compact {
            self.compact_share_plan(&[goal, proof], theorem_name)
        } else {
            LeanSharePlan::default()
        };
        for &expression in &shares.order {
            let name = &shares.names[&expression];
            let _ = write!(out, "\ndef {name} :=\n  ");
            self.write_lean_with_shares(
                out,
                expression,
                &at_consts,
                &shares.names,
                Some(expression),
            );
            let _ = out.write_char('\n');
        }
        let _ = write!(out, "\ntheorem {theorem_name} : ");
        if compact {
            self.write_lean_with_shares(out, goal, &at_consts, &shares.names, None);
        } else {
            self.write_lean_without_shares(out, goal, &at_consts);
        }
        let _ = out.write_str(" :=\n  ");
        if compact {
            self.write_lean_with_shares(out, proof, &at_consts, &shares.names, None);
        } else {
            self.write_lean_without_shares(out, proof, &at_consts);
        }
        let _ = write!(out, "\n\n#print axioms {theorem_name}\n");
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
                    "theorem"
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

    /// The environment declarations reachable from `roots` (transitively through
    /// each declaration's type and — for definitions/theorems/opaques — value),
    /// in dependency order (a declaration appears after every declaration it
    /// references). Names not present in the environment are skipped.
    fn reachable_decl_order(&self, roots: &[ExprId]) -> Vec<NameId> {
        // Reachability closure over constant references.
        let mut needed: std::collections::BTreeSet<NameId> = std::collections::BTreeSet::new();
        let mut work: Vec<NameId> = Vec::new();
        let mut seed = Vec::new();
        for &r in roots {
            self.collect_const_deps(r, &mut seed);
        }
        for n in seed {
            if needed.insert(n) {
                work.push(n);
            }
        }
        while let Some(n) = work.pop() {
            for d in self.decl_deps(n) {
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
        for d in self.decl_deps(name) {
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

    fn compact_share_candidates(&self, postorder: &[ExprId], roots: &[ExprId]) -> HashSet<ExprId> {
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
                );
            if selected.contains(&expression) || (shareable && size >= COMPACT_CHUNK_TREE_NODES) {
                selected.insert(expression);
                size = 1;
            }
            chunk_sizes.insert(expression, size);
        }
        drop(chunk_sizes);
        selected
    }

    fn compact_share_plan(&self, roots: &[ExprId], theorem_name: &str) -> LeanSharePlan {
        let postorder = self.expr_postorder(roots);
        let selected = self.compact_share_candidates(&postorder, roots);

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
            names.insert(expression, name);
            order.push(expression);
        }
        LeanSharePlan { names, order }
    }

    fn write_lean_without_shares<O: LeanModuleOutput>(
        &self,
        out: &mut O,
        expression: ExprId,
        at_consts: &BTreeSet<NameId>,
    ) {
        self.write_lean_with_shares(out, expression, at_consts, &BTreeMap::new(), None);
    }

    fn write_lean_with_shares<O: LeanModuleOutput>(
        &self,
        out: &mut O,
        expression: ExprId,
        at_consts: &BTreeSet<NameId>,
        shares: &BTreeMap<ExprId, String>,
        expand_root: Option<ExprId>,
    ) {
        let mut binders = Vec::new();
        self.write_expr_with_shares(
            out,
            expression,
            &mut binders,
            at_consts,
            shares,
            expand_root,
        );
    }

    fn write_lean_with_local_shares<O: LeanModuleOutput>(
        &self,
        out: &mut O,
        expression: ExprId,
        at_consts: &BTreeSet<NameId>,
    ) {
        let shares = self.compact_share_plan(&[expression], "axeyum_local_expression");
        if shares.order.is_empty() {
            self.write_lean_without_shares(out, expression, at_consts);
            return;
        }
        for &shared in &shares.order {
            let name = &shares.names[&shared];
            let _ = write!(out, "let {name} :=\n  ");
            self.write_lean_with_shares(out, shared, at_consts, &shares.names, Some(shared));
            let _ = out.write_str(";\n");
        }
        self.write_lean_with_shares(out, expression, at_consts, &shares.names, None);
    }

    fn write_expr_with_shares_atom<O: LeanModuleOutput>(
        &self,
        out: &mut O,
        expression: ExprId,
        binders: &mut Vec<String>,
        at_consts: &BTreeSet<NameId>,
        shares: &BTreeMap<ExprId, String>,
        expand_root: Option<ExprId>,
    ) {
        if expand_root != Some(expression)
            && let Some(name) = shares.get(&expression)
        {
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
                self.write_expr_with_shares(
                    out,
                    expression,
                    binders,
                    at_consts,
                    shares,
                    expand_root,
                );
            }
            ExprNode::App(_, _) | ExprNode::Lam(..) | ExprNode::Pi(..) | ExprNode::Let(..) => {
                let _ = out.write_char('(');
                self.write_expr_with_shares(
                    out,
                    expression,
                    binders,
                    at_consts,
                    shares,
                    expand_root,
                );
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
        share_state: (&BTreeMap<ExprId, String>, Option<ExprId>),
    ) {
        let (shares, expand_root) = share_state;
        let _ = out.write_char('(');
        self.write_expr_with_shares(out, structure, binders, at_consts, shares, expand_root);
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
        shares: &BTreeMap<ExprId, String>,
        expand_root: Option<ExprId>,
    ) {
        // One flat left-associated spine: see [`Self::app_spine`]. A shared
        // node inside the spine ends it (it prints as its name).
        let (head, arguments) = self.app_spine(expression, |node| {
            expand_root != Some(node) && shares.contains_key(&node)
        });
        self.write_expr_with_shares_atom(out, head, binders, at_consts, shares, expand_root);
        for argument in arguments {
            let _ = out.write_char(' ');
            self.write_expr_with_shares_atom(
                out,
                argument,
                binders,
                at_consts,
                shares,
                expand_root,
            );
        }
    }

    fn write_expr_with_shares<O: LeanModuleOutput>(
        &self,
        out: &mut O,
        expression: ExprId,
        binders: &mut Vec<String>,
        at_consts: &BTreeSet<NameId>,
        shares: &BTreeMap<ExprId, String>,
        expand_root: Option<ExprId>,
    ) {
        if expand_root != Some(expression)
            && let Some(name) = shares.get(&expression)
        {
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
                    (shares, expand_root),
                );
            }
            ExprNode::App(_, _) => {
                self.write_application_with_shares(
                    out,
                    expression,
                    binders,
                    at_consts,
                    shares,
                    expand_root,
                );
            }
            ExprNode::Lam(name, ty, body, _) => {
                let binder = self.binder_name(*name, binders.len());
                let _ = write!(out, "fun ({binder} : ");
                self.write_expr_with_shares(out, *ty, binders, at_consts, shares, expand_root);
                let _ = out.write_str(") => ");
                binders.push(binder.clone());
                self.write_expr_with_shares(out, *body, binders, at_consts, shares, expand_root);
                binders.pop();
            }
            ExprNode::Pi(name, ty, body, _) => {
                let binder = self.binder_name(*name, binders.len());
                let _ = write!(out, "(({binder} : ");
                self.write_expr_with_shares(out, *ty, binders, at_consts, shares, expand_root);
                let _ = out.write_str(") -> ");
                binders.push(binder.clone());
                self.write_expr_with_shares(out, *body, binders, at_consts, shares, expand_root);
                binders.pop();
                let _ = out.write_char(')');
            }
            ExprNode::Let(name, ty, value, body) => {
                let binder = self.binder_name(*name, binders.len());
                let _ = write!(out, "let {binder} : ");
                self.write_expr_with_shares(out, *ty, binders, at_consts, shares, expand_root);
                let _ = out.write_str(" := ");
                self.write_expr_with_shares(out, *value, binders, at_consts, shares, expand_root);
                let _ = out.write_str("; ");
                binders.push(binder.clone());
                self.write_expr_with_shares(out, *body, binders, at_consts, shares, expand_root);
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
    use crate::Kernel;

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
        // `False` and `h` are reachable and declared.
        assert!(module.contains("axiom False : Prop"), "{module}");
        assert!(module.contains("axiom h : False"), "{module}");
        // Unrelated prelude inductives are NOT pulled in.
        assert!(!module.contains("axiom And "), "{module}");
        // The theorem and audit close the module.
        assert!(module.contains("theorem g : False :=\n  h"), "{module}");
        assert!(module.trim_end().ends_with("#print axioms g"), "{module}");
        // `False` is declared before the theorem that uses it.
        let false_at = module.find("axiom False").unwrap();
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
            module.contains("axiom h : let axeyum_proof_share_"),
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

        let plan = k.compact_share_plan(&[lambda], "open_term");
        assert!(plan.names.is_empty(), "open terms must not be hoisted");
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

        let plan = k.compact_share_plan(&[lambda], "binder_collision");
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

        let plan = k.compact_share_plan(&[root], "large_closed_dag");
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

        let plan = k.compact_share_plan(&[chain], "single_use_chain");
        assert!(
            plan.names.len() >= 4,
            "single-use proof chains need bounded serialization chunks: {} shares",
            plan.names.len()
        );
        assert_eq!(plan.names.len(), plan.order.len());
    }
}

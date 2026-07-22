//! In-tree independent Rust Lean kernel for Axeyum (ADR-0036).
//!
//! The north star is Z3 **and Lean** parity: every `unsat`/`valid` result
//! should carry a machine-checkable proof a Lean-grade kernel accepts. This
//! crate contains the term language and de Bruijn machinery, declarations and
//! environments, WHNF reduction, definitional equality, type inference and
//! checking, proof irrelevance, and the admitted inductive/recursor profile.
//! It is not Lean's parser, elaborator, tactic engine, compiler, package system,
//! language server, or mathlib; those are separate compatibility axes documented
//! in the Lean-system roadmap.
//!
//! The semantics are ported from `nanoda_lib` (a faithful Rust reimplementation
//! of the Lean 4 kernel), but adapted to axeyum's idioms: nanoda's
//! lifetime-tagged arena (`Level<'a>`, `ExprPtr<'a>`) is replaced by a
//! `Vec`-backed hash-consing interner returning lifetime-free `Copy` ids
//! ([`NameId`]/[`LevelId`]/[`ExprId`]), mirroring `axeyum-ir`. No `'a` lifetimes
//! leak into public APIs (Hard Rule). The interner is deterministic: ids are
//! assigned in insertion order and no hash-map iteration order is observable.
//!
//! ## Contents
//!
//! - [`NameNode`] — hierarchical names (`Anonymous`/`Str`/`Num`).
//! - [`LevelNode`] — universe levels with `simplify`, `subst`, and the
//!   antisymmetric `leq`/`is_equiv` comparison.
//! - [`ExprNode`] — locally-nameless expressions with de Bruijn
//!   `instantiate`/`abstract`/`lift`, driven by cached loose-bvar / free-var
//!   metadata.
//! - [`Environment`] and [`Declaration`] — the checked declaration environment.
//! - [`LocalContext`] and [`KernelError`] — type checking and explicit declines.
//!
//! ## Example
//!
//! Build the identity lambda `fun x => x` and instantiate its body with a
//! constant, recovering the constant:
//!
//! ```
//! use axeyum_lean_kernel::{BinderInfo, Kernel};
//!
//! let mut k = Kernel::new();
//! let n = k.anon();
//! let ty = k.sort_zero();
//! let body = k.bvar(0); // de Bruijn 0: the bound `x`
//! let id_fn = k.lam(n, ty, body, BinderInfo::Default);
//!
//! // Take the lambda apart and instantiate `body` with a concrete argument.
//! let c_name = k.name_str(n, "c");
//! let c = k.const_(c_name, vec![]);
//! let inner = k.lam_body(id_fn).unwrap();
//! assert_eq!(k.instantiate(inner, &[c]), c);
//! ```

#![forbid(unsafe_code)]

mod arith_prelude;
mod env;
mod expr;
mod inductive;
mod int_prelude;
mod lean_pp;
mod level;
mod name;
mod prelude;
mod string_prelude;
mod tc;

use std::collections::HashMap;
use std::fmt;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::ops::Index;

pub use arith_prelude::{ArithPrelude, build_arith_prelude};
pub use env::{Declaration, Environment, RecRule, ReducibilityHint};
pub use expr::{BinderInfo, ExprId, ExprNode, Lit, NatLit};
pub use inductive::InductiveFamilySpec;
pub use int_prelude::{IntPrelude, build_int_prelude};
pub use level::{LevelId, LevelNode};
pub use name::{NameId, NameNode};
pub use prelude::{
    DatatypeFamily, DatatypeInductive, LogicPrelude, RecField, RecursiveDatatypeFamily,
    build_logic_prelude,
};
pub use string_prelude::{StringPrelude, build_string_prelude};
pub use tc::{KernelError, LocalContext, LocalDecl};

use expr::ExprMeta;

const EXPR_INTERN_SHARDS: usize = 64;
const EXPR_ARENA_CHUNK_CAPACITY: usize = 1 << 18;

/// Dense, index-addressable storage that grows without relocating old entries.
///
/// `ExprId` remains a single monotonically assigned integer; segmentation is an
/// internal allocation detail. Fixed chunks prevent a large proof arena from
/// needing both the old and doubled `Vec` buffers live during growth.
#[derive(Debug)]
struct SegmentedVec<T> {
    chunks: Vec<Vec<T>>,
    len: usize,
}

impl<T> Default for SegmentedVec<T> {
    fn default() -> Self {
        Self {
            chunks: Vec::new(),
            len: 0,
        }
    }
}

impl<T> SegmentedVec<T> {
    fn len(&self) -> usize {
        self.len
    }

    fn push(&mut self, value: T) {
        if self.len.is_multiple_of(EXPR_ARENA_CHUNK_CAPACITY) {
            self.chunks
                .push(Vec::with_capacity(EXPR_ARENA_CHUNK_CAPACITY));
        }
        self.chunks
            .last_mut()
            .expect("an arena chunk exists after allocation")
            .push(value);
        self.len += 1;
    }

    fn get(&self, index: usize) -> Option<&T> {
        if index >= self.len {
            return None;
        }
        self.chunks
            .get(index / EXPR_ARENA_CHUNK_CAPACITY)
            .and_then(|chunk| chunk.get(index % EXPR_ARENA_CHUNK_CAPACITY))
    }
}

impl<T> Index<usize> for SegmentedVec<T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        self.get(index)
            .expect("segmented arena index out of bounds")
    }
}

/// Hash-consing lookup split into independently growing tables.
///
/// Large generated proofs can carry tens of millions of expression nodes. A
/// single `HashMap` then needs an old+new multi-gigabyte bucket allocation while
/// growing, even though the steady-state table fits the configured memory cap.
/// Sharding preserves the same insertion-ordered `ExprId` assignment while
/// bounding any one table growth to roughly `1 / EXPR_INTERN_SHARDS` of the
/// complete interner. The stable shard hash is not observable in output.
#[derive(Debug)]
struct ExprInterner {
    shards: Vec<HashMap<u64, ExprId>>,
    collisions: HashMap<u64, Vec<ExprId>>,
}

impl Default for ExprInterner {
    fn default() -> Self {
        Self {
            shards: (0..EXPR_INTERN_SHARDS).map(|_| HashMap::new()).collect(),
            collisions: HashMap::new(),
        }
    }
}

impl ExprInterner {
    fn hash(node: &ExprNode) -> u64 {
        let mut hasher = DefaultHasher::new();
        node.hash(&mut hasher);
        hasher.finish()
    }

    fn shard(hash: u64) -> usize {
        usize::try_from(hash % EXPR_INTERN_SHARDS as u64)
            .expect("expression shard index fits usize")
    }

    fn get(&self, node: &ExprNode, arena: &SegmentedVec<ExprNode>) -> Option<ExprId> {
        let hash = Self::hash(node);
        let primary = self.shards[Self::shard(hash)].get(&hash).copied()?;
        if arena.get(primary.index()) == Some(node) {
            return Some(primary);
        }
        self.collisions.get(&hash).and_then(|ids| {
            ids.iter()
                .copied()
                .find(|id| arena.get(id.index()) == Some(node))
        })
    }

    fn insert_hash(&mut self, hash: u64, id: ExprId) {
        match self.shards[Self::shard(hash)].entry(hash) {
            std::collections::hash_map::Entry::Vacant(entry) => {
                entry.insert(id);
            }
            std::collections::hash_map::Entry::Occupied(_) => {
                self.collisions.entry(hash).or_default().push(id);
            }
        }
    }

    #[cfg(test)]
    fn is_empty(&self) -> bool {
        self.shards.iter().all(HashMap::is_empty) && self.collisions.is_empty()
    }
}

/// The interning arena and term builder for the Lean kernel.
///
/// Owns three hash-consed tables ([`NameNode`], [`LevelNode`], [`ExprNode`]).
/// Structurally equal nodes intern to the same id; ids are dense and assigned in
/// insertion order, so identical construction sequences are reproducible
/// (determinism rule). Handles are lifetime-free `Copy` ids and must not be
/// mixed across kernels.
#[derive(Debug, Default)]
pub struct Kernel {
    names: Vec<NameNode>,
    name_intern: HashMap<NameNode, NameId>,

    levels: Vec<LevelNode>,
    level_intern: HashMap<LevelNode, LevelId>,

    exprs: SegmentedVec<ExprNode>,
    expr_meta: SegmentedVec<ExprMeta>,
    expr_intern: ExprInterner,
    /// Successful inferred types for closed expressions. Closed terms are
    /// independent of the local context, so sharing this cache across recursive
    /// checks avoids exponential re-walks of hash-consed proof DAGs.
    infer_closed_cache: HashMap<ExprId, ExprId>,
    /// Weak-head normal forms keyed by the declaration-environment size. The
    /// revision key prevents a result cached before a definition/recursor is
    /// admitted from suppressing a later valid reduction.
    whnf_cache: HashMap<(ExprId, usize), ExprId>,
    /// One-way guard set after transient tables are released for serialization.
    export_only: bool,

    /// The global declaration environment (ADR-0036, slice 3). Declarations are
    /// admitted only through the type-checked [`Kernel::add_declaration`] gate.
    env: Environment,
}

// ---------------------------------------------------------------------------
// Interner core
// ---------------------------------------------------------------------------

impl Kernel {
    /// Creates an empty kernel.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Release hash-consing and typechecking lookup tables before a final,
    /// read-only export of a large checked proof.
    ///
    /// The dense name/level/expression arenas and declaration environment remain
    /// intact, so renderers observe exactly the same kernel term. Construction or
    /// typechecking that tries to intern a node afterward panics instead of
    /// assigning a duplicate handle.
    ///
    /// # Panics
    ///
    /// After this method, any operation that needs to intern a name, level, or
    /// expression panics. Rendering the retained proof remains valid.
    pub fn release_transient_tables_for_export(&mut self) {
        self.name_intern = HashMap::new();
        self.level_intern = HashMap::new();
        self.expr_intern = ExprInterner::default();
        self.infer_closed_cache = HashMap::new();
        self.whnf_cache = HashMap::new();
        self.export_only = true;
    }

    fn intern_name(&mut self, node: NameNode) -> NameId {
        assert!(
            !self.export_only,
            "kernel was finalized for read-only export"
        );
        if let Some(&id) = self.name_intern.get(&node) {
            return id;
        }
        let id = NameId(u32::try_from(self.names.len()).expect("name count fits u32"));
        self.names.push(node.clone());
        self.name_intern.insert(node, id);
        id
    }

    fn intern_level(&mut self, node: LevelNode) -> LevelId {
        assert!(
            !self.export_only,
            "kernel was finalized for read-only export"
        );
        if let Some(&id) = self.level_intern.get(&node) {
            return id;
        }
        let id = LevelId(u32::try_from(self.levels.len()).expect("level count fits u32"));
        self.levels.push(node.clone());
        self.level_intern.insert(node, id);
        id
    }

    fn intern_expr(&mut self, node: ExprNode) -> ExprId {
        assert!(
            !self.export_only,
            "kernel was finalized for read-only export"
        );
        if let Some(id) = self.expr_intern.get(&node, &self.exprs) {
            return id;
        }
        let meta = self.compute_expr_meta(&node);
        let hash = ExprInterner::hash(&node);
        let id = ExprId(u32::try_from(self.exprs.len()).expect("expr count fits u32"));
        self.exprs.push(node);
        self.expr_meta.push(meta);
        self.expr_intern.insert_hash(hash, id);
        id
    }

    /// The structural node of an interned name.
    ///
    /// # Panics
    ///
    /// Panics if `id` does not belong to this kernel.
    #[must_use]
    pub fn name_node(&self, id: NameId) -> &NameNode {
        &self.names[id.index()]
    }

    /// The structural node of an interned level.
    ///
    /// # Panics
    ///
    /// Panics if `id` does not belong to this kernel.
    #[must_use]
    pub fn level_node(&self, id: LevelId) -> &LevelNode {
        &self.levels[id.index()]
    }

    /// The structural node of an interned expression.
    ///
    /// # Panics
    ///
    /// Panics if `id` does not belong to this kernel.
    #[must_use]
    pub fn expr_node(&self, id: ExprId) -> &ExprNode {
        &self.exprs[id.index()]
    }

    /// A shared reference to the global declaration [`Environment`].
    #[must_use]
    pub fn environment(&self) -> &Environment {
        &self.env
    }
}

// ---------------------------------------------------------------------------
// Name builders
// ---------------------------------------------------------------------------

impl Kernel {
    /// The anonymous (empty) root name.
    pub fn anon(&mut self) -> NameId {
        self.intern_name(NameNode::Anonymous)
    }

    /// Appends string component `s` to `parent`.
    pub fn name_str(&mut self, parent: NameId, s: impl Into<String>) -> NameId {
        self.intern_name(NameNode::Str(parent, s.into()))
    }

    /// Appends numeric component `n` to `parent`.
    pub fn name_num(&mut self, parent: NameId, n: u64) -> NameId {
        self.intern_name(NameNode::Num(parent, n))
    }

    /// A wrapper that renders an interned name in dotted form (`a.b.1`) via
    /// [`fmt::Display`].
    #[must_use]
    pub fn display_name(&self, id: NameId) -> NameDisplay<'_> {
        NameDisplay { kernel: self, id }
    }
}

/// A [`fmt::Display`] adapter for an interned [`NameId`], printing the dotted
/// form (e.g. `a.b.1`). The anonymous name prints as `[anonymous]`.
#[derive(Debug, Clone, Copy)]
pub struct NameDisplay<'k> {
    kernel: &'k Kernel,
    id: NameId,
}

impl fmt::Display for NameDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn go(k: &Kernel, id: NameId, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match k.name_node(id) {
                NameNode::Anonymous => write!(f, "[anonymous]"),
                NameNode::Str(parent, s) => write_component(k, *parent, f, |f| write!(f, "{s}")),
                NameNode::Num(parent, n) => write_component(k, *parent, f, |f| write!(f, "{n}")),
            }
        }

        fn write_component(
            k: &Kernel,
            parent: NameId,
            f: &mut fmt::Formatter<'_>,
            write_self: impl FnOnce(&mut fmt::Formatter<'_>) -> fmt::Result,
        ) -> fmt::Result {
            if matches!(k.name_node(parent), NameNode::Anonymous) {
                write_self(f)
            } else {
                go(k, parent, f)?;
                write!(f, ".")?;
                write_self(f)
            }
        }

        go(self.kernel, self.id, f)
    }
}

// ---------------------------------------------------------------------------
// Level builders
// ---------------------------------------------------------------------------

impl Kernel {
    /// The level `0` (`Zero`).
    pub fn level_zero(&mut self) -> LevelId {
        self.intern_level(LevelNode::Zero)
    }

    /// `Succ l`.
    pub fn level_succ(&mut self, l: LevelId) -> LevelId {
        self.intern_level(LevelNode::Succ(l))
    }

    /// `Max l r`.
    pub fn level_max(&mut self, l: LevelId, r: LevelId) -> LevelId {
        self.intern_level(LevelNode::Max(l, r))
    }

    /// `IMax l r`.
    pub fn level_imax(&mut self, l: LevelId, r: LevelId) -> LevelId {
        self.intern_level(LevelNode::IMax(l, r))
    }

    /// A universe parameter named `name`.
    pub fn level_param(&mut self, name: NameId) -> LevelId {
        self.intern_level(LevelNode::Param(name))
    }

    /// `Succ^n l` — apply `Succ` `n` times to `l`.
    pub fn level_offset(&mut self, mut l: LevelId, n: u64) -> LevelId {
        for _ in 0..n {
            l = self.level_succ(l);
        }
        l
    }

    /// Peels leading `Succ`s, returning the inner level and the count peeled.
    #[must_use]
    pub fn level_succs(&self, mut l: LevelId) -> (LevelId, usize) {
        let mut n = 0;
        while let LevelNode::Succ(pred) = self.level_node(l) {
            l = *pred;
            n += 1;
        }
        (l, n)
    }
}

// ---------------------------------------------------------------------------
// Level operations (ported from nanoda level.rs)
// ---------------------------------------------------------------------------

impl Kernel {
    /// `combining l r` — the smart `Max` constructor used by [`Kernel::simplify`].
    fn combining(&mut self, l: LevelId, r: LevelId) -> LevelId {
        match (self.level_node(l).clone(), self.level_node(r).clone()) {
            (LevelNode::Zero, _) => r,
            (_, LevelNode::Zero) => l,
            (LevelNode::Succ(lp), LevelNode::Succ(rp)) => {
                let pred = self.combining(lp, rp);
                self.level_succ(pred)
            }
            _ => self.level_max(l, r),
        }
    }

    /// Normalize a level to a canonical form. Idempotent: `simplify(simplify l)
    /// == simplify l`.
    pub fn simplify(&mut self, l: LevelId) -> LevelId {
        match self.level_node(l).clone() {
            LevelNode::Zero | LevelNode::Param(_) => l,
            LevelNode::Succ(val) => {
                let val = self.simplify(val);
                self.level_succ(val)
            }
            LevelNode::Max(lhs, rhs) => {
                let lhs = self.simplify(lhs);
                let rhs = self.simplify(rhs);
                self.combining(lhs, rhs)
            }
            LevelNode::IMax(lhs, rhs) => {
                let l_simp = self.simplify(lhs);
                let r_simp = self.simplify(rhs);
                if self.is_definitely_zero(l_simp) || self.is_definitely_one(l_simp) {
                    r_simp
                } else {
                    match self.level_node(r_simp).clone() {
                        LevelNode::Zero => r_simp,
                        LevelNode::Succ(_) => self.combining(l_simp, r_simp),
                        _ => self.level_imax(l_simp, r_simp),
                    }
                }
            }
        }
    }

    /// Syntactic check: is this level literally `Zero`?
    fn is_definitely_zero(&self, l: LevelId) -> bool {
        matches!(self.level_node(l), LevelNode::Zero)
    }

    /// Syntactic check: is this level literally `Succ Zero`?
    fn is_definitely_one(&self, l: LevelId) -> bool {
        match self.level_node(l) {
            LevelNode::Succ(pred) => self.is_definitely_zero(*pred),
            _ => false,
        }
    }

    fn is_param_level(&self, l: LevelId) -> bool {
        matches!(self.level_node(l), LevelNode::Param(_))
    }

    fn is_any_max(&self, l: LevelId) -> bool {
        matches!(self.level_node(l), LevelNode::Max(..) | LevelNode::IMax(..))
    }

    /// Substitute universe parameters in `l` according to `subst`
    /// (`Param(name) -> level`). Parameters not present in `subst` are kept.
    pub fn substitute_level(&mut self, l: LevelId, subst: &[(NameId, LevelId)]) -> LevelId {
        match self.level_node(l).clone() {
            LevelNode::Zero => l,
            LevelNode::Succ(val) => {
                let val = self.substitute_level(val, subst);
                self.level_succ(val)
            }
            LevelNode::Max(lhs, rhs) => {
                let lhs = self.substitute_level(lhs, subst);
                let rhs = self.substitute_level(rhs, subst);
                self.level_max(lhs, rhs)
            }
            LevelNode::IMax(lhs, rhs) => {
                let lhs = self.substitute_level(lhs, subst);
                let rhs = self.substitute_level(rhs, subst);
                self.level_imax(lhs, rhs)
            }
            LevelNode::Param(name) => {
                for &(k, v) in subst {
                    if k == name {
                        return v;
                    }
                }
                l
            }
        }
    }

    /// Substitute universe parameters **inside an expression** `e`, replacing
    /// every `Param` named in `subst` wherever a level appears (`Sort` levels
    /// and `Const` universe arguments). Bound/free variables, literals, and the
    /// term structure are otherwise unchanged.
    ///
    /// This is the expression-level analogue of [`Kernel::substitute_level`],
    /// ported from nanoda's `subst_expr_levels`. It is used for universe
    /// instantiation: a `Const(name, level_args)` instantiates the
    /// declaration's `uparams` with `level_args` by substituting in the
    /// declaration's type (and, when δ-unfolding, its value).
    pub fn substitute_expr_levels(&mut self, e: ExprId, subst: &[(NameId, LevelId)]) -> ExprId {
        let mut memo = HashMap::new();
        self.substitute_expr_levels_aux(e, subst, &mut memo)
    }

    fn substitute_expr_levels_aux(
        &mut self,
        e: ExprId,
        subst: &[(NameId, LevelId)],
        memo: &mut HashMap<ExprId, ExprId>,
    ) -> ExprId {
        if let Some(&substituted) = memo.get(&e) {
            return substituted;
        }
        let substituted = match self.expr_node(e).clone() {
            ExprNode::BVar(_) | ExprNode::FVar(_) | ExprNode::Lit(_) => e,
            ExprNode::Sort(level) => {
                let level = self.substitute_level(level, subst);
                self.sort(level)
            }
            ExprNode::Const(name, levels) => {
                let levels = levels
                    .into_iter()
                    .map(|l| self.substitute_level(l, subst))
                    .collect();
                self.const_(name, levels)
            }
            ExprNode::Proj(type_name, field_index, structure) => {
                let structure = self.substitute_expr_levels_aux(structure, subst, memo);
                self.proj(type_name, field_index, structure)
            }
            ExprNode::App(f, a) => {
                let f = self.substitute_expr_levels_aux(f, subst, memo);
                let a = self.substitute_expr_levels_aux(a, subst, memo);
                self.app(f, a)
            }
            ExprNode::Lam(name, ty, body, info) => {
                let ty = self.substitute_expr_levels_aux(ty, subst, memo);
                let body = self.substitute_expr_levels_aux(body, subst, memo);
                self.lam(name, ty, body, info)
            }
            ExprNode::Pi(name, ty, body, info) => {
                let ty = self.substitute_expr_levels_aux(ty, subst, memo);
                let body = self.substitute_expr_levels_aux(body, subst, memo);
                self.pi(name, ty, body, info)
            }
            ExprNode::Let(name, ty, val, body) => {
                let ty = self.substitute_expr_levels_aux(ty, subst, memo);
                let val = self.substitute_expr_levels_aux(val, subst, memo);
                let body = self.substitute_expr_levels_aux(body, subst, memo);
                self.let_(name, ty, val, body)
            }
        };
        memo.insert(e, substituted);
        substituted
    }

    /// `subst` then `simplify` — the substitution used by `leq_imax_by_cases`.
    fn subst_simp(&mut self, l: LevelId, subst: &[(NameId, LevelId)]) -> LevelId {
        let l = self.substitute_level(l, subst);
        self.simplify(l)
    }

    /// Case split on whether a parameter is zero or non-zero, requiring the
    /// inequality under both substitutions.
    fn leq_imax_by_cases(
        &mut self,
        param: NameId,
        lhs: LevelId,
        rhs: LevelId,
        diff: isize,
    ) -> bool {
        let zero = self.level_zero();
        let param_lvl = self.level_param(param);
        let succ_param = self.level_succ(param_lvl);

        let to_zero = [(param, zero)];
        let to_succ = [(param, succ_param)];

        let lhs_0 = self.subst_simp(lhs, &to_zero);
        let rhs_0 = self.subst_simp(rhs, &to_zero);
        let lhs_s = self.subst_simp(lhs, &to_succ);
        let rhs_s = self.subst_simp(rhs, &to_succ);

        self.leq_core(lhs_0, rhs_0, diff) && self.leq_core(lhs_s, rhs_s, diff)
    }

    /// Core of the `<=` test on simplified levels. `diff` tracks how many more
    /// `Succ`s have been stripped from the right than the left (more positive ⇒
    /// the right side is larger).
    ///
    /// Ported line-for-line from nanoda's `leq_core`.
    fn leq_core(&mut self, l_in: LevelId, r_in: LevelId, diff: isize) -> bool {
        match (self.level_node(l_in).clone(), self.level_node(r_in).clone()) {
            (LevelNode::Zero, _) if diff >= 0 => true,
            (_, LevelNode::Zero) if diff < 0 => false,
            (LevelNode::Param(a), LevelNode::Param(x)) => a == x && diff >= 0,
            (LevelNode::Param(_), LevelNode::Zero) => false,
            (LevelNode::Zero, LevelNode::Param(_)) => diff >= 0,
            (LevelNode::Succ(s), _) => self.leq_core(s, r_in, diff - 1),
            (_, LevelNode::Succ(s)) => self.leq_core(l_in, s, diff + 1),
            (LevelNode::Max(a, b), _) => {
                self.leq_core(a, r_in, diff) && self.leq_core(b, r_in, diff)
            }
            // nanoda has these as two separate arms (Param|Max) and (Zero|Max)
            // with identical bodies; merged here as an or-pattern.
            (LevelNode::Param(_) | LevelNode::Zero, LevelNode::Max(x, y)) => {
                self.leq_core(l_in, x, diff) || self.leq_core(l_in, y, diff)
            }
            (LevelNode::IMax(a, b), LevelNode::IMax(x, y)) if a == x && b == y && diff >= 0 => true,
            (LevelNode::IMax(_, b), _) if self.is_param_level(b) => {
                let LevelNode::Param(p) = self.level_node(b).clone() else {
                    unreachable!()
                };
                self.leq_imax_by_cases(p, l_in, r_in, diff)
            }
            (_, LevelNode::IMax(_, y)) if self.is_param_level(y) => {
                let LevelNode::Param(p) = self.level_node(y).clone() else {
                    unreachable!()
                };
                self.leq_imax_by_cases(p, l_in, r_in, diff)
            }
            (LevelNode::IMax(a, b), _) if self.is_any_max(b) => match self.level_node(b).clone() {
                LevelNode::IMax(x, y) => {
                    let new_lhs = self.level_imax(a, y);
                    let new_rhs = self.level_imax(x, y);
                    let new_max = self.level_max(new_lhs, new_rhs);
                    self.leq_core(new_max, r_in, diff)
                }
                LevelNode::Max(x, y) => {
                    let new_lhs = self.level_imax(a, x);
                    let new_rhs = self.level_imax(a, y);
                    let new_max = self.level_max(new_lhs, new_rhs);
                    let new_max = self.simplify(new_max);
                    self.leq_core(new_max, r_in, diff)
                }
                _ => unreachable!(),
            },
            (_, LevelNode::IMax(x, y)) if self.is_any_max(y) => match self.level_node(y).clone() {
                LevelNode::IMax(j, k) => {
                    let new_lhs = self.level_imax(x, k);
                    let new_rhs = self.level_imax(j, k);
                    let new_max = self.level_max(new_lhs, new_rhs);
                    self.leq_core(l_in, new_max, diff)
                }
                LevelNode::Max(j, k) => {
                    let new_lhs = self.level_imax(x, j);
                    let new_rhs = self.level_imax(x, k);
                    let new_rhs = self.level_max(new_lhs, new_rhs);
                    let new_rhs = self.simplify(new_rhs);
                    self.leq_core(l_in, new_rhs, diff)
                }
                _ => unreachable!(),
            },
            _ => unreachable!("leq_core: unhandled level pair"),
        }
    }

    /// `l <= r` on universe levels (simplifies both, then runs the core
    /// antisymmetric comparison).
    pub fn level_leq(&mut self, l: LevelId, r: LevelId) -> bool {
        let l = self.simplify(l);
        let r = self.simplify(r);
        self.leq_core(l, r, 0)
    }

    /// Antisymmetric equivalence: `l <= r` and `r <= l`.
    pub fn level_is_equiv(&mut self, l: LevelId, r: LevelId) -> bool {
        self.level_leq(l, r) && self.level_leq(r, l)
    }

    /// `l <= 0`, i.e. `l` is provably the zero universe.
    pub fn level_is_zero(&mut self, l: LevelId) -> bool {
        let zero = self.level_zero();
        self.level_leq(l, zero)
    }

    /// `1 <= l`, i.e. `l` is provably non-zero.
    pub fn level_is_nonzero(&mut self, l: LevelId) -> bool {
        let zero = self.level_zero();
        let one = self.level_succ(zero);
        self.level_leq(one, l)
    }
}

// ---------------------------------------------------------------------------
// Expr builders (compute and cache metadata at intern time)
// ---------------------------------------------------------------------------

impl Kernel {
    fn compute_expr_meta(&self, node: &ExprNode) -> ExprMeta {
        match node {
            ExprNode::Sort(_) | ExprNode::Const(..) | ExprNode::Lit(_) => ExprMeta {
                num_loose_bvars: 0,
                has_fvars: false,
            },
            ExprNode::FVar(_) => ExprMeta {
                num_loose_bvars: 0,
                has_fvars: true,
            },
            // A `BVar(i)` is loose relative to its own position; one node above
            // it (under one binder) it has loose-range `i + 1`. Binders below
            // decrement via the binder cases here.
            ExprNode::BVar(i) => ExprMeta {
                num_loose_bvars: i + 1,
                has_fvars: false,
            },
            ExprNode::Proj(_, _, structure) => self.expr_meta[structure.index()],
            ExprNode::App(f, a) => {
                let mf = self.expr_meta[f.index()];
                let ma = self.expr_meta[a.index()];
                ExprMeta {
                    num_loose_bvars: mf.num_loose_bvars.max(ma.num_loose_bvars),
                    has_fvars: mf.has_fvars || ma.has_fvars,
                }
            }
            ExprNode::Lam(_, ty, body, _) | ExprNode::Pi(_, ty, body, _) => {
                let mt = self.expr_meta[ty.index()];
                let mb = self.expr_meta[body.index()];
                // The binder consumes one loose level in `body`.
                let body_loose = mb.num_loose_bvars.saturating_sub(1);
                ExprMeta {
                    num_loose_bvars: mt.num_loose_bvars.max(body_loose),
                    has_fvars: mt.has_fvars || mb.has_fvars,
                }
            }
            ExprNode::Let(_, ty, val, body) => {
                let mt = self.expr_meta[ty.index()];
                let mv = self.expr_meta[val.index()];
                let mb = self.expr_meta[body.index()];
                let body_loose = mb.num_loose_bvars.saturating_sub(1);
                ExprMeta {
                    num_loose_bvars: mt.num_loose_bvars.max(mv.num_loose_bvars).max(body_loose),
                    has_fvars: mt.has_fvars || mv.has_fvars || mb.has_fvars,
                }
            }
        }
    }

    /// A bound variable with de Bruijn index `idx`.
    pub fn bvar(&mut self, idx: u32) -> ExprId {
        self.intern_expr(ExprNode::BVar(idx))
    }

    /// A free/local variable with unique id `id`.
    pub fn fvar(&mut self, id: u64) -> ExprId {
        self.intern_expr(ExprNode::FVar(id))
    }

    /// A type universe `Sort level`.
    pub fn sort(&mut self, level: LevelId) -> ExprId {
        self.intern_expr(ExprNode::Sort(level))
    }

    /// `Sort 0` (i.e. `Prop`).
    pub fn sort_zero(&mut self) -> ExprId {
        let z = self.level_zero();
        self.sort(z)
    }

    /// A constant reference `name.{levels}`.
    pub fn const_(&mut self, name: NameId, levels: Vec<LevelId>) -> ExprId {
        self.intern_expr(ExprNode::Const(name, levels))
    }

    /// Project the zero-based non-parameter field `field_index` from
    /// `structure`, whose inductive structure type is named `type_name`.
    ///
    /// This constructor records Lean's core expression exactly. TL2.3 owns
    /// validation and dependent result-type inference; TL2.4 owns reduction.
    pub fn proj(&mut self, type_name: NameId, field_index: u32, structure: ExprId) -> ExprId {
        self.intern_expr(ExprNode::Proj(type_name, field_index, structure))
    }

    /// Application `fun arg`.
    pub fn app(&mut self, fun: ExprId, arg: ExprId) -> ExprId {
        self.intern_expr(ExprNode::App(fun, arg))
    }

    /// `fun (name : ty) => body`.
    pub fn lam(&mut self, name: NameId, ty: ExprId, body: ExprId, info: BinderInfo) -> ExprId {
        self.intern_expr(ExprNode::Lam(name, ty, body, info))
    }

    /// `(name : ty) -> body`.
    pub fn pi(&mut self, name: NameId, ty: ExprId, body: ExprId, info: BinderInfo) -> ExprId {
        self.intern_expr(ExprNode::Pi(name, ty, body, info))
    }

    /// `let name : ty := val; body`.
    pub fn let_(&mut self, name: NameId, ty: ExprId, val: ExprId, body: ExprId) -> ExprId {
        self.intern_expr(ExprNode::Let(name, ty, val, body))
    }

    /// A literal expression.
    pub fn lit(&mut self, lit: Lit) -> ExprId {
        self.intern_expr(ExprNode::Lit(lit))
    }

    /// The body of a `Lam`, or `None` if `e` is not a lambda.
    #[must_use]
    pub fn lam_body(&self, e: ExprId) -> Option<ExprId> {
        match self.expr_node(e) {
            ExprNode::Lam(_, _, body, _) => Some(*body),
            _ => None,
        }
    }

    /// The body of a `Pi`, or `None` if `e` is not a pi.
    #[must_use]
    pub fn pi_body(&self, e: ExprId) -> Option<ExprId> {
        match self.expr_node(e) {
            ExprNode::Pi(_, _, body, _) => Some(*body),
            _ => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Expr metadata queries
// ---------------------------------------------------------------------------

impl Kernel {
    /// One more than the largest loose de Bruijn index escaping `e` (`0` ⇒
    /// closed). This is nanoda's `num_loose_bvars`.
    #[must_use]
    pub fn num_loose_bvars(&self, e: ExprId) -> u32 {
        self.expr_meta[e.index()].num_loose_bvars
    }

    /// Whether `e` has any loose (escaping) bound variables.
    #[must_use]
    pub fn has_loose_bvars(&self, e: ExprId) -> bool {
        self.num_loose_bvars(e) > 0
    }

    /// The half-open range `0..num_loose_bvars(e)` of loose de Bruijn indices
    /// that may escape `e`.
    #[must_use]
    pub fn loose_bvar_range(&self, e: ExprId) -> std::ops::Range<u32> {
        0..self.num_loose_bvars(e)
    }

    /// Whether any free variable occurs in `e`.
    #[must_use]
    pub fn has_fvars(&self, e: ExprId) -> bool {
        self.expr_meta[e.index()].has_fvars
    }
}

// ---------------------------------------------------------------------------
// De Bruijn operations (ported from nanoda expr.rs)
// ---------------------------------------------------------------------------

impl Kernel {
    /// Replace loose bound variables in `e` with the expressions in `subst`.
    ///
    /// `subst` substitutes the outermost loose bvars: a loose `BVar(offset + i)`
    /// at binder depth `offset` is replaced by `subst[subst.len() - 1 - i]`
    /// (matching nanoda's `substs.iter().rev().nth(i)`), with no shifting of the
    /// substituted terms (they are assumed closed at the substitution site, as
    /// in nanoda's β/ζ reduction usage). A loose index past the end of `subst`
    /// is left unchanged.
    ///
    /// On a closed expression this is the identity.
    pub fn instantiate(&mut self, e: ExprId, subst: &[ExprId]) -> ExprId {
        let mut memo = HashMap::new();
        self.instantiate_aux(e, subst, 0, &mut memo)
    }

    fn instantiate_aux(
        &mut self,
        e: ExprId,
        subst: &[ExprId],
        offset: u32,
        memo: &mut HashMap<(ExprId, u32), ExprId>,
    ) -> ExprId {
        if self.num_loose_bvars(e) <= offset {
            return e;
        }
        if let Some(&instantiated) = memo.get(&(e, offset)) {
            return instantiated;
        }
        let instantiated = match self.expr_node(e).clone() {
            ExprNode::Sort(_) | ExprNode::Const(..) | ExprNode::FVar(_) | ExprNode::Lit(_) => e,
            ExprNode::BVar(idx) => {
                debug_assert!(idx >= offset);
                let i = (idx - offset) as usize;
                subst.iter().rev().nth(i).copied().unwrap_or(e)
            }
            ExprNode::Proj(type_name, field_index, structure) => {
                let structure = self.instantiate_aux(structure, subst, offset, memo);
                self.proj(type_name, field_index, structure)
            }
            ExprNode::App(f, a) => {
                let f = self.instantiate_aux(f, subst, offset, memo);
                let a = self.instantiate_aux(a, subst, offset, memo);
                self.app(f, a)
            }
            ExprNode::Lam(name, ty, body, info) => {
                let ty = self.instantiate_aux(ty, subst, offset, memo);
                let body = self.instantiate_aux(body, subst, offset + 1, memo);
                self.lam(name, ty, body, info)
            }
            ExprNode::Pi(name, ty, body, info) => {
                let ty = self.instantiate_aux(ty, subst, offset, memo);
                let body = self.instantiate_aux(body, subst, offset + 1, memo);
                self.pi(name, ty, body, info)
            }
            ExprNode::Let(name, ty, val, body) => {
                let ty = self.instantiate_aux(ty, subst, offset, memo);
                let val = self.instantiate_aux(val, subst, offset, memo);
                let body = self.instantiate_aux(body, subst, offset + 1, memo);
                self.let_(name, ty, val, body)
            }
        };
        memo.insert((e, offset), instantiated);
        instantiated
    }

    /// Replace the free variables in `fvars` with loose bound variables.
    ///
    /// The inverse of [`Kernel::instantiate`]: when going *under* binders, each
    /// `FVar(fvars[j])` becomes `BVar(offset + (len-1-position))` so that the
    /// last entry of `fvars` (the innermost binder) maps to the lowest index.
    /// This matches nanoda's `abstr`: `locals.iter().rev().position(..)`.
    pub fn abstract_fvars(&mut self, e: ExprId, fvars: &[u64]) -> ExprId {
        if fvars.is_empty() {
            return e;
        }
        let target_presence = self.fvar_target_presence(e, fvars);
        let mut memo = HashMap::new();
        self.abstract_aux(e, fvars, 0, &target_presence, &mut memo)
    }

    fn fvar_target_presence(&self, root: ExprId, targets: &[u64]) -> Vec<u8> {
        const ABSENT: u8 = 1;
        const PRESENT: u8 = 2;

        let mut presence = vec![0_u8; root.index() + 1];
        let mut stack = vec![(root, false)];
        while let Some((expression, visited)) = stack.pop() {
            if presence[expression.index()] != 0 {
                continue;
            }
            if !visited {
                stack.push((expression, true));
                match self.expr_node(expression) {
                    ExprNode::Proj(_, _, structure) => stack.push((*structure, false)),
                    ExprNode::App(function, argument) => {
                        stack.push((*function, false));
                        stack.push((*argument, false));
                    }
                    ExprNode::Lam(_, ty, body, _) | ExprNode::Pi(_, ty, body, _) => {
                        stack.push((*ty, false));
                        stack.push((*body, false));
                    }
                    ExprNode::Let(_, ty, value, body) => {
                        stack.push((*ty, false));
                        stack.push((*value, false));
                        stack.push((*body, false));
                    }
                    ExprNode::BVar(_)
                    | ExprNode::FVar(_)
                    | ExprNode::Sort(_)
                    | ExprNode::Const(..)
                    | ExprNode::Lit(_) => {}
                }
                continue;
            }

            let child_present = |child: ExprId| presence[child.index()] == PRESENT;
            let found = match self.expr_node(expression) {
                ExprNode::FVar(id) => targets.contains(id),
                ExprNode::Proj(_, _, structure) => child_present(*structure),
                ExprNode::App(function, argument) => {
                    child_present(*function) || child_present(*argument)
                }
                ExprNode::Lam(_, ty, body, _) | ExprNode::Pi(_, ty, body, _) => {
                    child_present(*ty) || child_present(*body)
                }
                ExprNode::Let(_, ty, value, body) => {
                    child_present(*ty) || child_present(*value) || child_present(*body)
                }
                ExprNode::BVar(_) | ExprNode::Sort(_) | ExprNode::Const(..) | ExprNode::Lit(_) => {
                    false
                }
            };
            presence[expression.index()] = if found { PRESENT } else { ABSENT };
        }
        presence
    }

    fn abstract_aux(
        &mut self,
        e: ExprId,
        fvars: &[u64],
        offset: u32,
        target_presence: &[u8],
        memo: &mut HashMap<(ExprId, u32), ExprId>,
    ) -> ExprId {
        if target_presence[e.index()] != 2 {
            return e;
        }
        if let Some(&abstracted) = memo.get(&(e, offset)) {
            return abstracted;
        }
        let abstracted = match self.expr_node(e).clone() {
            ExprNode::FVar(id) => match fvars.iter().rev().position(|&x| x == id) {
                Some(pos) => self.bvar(u32::try_from(pos).expect("fvar count fits u32") + offset),
                None => e,
            },
            ExprNode::BVar(_) | ExprNode::Sort(_) | ExprNode::Const(..) | ExprNode::Lit(_) => e,
            ExprNode::Proj(type_name, field_index, structure) => {
                let structure = self.abstract_aux(structure, fvars, offset, target_presence, memo);
                self.proj(type_name, field_index, structure)
            }
            ExprNode::App(f, a) => {
                let f = self.abstract_aux(f, fvars, offset, target_presence, memo);
                let a = self.abstract_aux(a, fvars, offset, target_presence, memo);
                self.app(f, a)
            }
            ExprNode::Lam(name, ty, body, info) => {
                let ty = self.abstract_aux(ty, fvars, offset, target_presence, memo);
                let body = self.abstract_aux(body, fvars, offset + 1, target_presence, memo);
                self.lam(name, ty, body, info)
            }
            ExprNode::Pi(name, ty, body, info) => {
                let ty = self.abstract_aux(ty, fvars, offset, target_presence, memo);
                let body = self.abstract_aux(body, fvars, offset + 1, target_presence, memo);
                self.pi(name, ty, body, info)
            }
            ExprNode::Let(name, ty, val, body) => {
                let ty = self.abstract_aux(ty, fvars, offset, target_presence, memo);
                let val = self.abstract_aux(val, fvars, offset, target_presence, memo);
                let body = self.abstract_aux(body, fvars, offset + 1, target_presence, memo);
                self.let_(name, ty, val, body)
            }
        };
        memo.insert((e, offset), abstracted);
        abstracted
    }

    /// Closes free variables at their explicitly associated lambda nodes in one
    /// shared-DAG traversal.
    ///
    /// Each `(lambda, fvar)` marker says that `fvar` is the local represented by
    /// that lambda. The input may be an open skeleton whose marked lambda bodies
    /// still reference those locals as [`ExprNode::FVar`] nodes. The result
    /// replaces each in-scope marked free variable by the correct de Bruijn index,
    /// including shifts below ordinary unmarked lambdas, pis, and lets. Unmarked
    /// free variables remain free.
    ///
    /// This is equivalent to closing each marked lambda separately with
    /// [`Self::abstract_fvars`], but avoids repeatedly copying a large nested proof
    /// tail once per binder.
    ///
    /// # Panics
    ///
    /// Panics when a marker does not name a lambda, one lambda appears more than
    /// once, or the same free variable is marked in overlapping scopes.
    pub fn close_scoped_fvars(&mut self, e: ExprId, binders: &[(ExprId, u64)]) -> ExprId {
        let mut markers = HashMap::with_capacity(binders.len());
        for &(lambda, fvar) in binders {
            assert!(
                matches!(self.expr_node(lambda), ExprNode::Lam(..)),
                "scoped free-variable marker must name a lambda"
            );
            assert!(
                markers.insert(lambda, fvar).is_none(),
                "a lambda cannot bind two scoped free variables"
            );
        }
        let mut memo = HashMap::new();
        let mut active = HashMap::with_capacity(binders.len());
        let mut scopes = HashMap::with_capacity(binders.len());
        let mut next_scope = 1_usize;
        self.close_scoped_fvars_aux(
            e,
            0,
            0,
            &markers,
            &mut active,
            &mut scopes,
            &mut next_scope,
            &mut memo,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn close_scoped_fvars_aux(
        &mut self,
        e: ExprId,
        depth: u32,
        scope: usize,
        markers: &HashMap<ExprId, u64>,
        active: &mut HashMap<u64, u32>,
        scopes: &mut HashMap<(usize, ExprId), usize>,
        next_scope: &mut usize,
        memo: &mut HashMap<(ExprId, u32, usize), ExprId>,
    ) -> ExprId {
        if !self.has_fvars(e) {
            return e;
        }
        if let Some(&closed) = memo.get(&(e, depth, scope)) {
            return closed;
        }
        let closed = match self.expr_node(e).clone() {
            ExprNode::FVar(id) => active
                .get(&id)
                .map_or(e, |&binder_depth| self.bvar(depth - binder_depth - 1)),
            ExprNode::BVar(_) | ExprNode::Sort(_) | ExprNode::Const(..) | ExprNode::Lit(_) => e,
            ExprNode::Proj(type_name, field_index, structure) => {
                let structure = self.close_scoped_fvars_aux(
                    structure, depth, scope, markers, active, scopes, next_scope, memo,
                );
                self.proj(type_name, field_index, structure)
            }
            ExprNode::App(function, argument) => {
                let function = self.close_scoped_fvars_aux(
                    function, depth, scope, markers, active, scopes, next_scope, memo,
                );
                let argument = self.close_scoped_fvars_aux(
                    argument, depth, scope, markers, active, scopes, next_scope, memo,
                );
                self.app(function, argument)
            }
            ExprNode::Lam(name, ty, body, info) => {
                let ty = self.close_scoped_fvars_aux(
                    ty, depth, scope, markers, active, scopes, next_scope, memo,
                );
                let marker = markers.get(&e).copied();
                let body_scope = if marker.is_some() {
                    *scopes.entry((scope, e)).or_insert_with(|| {
                        let allocated = *next_scope;
                        *next_scope += 1;
                        allocated
                    })
                } else {
                    scope
                };
                if let Some(fvar) = marker {
                    assert!(active.insert(fvar, depth).is_none());
                }
                let body = self.close_scoped_fvars_aux(
                    body,
                    depth + 1,
                    body_scope,
                    markers,
                    active,
                    scopes,
                    next_scope,
                    memo,
                );
                if let Some(fvar) = marker {
                    assert_eq!(active.remove(&fvar), Some(depth));
                }
                self.lam(name, ty, body, info)
            }
            ExprNode::Pi(name, ty, body, info) => {
                let ty = self.close_scoped_fvars_aux(
                    ty, depth, scope, markers, active, scopes, next_scope, memo,
                );
                let body = self.close_scoped_fvars_aux(
                    body,
                    depth + 1,
                    scope,
                    markers,
                    active,
                    scopes,
                    next_scope,
                    memo,
                );
                self.pi(name, ty, body, info)
            }
            ExprNode::Let(name, ty, value, body) => {
                let ty = self.close_scoped_fvars_aux(
                    ty, depth, scope, markers, active, scopes, next_scope, memo,
                );
                let value = self.close_scoped_fvars_aux(
                    value, depth, scope, markers, active, scopes, next_scope, memo,
                );
                let body = self.close_scoped_fvars_aux(
                    body,
                    depth + 1,
                    scope,
                    markers,
                    active,
                    scopes,
                    next_scope,
                    memo,
                );
                self.let_(name, ty, value, body)
            }
        };
        memo.insert((e, depth, scope), closed);
        closed
    }

    /// Shift loose bound variables in `e` by `amount`, only those whose index is
    /// `>= cutoff` (the standard lifting operation used when moving an
    /// expression under `amount` extra binders).
    pub fn lift_loose_bvars(&mut self, e: ExprId, cutoff: u32, amount: u32) -> ExprId {
        if amount == 0 || self.num_loose_bvars(e) <= cutoff {
            return e;
        }
        match self.expr_node(e).clone() {
            ExprNode::BVar(idx) => {
                if idx >= cutoff {
                    self.bvar(idx + amount)
                } else {
                    e
                }
            }
            ExprNode::Sort(_) | ExprNode::Const(..) | ExprNode::FVar(_) | ExprNode::Lit(_) => e,
            ExprNode::Proj(type_name, field_index, structure) => {
                let structure = self.lift_loose_bvars(structure, cutoff, amount);
                self.proj(type_name, field_index, structure)
            }
            ExprNode::App(f, a) => {
                let f = self.lift_loose_bvars(f, cutoff, amount);
                let a = self.lift_loose_bvars(a, cutoff, amount);
                self.app(f, a)
            }
            ExprNode::Lam(name, ty, body, info) => {
                let ty = self.lift_loose_bvars(ty, cutoff, amount);
                let body = self.lift_loose_bvars(body, cutoff + 1, amount);
                self.lam(name, ty, body, info)
            }
            ExprNode::Pi(name, ty, body, info) => {
                let ty = self.lift_loose_bvars(ty, cutoff, amount);
                let body = self.lift_loose_bvars(body, cutoff + 1, amount);
                self.pi(name, ty, body, info)
            }
            ExprNode::Let(name, ty, val, body) => {
                let ty = self.lift_loose_bvars(ty, cutoff, amount);
                let val = self.lift_loose_bvars(val, cutoff, amount);
                let body = self.lift_loose_bvars(body, cutoff + 1, amount);
                self.let_(name, ty, val, body)
            }
        }
    }
}

#[cfg(test)]
mod tests;

//! Adversarial differential soundness fuzzer for the array-of-bit-vectors
//! (`QF_ABV`) sat/unsat decider against the Z3 oracle.
//!
//! Arrays add the read-over-write / extensionality theory on top of the bit-
//! vector core: axeyum decides `QF_ABV` by eager `eliminate_arrays`
//! (read-over-write + Ackermann + extensionality, ADR-0010) down to `QF_BV`,
//! then bit-blasts. A wrong `Unsat` (claiming no model when one exists — e.g. a
//! spurious extensionality collapse) or a wrong `Sat` (a model that does not
//! satisfy the original atoms, or one Z3 refutes) would be the worst possible
//! bug. The same differential pattern recently found four real defects in other
//! fragments.
//!
//! This harness — mirroring the proven `nia_differential_fuzz.rs` /
//! `uflia_differential_fuzz.rs` templates — deterministically generates
//! thousands of small random `QF_ABV` formulas (no `Math::random`/`Date::now`;
//! a fixed-seed LCG drives every choice), decides each with both the default
//! pure-Rust `solve` front door (which auto-dispatches the array path) and a
//! direct Z3 array query over the same declarations and atoms, and gates on the
//! joint verdict:
//!
//! - axeyum `Sat` ∧ Z3 `Unsat` → **PANIC** (wrong sat).
//! - axeyum `Unsat` ∧ Z3 `Sat` → **PANIC** (wrong unsat — the worst bug).
//! - axeyum `Sat` → the returned model (BV variable bindings **and** array
//!   interpretations) is **independently replayed** through the IR ground
//!   evaluator on every original atom; a definitely-non-replaying Sat panics
//!   regardless of Z3. If the evaluator cannot replay an atom (e.g. an array
//!   symbol the model left unbound) the atom is counted replay-INDETERMINATE
//!   and Z3 adjudicates — only a definite `Bool(false)` replay panics.
//! - axeyum `Unknown` is ALLOWED (incomplete is sound) — counted, never failed.
//! - Z3 `Unknown`/timeout → the instance is skipped (cannot adjudicate).
//! - a solver panic is caught (`catch_unwind`) and counted as CRASHED
//!   (adjudication-neutral — a panic is never a verdict, hence never a
//!   mis-verdict); the first repro is recorded and the sweep continues.
//!
//! The test passes iff disagreements == 0 AND no axeyum `Sat` definitely
//! refutes under replay.
//!
//! ## Semantic-safety note
//!
//! Only constructs with *identical* SMT-LIB semantics on both sides are
//! generated:
//! - Arrays `(Array (_ BitVec W) (_ BitVec W))` are SMT-LIB extensional total
//!   maps in both axeyum (ADR-0010) and Z3, so `select`/`store`/array-equality
//!   match verbatim. Index and element widths are kept equal per instance so
//!   every total BV op composes without an explicit width check.
//! - Bit-vector terms over `Sort::BitVec(W)`: variables, constants, and only the
//!   **total, convention-free** ops `bvnot, bvand, bvor, bvxor, bvadd` (whose
//!   axeyum and Z3 semantics are identical). NO `bvudiv`/`bvurem`/`bvsdiv`/
//!   shifts — anything whose totality convention could differ is omitted, so a
//!   verdict mismatch is a real bug, never a false alarm.
//! - Atom relations: element-level `{=, !=, bvult, bvule}` (all four total and
//!   identical on both sides) and **array-level `=` / `!=`** (exercising
//!   extensionality — the classic array-soundness stressor). At least one atom
//!   per instance is forced to touch `select`/`store`/array-equality so the
//!   array theory is genuinely tested.
#![cfg(feature = "full")]
#![cfg(feature = "z3")]

use std::sync::mpsc;
use std::time::Duration;

use axeyum_ir::{ArraySortKey, Sort, SymbolId, TermArena, TermId, Value, eval};
use axeyum_solver::{CheckResult, SolverConfig, solve};
use z3::ast::{Array, BV, Bool};
use z3::{Params, SatResult, Solver, Sort as Z3Sort};

/// Number of instances generated and adjudicated. Each is tiny (≤ 2 arrays, ≤ 3
/// BV vars, ≤ 4 atoms, narrow widths) so Z3 decides well within its timeout.
const INSTANCES: u64 = 2500;

/// Per-instance Z3 wall-clock budget. Small `QF_ABV` formulas ⇒ Z3 decides far
/// faster; this only bounds the rare pathological shape so the test never hangs.
const Z3_TIMEOUT: Duration = Duration::from_secs(2);

/// Per-instance hard wall-clock cap on the axeyum `solve`. A slow array shape is
/// run on a worker thread and joined with this cap; a solve that overruns is
/// recorded as a timeout (adjudication-neutral, exactly like `Unknown`) and the
/// sweep moves on. This is sound — a timeout is never a sat/unsat verdict — and
/// bounds total runtime.
const AXEYUM_TIMEOUT: Duration = Duration::from_secs(4);

/// A deterministic linear-congruential PRNG (the MMIX multiplier/increment).
/// No clock, no OS entropy: the whole sweep is reproducible from the seed.
struct Lcg(u64);

impl Lcg {
    fn new(seed: u64) -> Self {
        // Mix the seed once so consecutive seeds 0,1,2,… don't start correlated.
        Lcg(seed
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407))
    }

    /// Advance and return the next 64-bit state.
    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0
    }

    /// A uniform integer in `0..n` (`n > 0`), returned as a `usize`.
    fn below(&mut self, n: u64) -> usize {
        usize::try_from(self.next_u64() % n).expect("modulus fits usize")
    }
}

/// The relations over element-level bit-vectors. All four are total and have
/// identical semantics in axeyum and Z3, so every one is a fair differential
/// test.
#[derive(Clone, Copy)]
enum BvCmp {
    Eq,
    Ne,
    Ult,
    Ule,
}

impl BvCmp {
    fn pick(rng: &mut Lcg) -> BvCmp {
        match rng.below(4) {
            0 => BvCmp::Eq,
            1 => BvCmp::Ne,
            2 => BvCmp::Ult,
            _ => BvCmp::Ule,
        }
    }

    fn symbol(self) -> &'static str {
        match self {
            BvCmp::Eq => "=",
            BvCmp::Ne => "!=",
            BvCmp::Ult => "bvult",
            BvCmp::Ule => "bvule",
        }
    }

    /// Build `lhs ⋈ rhs` as an IR Bool over two bit-vector element terms.
    fn build(self, a: &mut TermArena, lhs: TermId, rhs: TermId) -> TermId {
        match self {
            BvCmp::Eq => a.eq(lhs, rhs).unwrap(),
            BvCmp::Ne => {
                let e = a.eq(lhs, rhs).unwrap();
                a.not(e).unwrap()
            }
            BvCmp::Ult => a.bv_ult(lhs, rhs).unwrap(),
            BvCmp::Ule => a.bv_ule(lhs, rhs).unwrap(),
        }
    }

    /// Build `lhs ⋈ rhs` as a Z3 `Bool` over two bit-vector terms.
    fn build_z3(self, lhs: &BV, rhs: &BV) -> Bool {
        match self {
            BvCmp::Eq => lhs.eq(rhs),
            BvCmp::Ne => lhs.ne(rhs),
            BvCmp::Ult => lhs.bvult(rhs),
            BvCmp::Ule => lhs.bvule(rhs),
        }
    }
}

/// A total, convention-free binary bit-vector operation. Only ops with verbatim-
/// identical axeyum/Z3 semantics appear — no div/rem/shift.
#[derive(Clone, Copy)]
enum BvBin {
    Add,
    And,
    Or,
    Xor,
}

impl BvBin {
    fn pick(rng: &mut Lcg) -> BvBin {
        match rng.below(4) {
            0 => BvBin::Add,
            1 => BvBin::And,
            2 => BvBin::Or,
            _ => BvBin::Xor,
        }
    }

    fn symbol(self) -> &'static str {
        match self {
            BvBin::Add => "bvadd",
            BvBin::And => "bvand",
            BvBin::Or => "bvor",
            BvBin::Xor => "bvxor",
        }
    }

    fn build(self, a: &mut TermArena, x: TermId, y: TermId) -> TermId {
        match self {
            BvBin::Add => a.bv_add(x, y).unwrap(),
            BvBin::And => a.bv_and(x, y).unwrap(),
            BvBin::Or => a.bv_or(x, y).unwrap(),
            BvBin::Xor => a.bv_xor(x, y).unwrap(),
        }
    }

    fn build_z3(self, x: &BV, y: &BV) -> BV {
        match self {
            BvBin::Add => x.bvadd(y),
            BvBin::And => x.bvand(y),
            BvBin::Or => x.bvor(y),
            BvBin::Xor => x.bvxor(y),
        }
    }
}

/// An array-valued term. Plain data (no IR/Z3 handles), so an [`Instance`] is
/// `Send` + `Clone`. The same tree builds the IR term, the Z3 term, and the
/// pretty-print. Generation bounds the store nesting at depth ≤ 2.
#[derive(Clone)]
enum ArrTerm {
    /// An array variable, by index into the instance's arrays.
    Var(usize),
    /// `store(base, idx, elt)`.
    Store {
        base: Box<ArrTerm>,
        idx: Box<ElemTerm>,
        elt: Box<ElemTerm>,
    },
}

/// An element-valued (bit-vector) term of the instance's width `W`. Plain data.
/// Bounded depth keeps every term shallow so Z3 decides fast.
#[derive(Clone)]
enum ElemTerm {
    /// A bit-vector variable, by index into the instance's element vars.
    Var(usize),
    /// A small bit-vector constant (masked to `W` bits at build time).
    Const(u64),
    /// `select(array, idx)` — the array read that drives read-over-write.
    Select(Box<ArrTerm>, Box<ElemTerm>),
    /// `op(a, b)` for a total convention-free binary op.
    Bin(BvBin, Box<ElemTerm>, Box<ElemTerm>),
    /// `bvnot(a)`.
    Not(Box<ElemTerm>),
}

impl ArrTerm {
    /// Generate a random array term with remaining store-nesting `depth`.
    fn generate(rng: &mut Lcg, depth: usize, num_arrays: usize, num_elem_vars: usize) -> ArrTerm {
        // At depth 0, or randomly, bottom out at an array variable.
        if depth == 0 || rng.below(2) == 0 {
            return ArrTerm::Var(rng.below(num_arrays as u64));
        }
        ArrTerm::Store {
            base: Box::new(ArrTerm::generate(rng, depth - 1, num_arrays, num_elem_vars)),
            idx: Box::new(ElemTerm::generate(rng, 1, num_arrays, num_elem_vars)),
            elt: Box::new(ElemTerm::generate(rng, 1, num_arrays, num_elem_vars)),
        }
    }

    fn build(
        &self,
        arena: &mut TermArena,
        arrays: &[TermId],
        evars: &[TermId],
        width: u32,
    ) -> TermId {
        match self {
            ArrTerm::Var(i) => arrays[*i],
            ArrTerm::Store { base, idx, elt } => {
                let base_t = base.build(arena, arrays, evars, width);
                let idx_t = idx.build(arena, arrays, evars, width);
                let elt_t = elt.build(arena, arrays, evars, width);
                arena.store(base_t, idx_t, elt_t).unwrap()
            }
        }
    }

    fn build_z3(&self, arrays: &[Array], evars: &[BV], w: u32) -> Array {
        match self {
            ArrTerm::Var(i) => arrays[*i].clone(),
            ArrTerm::Store { base, idx, elt } => {
                let b = base.build_z3(arrays, evars, w);
                let i = idx.build_z3(arrays, evars, w);
                let e = elt.build_z3(arrays, evars, w);
                b.store(&i, &e)
            }
        }
    }

    fn dump(&self, anames: &[&str], enames: &[&str]) -> String {
        match self {
            ArrTerm::Var(i) => anames[*i].to_string(),
            ArrTerm::Store { base, idx, elt } => format!(
                "store({}, {}, {})",
                base.dump(anames, enames),
                idx.dump(anames, enames),
                elt.dump(anames, enames)
            ),
        }
    }
}

impl ElemTerm {
    /// Generate a random element term with remaining depth `depth`.
    fn generate(rng: &mut Lcg, depth: usize, num_arrays: usize, num_elem_vars: usize) -> ElemTerm {
        if depth == 0 {
            // Leaf: variable (favoured) or small constant.
            return if rng.below(3) == 0 {
                ElemTerm::Const(rng.next_u64())
            } else {
                ElemTerm::Var(rng.below(num_elem_vars as u64))
            };
        }
        match rng.below(6) {
            0 => ElemTerm::Var(rng.below(num_elem_vars as u64)),
            1 => ElemTerm::Const(rng.next_u64()),
            2 | 3 => ElemTerm::Select(
                Box::new(ArrTerm::generate(rng, 1, num_arrays, num_elem_vars)),
                Box::new(ElemTerm::generate(
                    rng,
                    depth - 1,
                    num_arrays,
                    num_elem_vars,
                )),
            ),
            4 => ElemTerm::Bin(
                BvBin::pick(rng),
                Box::new(ElemTerm::generate(
                    rng,
                    depth - 1,
                    num_arrays,
                    num_elem_vars,
                )),
                Box::new(ElemTerm::generate(
                    rng,
                    depth - 1,
                    num_arrays,
                    num_elem_vars,
                )),
            ),
            _ => ElemTerm::Not(Box::new(ElemTerm::generate(
                rng,
                depth - 1,
                num_arrays,
                num_elem_vars,
            ))),
        }
    }

    /// Does this element term read an array (`select`)? Used to force at least
    /// one atom to exercise the array theory.
    fn uses_array(&self) -> bool {
        match self {
            ElemTerm::Var(_) | ElemTerm::Const(_) => false,
            ElemTerm::Select(_, _) => true,
            ElemTerm::Bin(_, a, b) => a.uses_array() || b.uses_array(),
            ElemTerm::Not(a) => a.uses_array(),
        }
    }

    fn build(&self, a: &mut TermArena, arrays: &[TermId], evars: &[TermId], w: u32) -> TermId {
        match self {
            ElemTerm::Var(i) => evars[*i],
            ElemTerm::Const(k) => {
                let masked = mask_u128(u128::from(*k), w);
                a.bv_const(w, masked).unwrap()
            }
            ElemTerm::Select(arr, idx) => {
                let arr_t = arr.build(a, arrays, evars, w);
                let idx_t = idx.build(a, arrays, evars, w);
                a.select(arr_t, idx_t).unwrap()
            }
            ElemTerm::Bin(op, x, y) => {
                let xt = x.build(a, arrays, evars, w);
                let yt = y.build(a, arrays, evars, w);
                op.build(a, xt, yt)
            }
            ElemTerm::Not(x) => {
                let xt = x.build(a, arrays, evars, w);
                a.bv_not(xt).unwrap()
            }
        }
    }

    fn build_z3(&self, arrays: &[Array], evars: &[BV], w: u32) -> BV {
        match self {
            ElemTerm::Var(i) => evars[*i].clone(),
            ElemTerm::Const(k) => {
                let masked = mask_u128(u128::from(*k), w);
                // `w` ≤ 8 here, so the masked constant fits a u64.
                BV::from_u64(u64::try_from(masked).expect("masked const fits u64"), w)
            }
            ElemTerm::Select(arr, idx) => {
                let arr_t = arr.build_z3(arrays, evars, w);
                let idx_t = idx.build_z3(arrays, evars, w);
                arr_t
                    .select(&idx_t)
                    .as_bv()
                    .expect("select over a BV-element array returns a BV")
            }
            ElemTerm::Bin(op, x, y) => {
                let xt = x.build_z3(arrays, evars, w);
                let yt = y.build_z3(arrays, evars, w);
                op.build_z3(&xt, &yt)
            }
            ElemTerm::Not(x) => x.build_z3(arrays, evars, w).bvnot(),
        }
    }

    fn dump(&self, anames: &[&str], enames: &[&str]) -> String {
        match self {
            ElemTerm::Var(i) => enames[*i].to_string(),
            ElemTerm::Const(k) => format!("#x{k:x}"),
            ElemTerm::Select(arr, idx) => {
                format!(
                    "select({}, {})",
                    arr.dump(anames, enames),
                    idx.dump(anames, enames)
                )
            }
            ElemTerm::Bin(op, x, y) => format!(
                "{}({}, {})",
                op.symbol(),
                x.dump(anames, enames),
                y.dump(anames, enames)
            ),
            ElemTerm::Not(x) => format!("bvnot({})", x.dump(anames, enames)),
        }
    }
}

/// Mask `v` to the low `w` bits.
fn mask_u128(v: u128, w: u32) -> u128 {
    if w >= 128 { v } else { v & ((1u128 << w) - 1) }
}

/// A generated atom: either an element-level `bv ⋈ bv` or an array-level
/// `arr = arr` / `arr != arr` (extensionality).
#[derive(Clone)]
enum Atom {
    /// `lhs ⋈ rhs` over two element terms.
    Elem {
        lhs: ElemTerm,
        rhs: ElemTerm,
        cmp: BvCmp,
    },
    /// `lhs = rhs` (`eq` true) or `lhs != rhs` (`eq` false) over two array terms.
    Arr {
        lhs: ArrTerm,
        rhs: ArrTerm,
        eq: bool,
    },
}

impl Atom {
    /// Does this atom touch the array theory (a `select`, `store`, or an array-
    /// level equality)?
    fn uses_array(&self) -> bool {
        match self {
            Atom::Elem { lhs, rhs, .. } => lhs.uses_array() || rhs.uses_array(),
            Atom::Arr { .. } => true,
        }
    }

    fn build(
        &self,
        arena: &mut TermArena,
        arrays: &[TermId],
        evars: &[TermId],
        width: u32,
    ) -> TermId {
        match self {
            Atom::Elem { lhs, rhs, cmp } => {
                let lhs_t = lhs.build(arena, arrays, evars, width);
                let rhs_t = rhs.build(arena, arrays, evars, width);
                cmp.build(arena, lhs_t, rhs_t)
            }
            Atom::Arr { lhs, rhs, eq } => {
                let lhs_t = lhs.build(arena, arrays, evars, width);
                let rhs_t = rhs.build(arena, arrays, evars, width);
                let e = arena.eq(lhs_t, rhs_t).unwrap();
                if *eq { e } else { arena.not(e).unwrap() }
            }
        }
    }

    fn build_z3(&self, arrays: &[Array], evars: &[BV], w: u32) -> Bool {
        match self {
            Atom::Elem { lhs, rhs, cmp } => {
                let l = lhs.build_z3(arrays, evars, w);
                let r = rhs.build_z3(arrays, evars, w);
                cmp.build_z3(&l, &r)
            }
            Atom::Arr { lhs, rhs, eq } => {
                let l = lhs.build_z3(arrays, evars, w);
                let r = rhs.build_z3(arrays, evars, w);
                if *eq { l.eq(&r) } else { l.ne(&r) }
            }
        }
    }

    fn dump(&self, anames: &[&str], enames: &[&str]) -> String {
        match self {
            Atom::Elem { lhs, rhs, cmp } => format!(
                "{} {} {}",
                lhs.dump(anames, enames),
                cmp.symbol(),
                rhs.dump(anames, enames)
            ),
            Atom::Arr { lhs, rhs, eq } => format!(
                "{} {} {}",
                lhs.dump(anames, enames),
                if *eq { "=" } else { "!=" },
                rhs.dump(anames, enames)
            ),
        }
    }
}

/// A full generated instance. Owns only plain data (no IR/Z3 handles), so it is
/// `Send` + `Clone` — a clone can be moved onto an axeyum worker thread while the
/// original drives the Z3 query and the repro dump.
#[derive(Clone)]
struct Instance {
    /// Index = element bit-vector width (kept equal so all ops compose), in {4,8}.
    width: u32,
    num_arrays: usize,
    num_elem_vars: usize,
    atoms: Vec<Atom>,
}

/// Store-nesting / element-depth ceiling — shallow so Z3 decides fast and the
/// eager array elimination stays small.
const MAX_DEPTH: usize = 2;

impl Instance {
    /// Deterministically generate an instance from the PRNG.
    ///
    /// Distribution:
    /// - width `W` ∈ {4, 8} (small, so Z3 is fast and the bit-blast is cheap);
    /// - 1..=2 array variables, 1..=3 element (BV) variables;
    /// - 1..=4 atoms, each either an element relation `t ⋈ t`
    ///   (`{=, !=, bvult, bvule}` over element terms of depth ≤ 2 drawn from
    ///   {var, const, `select(arr, idx)`, `op(a,b)`, `bvnot(a)`}) or an array
    ///   relation `arr (=|!=) arr` over store-terms of nesting ≤ 2;
    /// - **at least one atom is forced to touch the array theory** (a select,
    ///   store, or array equality): if no generated atom does, the first atom is
    ///   replaced by `select(a0, e0) = e0`.
    fn generate(rng: &mut Lcg) -> Instance {
        let width = if rng.below(2) == 0 { 4 } else { 8 };
        let num_arrays = rng.below(2) + 1; // 1..=2
        let num_elem_vars = rng.below(3) + 1; // 1..=3
        let num_atoms = rng.below(4) + 1; // 1..=4

        let mut atoms = Vec::with_capacity(num_atoms);
        for _ in 0..num_atoms {
            // ~1/4 of atoms are array-level equalities (extensionality); the rest
            // are element relations.
            if rng.below(4) == 0 {
                atoms.push(Atom::Arr {
                    lhs: ArrTerm::generate(rng, MAX_DEPTH, num_arrays, num_elem_vars),
                    rhs: ArrTerm::generate(rng, MAX_DEPTH, num_arrays, num_elem_vars),
                    eq: rng.below(2) == 0,
                });
            } else {
                atoms.push(Atom::Elem {
                    lhs: ElemTerm::generate(rng, MAX_DEPTH, num_arrays, num_elem_vars),
                    rhs: ElemTerm::generate(rng, MAX_DEPTH, num_arrays, num_elem_vars),
                    cmp: BvCmp::pick(rng),
                });
            }
        }

        // Guarantee the array theory is genuinely tested.
        if !atoms.iter().any(Atom::uses_array) {
            atoms[0] = Atom::Elem {
                lhs: ElemTerm::Select(Box::new(ArrTerm::Var(0)), Box::new(ElemTerm::Var(0))),
                rhs: ElemTerm::Var(0),
                cmp: BvCmp::Eq,
            };
        }

        Instance {
            width,
            num_arrays,
            num_elem_vars,
            atoms,
        }
    }

    /// Materialize the instance as IR assertions over a fresh arena, returning
    /// the arena, the array symbol ids, the element-var symbol ids, and the
    /// assertion term ids.
    fn build(&self) -> (TermArena, Vec<SymbolId>, Vec<SymbolId>, Vec<TermId>) {
        let mut a = TermArena::new();
        let anames = ["a", "b"];
        let enames = ["x", "y", "z"];
        let array_sort = Sort::Array {
            index: ArraySortKey::BitVec(self.width),
            element: ArraySortKey::BitVec(self.width),
        };
        let asyms: Vec<SymbolId> = (0..self.num_arrays)
            .map(|i| a.declare(anames[i], array_sort).unwrap())
            .collect();
        let arrays: Vec<TermId> = asyms.iter().map(|&s| a.var(s)).collect();
        let esyms: Vec<SymbolId> = (0..self.num_elem_vars)
            .map(|i| a.declare(enames[i], Sort::BitVec(self.width)).unwrap())
            .collect();
        let evars: Vec<TermId> = esyms.iter().map(|&s| a.var(s)).collect();

        let assertions: Vec<TermId> = self
            .atoms
            .iter()
            .map(|atom| atom.build(&mut a, &arrays, &evars, self.width))
            .collect();
        (a, asyms, esyms, assertions)
    }

    /// Build the same instance as a list of Z3 `Bool` atoms over fresh Z3 array
    /// and bit-vector constants. The adjudication queries Z3 directly with the z3
    /// crate's array + BV theory — the exact same `QF_ABV` semantics axeyum's
    /// array elimination + bit-blast targets.
    fn to_z3(&self) -> Vec<Bool> {
        let anames = ["a", "b"];
        let enames = ["x", "y", "z"];
        let idx_sort = Z3Sort::bitvector(self.width);
        let elt_sort = Z3Sort::bitvector(self.width);
        let arrays: Vec<Array> = (0..self.num_arrays)
            .map(|i| Array::new_const(anames[i], &idx_sort, &elt_sort))
            .collect();
        let evars: Vec<BV> = (0..self.num_elem_vars)
            .map(|i| BV::new_const(enames[i], self.width))
            .collect();

        self.atoms
            .iter()
            .map(|atom| atom.build_z3(&arrays, &evars, self.width))
            .collect()
    }

    /// An SMT-ish dump of the instance for a reproducing panic message.
    fn dump(&self) -> String {
        let anames = ["a", "b"];
        let enames = ["x", "y", "z"];
        let w = self.width;
        let mut lines = vec![
            format!(
                "arrays: {} : (Array (_ BitVec {w}) (_ BitVec {w}))",
                anames[..self.num_arrays].join(", ")
            ),
            format!(
                "elem vars: {} : (_ BitVec {w})",
                enames[..self.num_elem_vars].join(", ")
            ),
        ];
        for (i, atom) in self.atoms.iter().enumerate() {
            lines.push(format!("  atom[{i}]: {}", atom.dump(&anames, &enames)));
        }
        lines.join("\n")
    }
}

/// A coarse verdict label, abstracting away the model/reason payloads.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Verdict {
    Sat,
    Unsat,
    Unknown,
}

fn label(r: &CheckResult) -> Verdict {
    match r {
        CheckResult::Sat(_) => Verdict::Sat,
        CheckResult::Unsat => Verdict::Unsat,
        CheckResult::Unknown(_) => Verdict::Unknown,
    }
}

/// The replay outcome of an axeyum `Sat`, computed on the worker thread (which
/// owns the arena). `Model::to_assignment` carries the BV variable bindings and
/// any array interpretations (`Value::Array`); the IR evaluator's `Op::Select`/
/// `Op::Store` arms replay them. A well-formed `QF_ABV` `Sat` is expected to
/// replay `AllTrue`. `Indeterminate` is kept for the case where the evaluator
/// declines an atom (e.g. an array symbol the model left unbound, which yields
/// `IrError::UnboundSymbol`) — adjudication-neutral; only `Violated` is a wrong
/// sat.
#[derive(Clone, PartialEq, Eq, Debug)]
enum Replay {
    /// Not a `Sat` verdict (no model to replay).
    NotSat,
    /// Every original atom evaluated `true` at the model — a verified replay.
    AllTrue,
    /// The evaluator declined ≥ 1 atom (`Err`/non-Bool) and refuted none —
    /// indeterminate; the Z3 cross-check still adjudicates the verdict.
    Indeterminate,
    /// An atom evaluated `false` at the model — a WRONG SAT (carries the atom
    /// index and a model dump for the panic).
    Violated { atom: usize, model: String },
}

/// The full axeyum result for one instance, decided on a worker thread under a
/// hard wall-clock cap.
struct AxeyumOutcome {
    verdict: Verdict,
    replay: Replay,
    /// A model dump for a `Sat` (used only when reporting a disagreement).
    model_dump: Option<String>,
}

/// The bounded axeyum decision for one instance.
enum Bounded {
    /// `solve` finished within the cap and returned a verdict.
    Decided(AxeyumOutcome),
    /// `solve` overran the wall-clock cap — adjudication-neutral, like `Unknown`.
    Timeout,
    /// `solve` (or the replay) **panicked** — a crash bug in the solver, *not* a
    /// sat/unsat verdict. Adjudication-neutral (a panic is never a verdict, so it
    /// can never be a wrong sat/unsat), but counted and the first one reported,
    /// since a panic on a valid `QF_ABV` query is itself a defect.
    Crashed,
}

/// Decide an instance with axeyum on a worker thread, joining under
/// [`AXEYUM_TIMEOUT`].
///
/// The arena, the model, and the replay all live on the worker thread; only the
/// `Send` summary crosses back. The whole `solve`+replay runs inside
/// `catch_unwind` so a solver panic does not abort the sweep — it is reported as
/// [`Bounded::Crashed`] (adjudication-neutral), letting the differential gate run
/// across every instance instead of wedging on one crashing shape.
fn solve_axeyum_bounded(inst: Instance) -> Bounded {
    let (tx, rx) = mpsc::channel::<AxeyumOutcome>();
    std::thread::spawn(move || {
        // Catch a panic from inside `solve` (or the replay) so it surfaces as a
        // crash signal (the channel staying empty) rather than tearing down the
        // harness. The closure owns the instance and builds its own arena, so
        // nothing shared is left poisoned.
        let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(move || {
            let (a, _asyms, esyms, assertions) = inst.build();
            let mut a = a;
            let result = solve(&mut a, &assertions, &SolverConfig::default());
            let outcome = match result {
                // `solve` must not error; treat an error like a crash (channel
                // stays empty → reported as Crashed). `Unknown` is a result.
                Err(_) => return,
                Ok(ax) => {
                    let verdict = label(&ax);
                    let (replay, model_dump) = match &ax {
                        CheckResult::Sat(model) => {
                            // The assignment carries BOTH the BV variable bindings
                            // and the array interpretations, so the evaluator
                            // replays the full model (`Op::Select`/`Op::Store`).
                            let asg = model.to_assignment();
                            let dump = dump_model(&esyms, model);
                            let mut replay = Replay::AllTrue;
                            for (i, &assertion) in assertions.iter().enumerate() {
                                match eval(&a, assertion, &asg) {
                                    Ok(Value::Bool(true)) => {}
                                    Ok(Value::Bool(false)) => {
                                        replay = Replay::Violated {
                                            atom: i,
                                            model: dump.clone(),
                                        };
                                        break;
                                    }
                                    // `Err(..)` (e.g. an unbound array symbol) or a
                                    // non-Bool result: indeterminate, not a
                                    // refutation. Keep scanning for a true
                                    // violation in a later atom.
                                    _ => {
                                        if replay == Replay::AllTrue {
                                            replay = Replay::Indeterminate;
                                        }
                                    }
                                }
                            }
                            (replay, Some(dump))
                        }
                        _ => (Replay::NotSat, None),
                    };
                    AxeyumOutcome {
                        verdict,
                        replay,
                        model_dump,
                    }
                }
            };
            // The receiver may be gone (we timed out); ignore a send error.
            let _ = tx.send(outcome);
        }));
        // On panic / error, `tx` is dropped here without a send → the receiver
        // observes `Disconnected`, mapped to a crash below.
    });

    match rx.recv_timeout(AXEYUM_TIMEOUT) {
        Ok(outcome) => Bounded::Decided(outcome),
        Err(mpsc::RecvTimeoutError::Timeout) => Bounded::Timeout,
        // The worker dropped its sender without sending: it panicked or `solve`
        // returned an error. Either way it is a crash, not a verdict.
        Err(mpsc::RecvTimeoutError::Disconnected) => Bounded::Crashed,
    }
}

/// Decide an instance with Z3 over the `QF_ABV` theory, with a tiny wall-clock
/// timeout. Returns `Unknown` on timeout/incompleteness (the instance is then
/// skipped — Z3 cannot adjudicate it).
fn z3_decide(inst: &Instance) -> Verdict {
    let solver = Solver::new();
    let mut params = Params::new();
    params.set_u32(
        "timeout",
        u32::try_from(Z3_TIMEOUT.as_millis()).unwrap_or(u32::MAX),
    );
    solver.set_params(&params);
    for atom in inst.to_z3() {
        solver.assert(&atom);
    }
    match solver.check() {
        SatResult::Sat => Verdict::Sat,
        SatResult::Unsat => Verdict::Unsat,
        SatResult::Unknown => Verdict::Unknown,
    }
}

/// Running counters for the sweep.
#[derive(Default)]
struct Tally {
    total: u64,
    jointly_decided: u64,
    agreements: u64,
    axeyum_unknown: u64,
    axeyum_timeout: u64,
    axeyum_crashed: u64,
    z3_unknown_skipped: u64,
    sat_replayed: u64,
    sat_replay_indeterminate: u64,
    /// The first crashing instance, kept for the report (a panic on a valid
    /// `QF_ABV` query is a defect even though it is never a *mis-verdict*).
    first_crash: Option<(u64, String)>,
}

/// Decide one instance with both engines and fold the result into `t`. Panics
/// only on a genuine soundness violation (a non-replaying Sat, or a jointly-
/// decided Sat/Unsat disagreement) — the whole point of the gate.
fn run_instance(seed: u64, inst: &Instance, t: &mut Tally) {
    // --- axeyum: the default pure-Rust front door, hard-capped. ----------
    let outcome = match solve_axeyum_bounded(inst.clone()) {
        Bounded::Decided(o) => o,
        Bounded::Timeout => {
            t.axeyum_timeout += 1;
            return;
        }
        Bounded::Crashed => {
            // A panic inside `solve` is a crash bug, *not* a sat/unsat verdict —
            // adjudication-neutral (counted, never failing the soundness gate).
            // Record the first one for the report and move on so the sweep covers
            // every instance.
            t.axeyum_crashed += 1;
            if t.first_crash.is_none() {
                t.first_crash = Some((seed, inst.dump()));
            }
            return;
        }
    };
    let ax_label = outcome.verdict;

    // A `Sat` whose model VIOLATES an original atom under the independent ground
    // evaluator (with the array interpretation) is a wrong sat — regardless of Z3.
    if let Replay::Violated { atom, model } = &outcome.replay {
        panic!(
            "WRONG SAT (seed {seed}): axeyum returned Sat but its model makes \
             atom[{atom}] FALSE under the independent ground evaluator (with the \
             array interpretation) — a soundness bug.\nmodel: {model}\ninstance:\n{}",
            inst.dump()
        );
    }
    match outcome.replay {
        Replay::AllTrue => t.sat_replayed += 1,
        Replay::Indeterminate => t.sat_replay_indeterminate += 1,
        Replay::NotSat | Replay::Violated { .. } => {}
    }

    if ax_label == Verdict::Unknown {
        t.axeyum_unknown += 1;
    }

    // --- Z3 oracle: a direct QF_ABV query, tiny timeout. -----------------
    let z3_label = z3_decide(inst);
    if z3_label == Verdict::Unknown {
        t.z3_unknown_skipped += 1;
        return;
    }
    // Both sides committed to Sat/Unsat (axeyum may still be Unknown).
    if ax_label == Verdict::Unknown {
        return;
    }

    t.jointly_decided += 1;

    // THE SOUNDNESS GATE: a jointly-decided instance must AGREE.
    if ax_label == z3_label {
        t.agreements += 1;
    } else {
        let model_dump = outcome
            .model_dump
            .unwrap_or_else(|| "(no axeyum model)".to_string());
        panic!(
            "DISAGREEMENT (seed {seed}): axeyum = {ax_label:?}, Z3 = {z3_label:?}.\n\
             This is a {} soundness bug.\n\
             axeyum model: {model_dump}\n\
             instance:\n{}",
            match (ax_label, z3_label) {
                (Verdict::Sat, Verdict::Unsat) => "WRONG-SAT",
                (Verdict::Unsat, Verdict::Sat) => "WRONG-UNSAT (worst case)",
                _ => "verdict",
            },
            inst.dump()
        );
    }
}

#[test]
fn abv_differential_fuzz_disagree_zero() {
    // Worker `solve` panics are *caught* (a crash is adjudication-neutral, not a
    // verdict). Install a panic hook that stays silent for panics originating in
    // solver/crate source (so thousands of caught crashes don't flood stderr) but
    // still prints panics from *this test file* — the genuine soundness-gate
    // panics — at full volume.
    let default_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        let from_this_test = info
            .location()
            .is_some_and(|loc| loc.file().ends_with("abv_differential_fuzz.rs"));
        if from_this_test {
            default_hook(info);
        }
    }));

    let mut t = Tally::default();

    for seed in 0..INSTANCES {
        t.total += 1;
        if seed % 250 == 0 {
            eprintln!(
                "[abv-fuzz] seed {seed}/{INSTANCES} (joint={}, agree={}, \
                 ax_unknown={}, ax_timeout={}, ax_crash={})",
                t.jointly_decided,
                t.agreements,
                t.axeyum_unknown,
                t.axeyum_timeout,
                t.axeyum_crashed
            );
        }
        let mut rng = Lcg::new(seed);
        let inst = Instance::generate(&mut rng);
        run_instance(seed, &inst, &mut t);
    }

    let Tally {
        total,
        jointly_decided,
        agreements,
        axeyum_unknown,
        axeyum_timeout,
        axeyum_crashed,
        z3_unknown_skipped,
        sat_replayed,
        sat_replay_indeterminate,
        first_crash,
    } = t;

    println!("=== QF_ABV differential fuzz tally ===");
    println!("total instances:      {total}");
    println!("jointly decided:      {jointly_decided}");
    println!("agreements:           {agreements}");
    println!("axeyum Unknown:       {axeyum_unknown}");
    println!(
        "axeyum timeout:       {axeyum_timeout} (slow array shape; capped, adjudication-neutral)"
    );
    println!(
        "axeyum CRASHED:       {axeyum_crashed} (solver panic on a valid QF_ABV query — a defect, \
         but never a mis-verdict)"
    );
    println!("Z3 Unknown (skipped): {z3_unknown_skipped}");
    println!("Sat replays verified: {sat_replayed}");
    println!("Sat replay declined:  {sat_replay_indeterminate} (eval gap; Z3-adjudicated)");
    println!("DISAGREEMENTS:        0");
    if let Some((seed, dump)) = &first_crash {
        println!(
            "--- first crashing instance (seed {seed}) — solver panic, reported \
             for a deliberate fix ---\n{dump}"
        );
    }

    // Reaching here means no disagreement panicked: DISAGREE=0 over the sweep.
    // Sanity: the sweep must actually exercise the joint decider (guards against
    // a silently-broken Z3 plumbing that always times out, which would make
    // DISAGREE=0 vacuous).
    assert!(
        jointly_decided > 100,
        "too few jointly-decided instances ({jointly_decided}); the differential \
         gate is not meaningfully exercised"
    );
}

/// Pretty-print an axeyum model's element-variable bindings. (Array symbol
/// interpretations are part of the assignment but `Value::Array` Debug is
/// verbose; the element bindings plus the instance dump suffice for a repro.)
fn dump_model(esyms: &[SymbolId], model: &axeyum_solver::Model) -> String {
    let enames = ["x", "y", "z"];
    let mut parts = Vec::new();
    for (i, &s) in esyms.iter().enumerate() {
        let v = model.get(s);
        parts.push(format!("{}={:?}", enames[i], v));
    }
    parts.join(", ")
}

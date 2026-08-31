//! Re-derive the evidence behind every `imported-kernel-lean` fact in
//! `artifacts/facts/`.
//!
//! WHAT THIS CHECKS, AND WHY IT IS NOT THE SAME AS PROVING ANYTHING.
//!
//! Each row below names a pinned official `lean4export` NDJSON stream that ships
//! in `artifacts/lean-imports/`, one declaration inside it, the type our kernel
//! derives for that declaration, and the trusted declarations that declaration's
//! transitive closure reaches. The test:
//!
//!   1. hashes the fixture bytes and compares against the pin, so the stream a
//!      fact cites cannot be swapped underneath it;
//!   2. runs the fail-closed importer, which admits nothing unless the WHOLE
//!      stream translates and every declaration passes `Kernel::add_declaration`;
//!   3. looks the target declaration up in the published environment and asserts
//!      `Kernel::render_lean` of its type is unchanged, AND that the fact's
//!      `formal.statement` is that render with the emit-direction `AxNat` guard
//!      undone (see [`Row::rendered_type`] for why the two differ);
//!   4. asserts `Kernel::axiom_footprint` of that declaration equals the Lean
//!      axioms the fact records.
//!
//! Step 4 is the honest part. `axiom_footprint` here is the footprint *inside the
//! imported environment* — it says what Lean's own proof term rests on. It does
//! NOT cover the trust the import itself adds: that the exporter faithfully
//! rendered Lean's environment, that our translation of the wire format preserves
//! meaning, and that the delivered bytes are the producer's intended export (the
//! format has no footer, so completion is relative to the bytes handed over).
//! Those live in the fact's `axiom_footprint` as named assumptions, which is why
//! `imported-kernel-lean` is not in the validator's `AXIOM_FREE_CAPABLE` set and
//! an empty footprint is rejected on this route.
//!
//! Each row prints a `AXEYUM-IMPORT-FACT|` marker line. The facts' checker
//! commands grep for their own marker, so a suite that compiles to zero tests —
//! this repository's signature defect — fails the gate instead of exiting 0.

use std::path::{Path, PathBuf};

use axeyum_lean_import::{ImportLimits, import_ndjson};
use axeyum_lean_kernel::Declaration;
use sha2::{Digest, Sha256};

struct Row {
    /// The `artifacts/facts/` entry this row re-derives.
    fact: &'static str,
    /// Fixture basename under `artifacts/lean-imports/`.
    fixture: &'static str,
    /// SHA-256 of the fixture bytes, pinned.
    sha256: &'static str,
    /// The declaration the fact is about.
    declaration: &'static str,
    /// `Kernel::render_lean` of its admitted type, VERBATIM.
    ///
    /// Note the `AxNat` root. `render_lean` rewrites a root `Nat` segment to
    /// `AxNat` so that emitting *our* prelude to a real `lean` binary does not
    /// shadow Lean's builtin `Nat` (which has literal/`OfNat` kernel support).
    /// That guard is correct in the emit direction and exactly backwards here:
    /// the `Nat` in an imported stream IS Lean's builtin `Nat`, so the rendered
    /// string names a constant that does not exist. Pinned verbatim anyway,
    /// because it is what the kernel actually derives and it moves if the kernel
    /// moves; `fact_statement` below is the form a fact may honestly carry.
    rendered_type: &'static str,
    /// `rendered_type` with the emit-direction `AxNat` guard undone — the string
    /// the corresponding fact carries in `formal.statement`.
    fact_statement: &'static str,
    /// Declarations admitted from the stream (family + constructors + recursors).
    admitted: usize,
    /// `Kernel::axiom_footprint` of `declaration`, rendered and sorted.
    lean_axioms: &'static [&'static str],
}

const ROWS: &[Row] = &[
    Row {
        fact: "F:nat-le-refl",
        fixture: "nat-le-refl.ndjson",
        sha256: "087e3097a28dbbc88ed4d52a04ea17d01f96f9d1fbbf6b0c5a3eda6c5cb03cd6",
        declaration: "Nat.le_refl",
        rendered_type: "((n : AxNat) -> LE.le.{0} AxNat instLENat n n)",
        fact_statement: "((n : Nat) -> LE.le.{0} Nat instLENat n n)",
        admitted: 14,
        lean_axioms: &[],
    },
    Row {
        fact: "F:nat-le-succ",
        fixture: "nat-le-succ.ndjson",
        sha256: "bded309d580baac0551fd94de97e692b6e3e2854d8157c247679b1fb8af04f7f",
        declaration: "Nat.le_succ",
        rendered_type: "((n : AxNat) -> LE.le.{0} AxNat instLENat n (AxNat.succ n))",
        fact_statement: "((n : Nat) -> LE.le.{0} Nat instLENat n (Nat.succ n))",
        admitted: 14,
        lean_axioms: &[],
    },
    Row {
        fact: "F:list-nil-append",
        fixture: "list-nil-append.ndjson",
        sha256: "02d24e45d1745e9f3d973a1198314b8a3c5e60ce2e9dc3f4eead44c930e4bf14",
        declaration: "List.nil_append",
        rendered_type: "((α : Sort (u+1)) -> ((as : List.{u} α) -> Eq.{u+1} (List.{u} α) (HAppend.hAppend.{u, u, u} (List.{u} α) (List.{u} α) (List.{u} α) (instHAppendOfAppend.{u} (List.{u} α) (List.instAppend.{u} α)) (List.nil.{u} α) as) as))",
        fact_statement: "((α : Sort (u+1)) -> ((as : List.{u} α) -> Eq.{u+1} (List.{u} α) (HAppend.hAppend.{u, u, u} (List.{u} α) (List.{u} α) (List.{u} α) (instHAppendOfAppend.{u} (List.{u} α) (List.instAppend.{u} α)) (List.nil.{u} α) as) as))",
        admitted: 33,
        lean_axioms: &[],
    },
    Row {
        fact: "F:bool-and-comm",
        fixture: "bool-and-comm.ndjson",
        sha256: "19e3fd972bccd534660e447b445f8a80cb708752813c1d40ad9b8427045c898f",
        declaration: "Bool.and_comm",
        rendered_type: "((x : Bool) -> ((y : Bool) -> Eq.{1} Bool (Bool.and x y) (Bool.and y x)))",
        fact_statement: "((x : Bool) -> ((y : Bool) -> Eq.{1} Bool (Bool.and x y) (Bool.and y x)))",
        admitted: 48,
        lean_axioms: &[],
    },
    Row {
        fact: "F:prop-excluded-middle-classical",
        fixture: "classical-em.ndjson",
        sha256: "e3ad1320c85bb756a8d8f673de29542db7250cac4a3a5a485a82664ef2939e19",
        declaration: "Classical.em",
        rendered_type: "((p : Prop) -> Or p (Not p))",
        fact_statement: "((p : Prop) -> Or p (Not p))",
        admitted: 106,
        lean_axioms: &[
            "Classical.choice",
            "Quot",
            "Quot.lift",
            "Quot.mk",
            "Quot.sound",
            "propext",
        ],
    },
    Row {
        fact: "F:ivt-mathlib-import-intermediate-value-icc",
        fixture: "ivt-intermediate-value-icc.ndjson",
        sha256: "4b56ae00ec5f292e371b22e1b2045c001220eac93e6ff9eb6f562e35a04a63ce",
        declaration: "intermediate_value_Icc",
        rendered_type: r#"((α : Sort (u+1)) -> ((inst._@.Mathlib.Topology.Order.IntermediateValue._3882871496._hygCtx._hyg._3 : TopologicalSpace.{u} α) -> ((inst._@.Mathlib.Topology.Order.IntermediateValue._3882871496._hygCtx._hyg._6 : ConditionallyCompleteLinearOrder.{u} α) -> ((inst._@.Mathlib.Topology.Order.IntermediateValue._3882871496._hygCtx._hyg._9 : OrderTopology.{u} α inst._@.Mathlib.Topology.Order.IntermediateValue._3882871496._hygCtx._hyg._3 (PartialOrder.toPreorder.{u} α (ConditionallyCompletePartialOrderSup.toPartialOrder.{u} α (ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{u} α (ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{u} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u} α inst._@.Mathlib.Topology.Order.IntermediateValue._3882871496._hygCtx._hyg._6)))))) -> ((inst._@.Mathlib.Topology.Order.IntermediateValue._3882871496._hygCtx._hyg._12 : DenselyOrdered.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (ConditionallyCompletePartialOrderSup.toPartialOrder.{u} α (ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{u} α (ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{u} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u} α inst._@.Mathlib.Topology.Order.IntermediateValue._3882871496._hygCtx._hyg._6))))))) -> ((δ : Sort (u_1+1)) -> ((inst._@.Mathlib.Topology.Order.IntermediateValue._3882871496._hygCtx._hyg._18 : LinearOrder.{u_1} δ) -> ((inst._@.Mathlib.Topology.Order.IntermediateValue._3882871496._hygCtx._hyg._21 : TopologicalSpace.{u_1} δ) -> ((inst._@.Mathlib.Topology.Order.IntermediateValue._3882871496._hygCtx._hyg._24 : OrderClosedTopology.{u_1} δ inst._@.Mathlib.Topology.Order.IntermediateValue._3882871496._hygCtx._hyg._21 (PartialOrder.toPreorder.{u_1} δ (SemilatticeInf.toPartialOrder.{u_1} δ (Lattice.toSemilatticeInf.{u_1} δ (DistribLattice.toLattice.{u_1} δ (instDistribLatticeOfLinearOrder.{u_1} δ inst._@.Mathlib.Topology.Order.IntermediateValue._3882871496._hygCtx._hyg._18)))))) -> ((a : α) -> ((b : α) -> ((hab : LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (ConditionallyCompletePartialOrderSup.toPartialOrder.{u} α (ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{u} α (ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{u} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u} α inst._@.Mathlib.Topology.Order.IntermediateValue._3882871496._hygCtx._hyg._6)))))) a b) -> ((f : ((a._@._internal._hyg._0 : α) -> δ)) -> ((hf : ContinuousOn.{u, u_1} α δ inst._@.Mathlib.Topology.Order.IntermediateValue._3882871496._hygCtx._hyg._3 inst._@.Mathlib.Topology.Order.IntermediateValue._3882871496._hygCtx._hyg._21 f (Set.Icc.{u} α (PartialOrder.toPreorder.{u} α (ConditionallyCompletePartialOrderSup.toPartialOrder.{u} α (ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{u} α (ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{u} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u} α inst._@.Mathlib.Topology.Order.IntermediateValue._3882871496._hygCtx._hyg._6))))) a b)) -> HasSubset.Subset.{u_1} (Set.{u_1} δ) (Set.instHasSubset.{u_1} δ) (Set.Icc.{u_1} δ (PartialOrder.toPreorder.{u_1} δ (SemilatticeInf.toPartialOrder.{u_1} δ (Lattice.toSemilatticeInf.{u_1} δ (DistribLattice.toLattice.{u_1} δ (instDistribLatticeOfLinearOrder.{u_1} δ inst._@.Mathlib.Topology.Order.IntermediateValue._3882871496._hygCtx._hyg._18))))) (f a) (f b)) (Set.image.{u, u_1} α δ f (Set.Icc.{u} α (PartialOrder.toPreorder.{u} α (ConditionallyCompletePartialOrderSup.toPartialOrder.{u} α (ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{u} α (ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{u} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u} α inst._@.Mathlib.Topology.Order.IntermediateValue._3882871496._hygCtx._hyg._6))))) a b))))))))))))))))"#,
        fact_statement: r#"((α : Sort (u+1)) -> ((inst._@.Mathlib.Topology.Order.IntermediateValue._3882871496._hygCtx._hyg._3 : TopologicalSpace.{u} α) -> ((inst._@.Mathlib.Topology.Order.IntermediateValue._3882871496._hygCtx._hyg._6 : ConditionallyCompleteLinearOrder.{u} α) -> ((inst._@.Mathlib.Topology.Order.IntermediateValue._3882871496._hygCtx._hyg._9 : OrderTopology.{u} α inst._@.Mathlib.Topology.Order.IntermediateValue._3882871496._hygCtx._hyg._3 (PartialOrder.toPreorder.{u} α (ConditionallyCompletePartialOrderSup.toPartialOrder.{u} α (ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{u} α (ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{u} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u} α inst._@.Mathlib.Topology.Order.IntermediateValue._3882871496._hygCtx._hyg._6)))))) -> ((inst._@.Mathlib.Topology.Order.IntermediateValue._3882871496._hygCtx._hyg._12 : DenselyOrdered.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (ConditionallyCompletePartialOrderSup.toPartialOrder.{u} α (ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{u} α (ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{u} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u} α inst._@.Mathlib.Topology.Order.IntermediateValue._3882871496._hygCtx._hyg._6))))))) -> ((δ : Sort (u_1+1)) -> ((inst._@.Mathlib.Topology.Order.IntermediateValue._3882871496._hygCtx._hyg._18 : LinearOrder.{u_1} δ) -> ((inst._@.Mathlib.Topology.Order.IntermediateValue._3882871496._hygCtx._hyg._21 : TopologicalSpace.{u_1} δ) -> ((inst._@.Mathlib.Topology.Order.IntermediateValue._3882871496._hygCtx._hyg._24 : OrderClosedTopology.{u_1} δ inst._@.Mathlib.Topology.Order.IntermediateValue._3882871496._hygCtx._hyg._21 (PartialOrder.toPreorder.{u_1} δ (SemilatticeInf.toPartialOrder.{u_1} δ (Lattice.toSemilatticeInf.{u_1} δ (DistribLattice.toLattice.{u_1} δ (instDistribLatticeOfLinearOrder.{u_1} δ inst._@.Mathlib.Topology.Order.IntermediateValue._3882871496._hygCtx._hyg._18)))))) -> ((a : α) -> ((b : α) -> ((hab : LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (ConditionallyCompletePartialOrderSup.toPartialOrder.{u} α (ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{u} α (ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{u} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u} α inst._@.Mathlib.Topology.Order.IntermediateValue._3882871496._hygCtx._hyg._6)))))) a b) -> ((f : ((a._@._internal._hyg._0 : α) -> δ)) -> ((hf : ContinuousOn.{u, u_1} α δ inst._@.Mathlib.Topology.Order.IntermediateValue._3882871496._hygCtx._hyg._3 inst._@.Mathlib.Topology.Order.IntermediateValue._3882871496._hygCtx._hyg._21 f (Set.Icc.{u} α (PartialOrder.toPreorder.{u} α (ConditionallyCompletePartialOrderSup.toPartialOrder.{u} α (ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{u} α (ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{u} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u} α inst._@.Mathlib.Topology.Order.IntermediateValue._3882871496._hygCtx._hyg._6))))) a b)) -> HasSubset.Subset.{u_1} (Set.{u_1} δ) (Set.instHasSubset.{u_1} δ) (Set.Icc.{u_1} δ (PartialOrder.toPreorder.{u_1} δ (SemilatticeInf.toPartialOrder.{u_1} δ (Lattice.toSemilatticeInf.{u_1} δ (DistribLattice.toLattice.{u_1} δ (instDistribLatticeOfLinearOrder.{u_1} δ inst._@.Mathlib.Topology.Order.IntermediateValue._3882871496._hygCtx._hyg._18))))) (f a) (f b)) (Set.image.{u, u_1} α δ f (Set.Icc.{u} α (PartialOrder.toPreorder.{u} α (ConditionallyCompletePartialOrderSup.toPartialOrder.{u} α (ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{u} α (ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{u} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u} α inst._@.Mathlib.Topology.Order.IntermediateValue._3882871496._hygCtx._hyg._6))))) a b))))))))))))))))"#,
        admitted: 3585,
        lean_axioms: &[
            "Classical.choice",
            "Quot",
            "Quot.lift",
            "Quot.mk",
            "Quot.sound",
            "String.Internal.append",
            "propext",
            "wrapped._@.Mathlib.Topology.Defs.Filter.2998874748._hygCtx._hyg.2",
        ],
    },
    Row {
        fact: "F:evt-mathlib-import-compact-exists-is-max-on",
        fixture: "evt-is-compact-exists-is-max-on.ndjson",
        sha256: "79141bd00f29dad5c049b320d0dbaf425c6ac87d120d7825665d95129ed639d8",
        declaration: "IsCompact.exists_isMaxOn",
        rendered_type: r#"((α : Sort (u_2+1)) -> ((β : Sort (u_3+1)) -> ((inst._@.Mathlib.Topology.Order.Compact._3966579681._hygCtx._hyg._6 : LinearOrder.{u_2} α) -> ((inst._@.Mathlib.Topology.Order.Compact._3966579681._hygCtx._hyg._9 : TopologicalSpace.{u_2} α) -> ((inst._@.Mathlib.Topology.Order.Compact._3966579681._hygCtx._hyg._12 : TopologicalSpace.{u_3} β) -> ((inst._@.Mathlib.Topology.Order.Compact._3966579681._hygCtx._hyg._18 : ClosedIciTopology.{u_2} α inst._@.Mathlib.Topology.Order.Compact._3966579681._hygCtx._hyg._9 (PartialOrder.toPreorder.{u_2} α (SemilatticeInf.toPartialOrder.{u_2} α (Lattice.toSemilatticeInf.{u_2} α (DistribLattice.toLattice.{u_2} α (instDistribLatticeOfLinearOrder.{u_2} α inst._@.Mathlib.Topology.Order.Compact._3966579681._hygCtx._hyg._6)))))) -> ((s : Set.{u_3} β) -> ((hs : IsCompact.{u_3} β inst._@.Mathlib.Topology.Order.Compact._3966579681._hygCtx._hyg._12 s) -> ((ne_s : Set.Nonempty.{u_3} β s) -> ((f : ((a._@._internal._hyg._0 : β) -> α)) -> ((hf : ContinuousOn.{u_3, u_2} β α inst._@.Mathlib.Topology.Order.Compact._3966579681._hygCtx._hyg._12 inst._@.Mathlib.Topology.Order.Compact._3966579681._hygCtx._hyg._9 f s) -> Exists.{u_3+1} β (fun (x : β) => And (Membership.mem.{u_3, u_3} β (Set.{u_3} β) (Set.instMembership.{u_3} β) s x) (IsMaxOn.{u_3, u_2} β α (PartialOrder.toPreorder.{u_2} α (SemilatticeInf.toPartialOrder.{u_2} α (Lattice.toSemilatticeInf.{u_2} α (DistribLattice.toLattice.{u_2} α (instDistribLatticeOfLinearOrder.{u_2} α inst._@.Mathlib.Topology.Order.Compact._3966579681._hygCtx._hyg._6))))) f s x)))))))))))))"#,
        fact_statement: r#"((α : Sort (u_2+1)) -> ((β : Sort (u_3+1)) -> ((inst._@.Mathlib.Topology.Order.Compact._3966579681._hygCtx._hyg._6 : LinearOrder.{u_2} α) -> ((inst._@.Mathlib.Topology.Order.Compact._3966579681._hygCtx._hyg._9 : TopologicalSpace.{u_2} α) -> ((inst._@.Mathlib.Topology.Order.Compact._3966579681._hygCtx._hyg._12 : TopologicalSpace.{u_3} β) -> ((inst._@.Mathlib.Topology.Order.Compact._3966579681._hygCtx._hyg._18 : ClosedIciTopology.{u_2} α inst._@.Mathlib.Topology.Order.Compact._3966579681._hygCtx._hyg._9 (PartialOrder.toPreorder.{u_2} α (SemilatticeInf.toPartialOrder.{u_2} α (Lattice.toSemilatticeInf.{u_2} α (DistribLattice.toLattice.{u_2} α (instDistribLatticeOfLinearOrder.{u_2} α inst._@.Mathlib.Topology.Order.Compact._3966579681._hygCtx._hyg._6)))))) -> ((s : Set.{u_3} β) -> ((hs : IsCompact.{u_3} β inst._@.Mathlib.Topology.Order.Compact._3966579681._hygCtx._hyg._12 s) -> ((ne_s : Set.Nonempty.{u_3} β s) -> ((f : ((a._@._internal._hyg._0 : β) -> α)) -> ((hf : ContinuousOn.{u_3, u_2} β α inst._@.Mathlib.Topology.Order.Compact._3966579681._hygCtx._hyg._12 inst._@.Mathlib.Topology.Order.Compact._3966579681._hygCtx._hyg._9 f s) -> Exists.{u_3+1} β (fun (x : β) => And (Membership.mem.{u_3, u_3} β (Set.{u_3} β) (Set.instMembership.{u_3} β) s x) (IsMaxOn.{u_3, u_2} β α (PartialOrder.toPreorder.{u_2} α (SemilatticeInf.toPartialOrder.{u_2} α (Lattice.toSemilatticeInf.{u_2} α (DistribLattice.toLattice.{u_2} α (instDistribLatticeOfLinearOrder.{u_2} α inst._@.Mathlib.Topology.Order.Compact._3966579681._hygCtx._hyg._6))))) f s x)))))))))))))"#,
        admitted: 2486,
        lean_axioms: &[
            "Classical.choice",
            "Quot",
            "Quot.lift",
            "Quot.mk",
            "Quot.sound",
            "String.Internal.append",
            "propext",
            "wrapped._@.Mathlib.Topology.Defs.Filter.2998874748._hygCtx._hyg.2",
        ],
    },
];

fn hex(bytes: &[u8]) -> String {
    use std::fmt::Write as _;
    let mut out = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        let _ = write!(out, "{b:02x}");
    }
    out
}

fn fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../artifacts/lean-imports")
        .canonicalize()
        .expect("artifacts/lean-imports must exist")
}

#[test]
fn imported_facts_re_derive_from_pinned_streams() {
    let dir = fixture_dir();
    let mut drift: Vec<String> = Vec::new();
    for row in ROWS {
        let path = dir.join(row.fixture);
        let bytes = std::fs::read(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
        let digest = hex(&Sha256::digest(&bytes));

        let completed = import_ndjson(bytes.as_slice(), ImportLimits::default())
            .unwrap_or_else(|e| panic!("{}: import failed: {e}", row.fixture));
        let (kernel, report) = completed.into_parts();

        let name = kernel
            .environment()
            .iter()
            .map(|(_, d)| d.name())
            .find(|&n| kernel.display_name(n).to_string() == row.declaration)
            .unwrap_or_else(|| panic!("{}: {} not admitted", row.fixture, row.declaration));
        let declaration = kernel.environment().get(name).expect("just found");
        let ty = match declaration {
            Declaration::Theorem { ty, .. } => *ty,
            other => panic!(
                "{}: {} is {other:?}, not a theorem",
                row.fixture, row.declaration
            ),
        };
        let rendered = kernel.render_lean(ty);
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|n| kernel.display_name(n).to_string())
            .collect();

        println!(
            "AXEYUM-IMPORT-FACT|{}|decl={}|sha256={}|lean={}|admitted={}|lean_axioms={}|type={}",
            row.fact,
            row.declaration,
            digest,
            report.lean_version,
            report.admitted_declarations,
            if footprint.is_empty() {
                "none".to_owned()
            } else {
                footprint.join(",")
            },
            rendered,
        );

        let mut check = |what: &str, got: String, want: &str| {
            if got != want {
                drift.push(format!(
                    "  {} {}: {what}\n    pinned {want}\n    got    {got}",
                    row.fact, row.fixture
                ));
            }
        };
        check("fixture bytes", digest, row.sha256);
        check(
            "admitted declarations",
            report.admitted_declarations.to_string(),
            &row.admitted.to_string(),
        );
        check(
            "Kernel::render_lean of the admitted type",
            rendered.clone(),
            row.rendered_type,
        );
        check(
            "fact formal.statement",
            unshadow_nat(&rendered),
            row.fact_statement,
        );
        check(
            "Kernel::axiom_footprint",
            footprint.join(","),
            &row.lean_axioms.join(","),
        );
    }

    assert!(
        drift.is_empty(),
        "{} imported-fact evidence row(s) no longer re-derive:\n{}",
        drift.len(),
        drift.join("\n")
    );
}

/// Undo `render_lean`'s emit-direction `AxNat` shadow guard.
///
/// Applied only to imported streams, where the root `Nat` is Lean's own builtin
/// and the guard therefore renames a constant that genuinely exists. It is a
/// whole-token rewrite so `AxNat.le` becomes `Nat.le` while an unrelated
/// identifier containing the letters is untouched.
fn unshadow_nat(rendered: &str) -> String {
    let mut out = String::with_capacity(rendered.len());
    let mut token = String::new();
    for c in rendered.chars() {
        if c.is_alphanumeric() || c == '_' || c == '.' {
            token.push(c);
            continue;
        }
        out.push_str(&rewrite_token(&token));
        token.clear();
        out.push(c);
    }
    out.push_str(&rewrite_token(&token));
    out
}

fn rewrite_token(token: &str) -> String {
    if token == "AxNat" {
        "Nat".to_owned()
    } else if let Some(rest) = token.strip_prefix("AxNat.") {
        format!("Nat.{rest}")
    } else {
        token.to_owned()
    }
}

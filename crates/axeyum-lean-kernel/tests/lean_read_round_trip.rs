//! The render → parse → same-term gate for `Kernel::read_lean` (Next Ten
//! item 9, first half; ADR-1680).
//!
//! For EVERY fact in the ledger carrying `formal.language: "lean4"` (derived
//! from `artifacts/facts/*.json` at test time, never a literal list), this
//! reads `formal.statement` back into a kernel `ExprId` against one kernel
//! that carries every prelude this crate builds, and checks:
//!
//! 1. `render_lean(read_lean(s)) == s` byte-for-byte, where `s` is the
//!    statement with its `theorem`/`def`/`axiom`/`inductive NAME : ` wrapper
//!    stripped (that wrapper is `scripts/gen-kernel-facts.py`'s own
//!    `f"theorem {name} : {rendered_type}"`, not something
//!    `Kernel::render_lean` ever emits).
//! 2. Where `formal.kernel_theorem` names a declaration this union kernel
//!    actually has (found by exact `display_name` match, never by string
//!    munging), `def_eq(read_lean(s), type_of(kernel_theorem))`.
//!
//! A `lean4` statement that does not read is a FINDING, not a skip: it is
//! tabulated per fragment under a typed failure class
//! ([`axeyum_lean_kernel::ReadError::class`]) and the suite still passes as
//! long as `missing == 0` (every fact in the population was actually
//! processed) — the population size and the per-class counts are what a
//! reader of this suite's output is meant to check, not a boolean.
//!
//! # What this measures, and what it claims
//!
//! Item 9's claim is narrow and this suite is the evidence for exactly that
//! width: for a `lean4` fact, its statement can now be checked to be a
//! well-formed proposition of THIS kernel on any host, without Lean. It says
//! nothing about `lean4-surface` facts (Mathlib's elaborator syntax — a
//! separate, larger grammar that ADR-1662's census found gated on demand it
//! does not have) and nothing about whether the statement is TRUE — only
//! that it type-checks as a well-formed term.
//!
//! Run with a generous timeout; this is pure Rust (no Lean invoked) but
//! builds several thousand kernel declarations before scoring the ledger:
//!
//! ```sh
//! scripts/cargo-serialized.sh test -p axeyum-lean-kernel \
//!   --test lean_read_round_trip -- --nocapture
//! ```

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use axeyum_lean_kernel::{
    Kernel, NameId, build_arith_prelude, build_characterization, build_complex_prelude,
    build_cpoint_prelude, build_creal_model_of_arith, build_int_model_of_arith, build_int_prelude,
    build_intspace_prelude, build_ipc_soundness_prelude, build_list_nat_bridge, build_list_perm,
    build_logic_prelude, build_metric_prelude, build_nat_prelude, build_rat_model_of_arith,
    build_rat_prelude, build_rn_prelude, build_string_length_append, build_string_prelude,
    build_string_substr_arithmetic, build_top_frame_prelude,
};

fn facts_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../artifacts/facts")
}

/// One `lean4`-language fact, as read from the ledger. Only the fields this
/// suite needs; everything else in the JSON is ignored.
struct LeanFact {
    id: String,
    fragment: String,
    statement: String,
    kernel_theorem: Option<String>,
}

/// Every ledger fact with `formal.language == "lean4"`, sorted by id for a
/// deterministic report. Population size is DERIVED here, never hardcoded —
/// the two `#[test]`s below assert a floor on this count so a scanning bug
/// that silently returns an empty `Vec` cannot pass as "0 facts, 0
/// failures".
fn load_lean4_facts() -> Vec<LeanFact> {
    let dir = facts_dir();
    let mut out = Vec::new();
    let entries = fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("cannot read fact ledger dir {}: {e}", dir.display()));
    for entry in entries {
        let path = entry.expect("readable dir entry").path();
        if path.extension().and_then(|e| e.to_str()) != Some("json") {
            continue;
        }
        let text = fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()));
        let value: serde_json::Value = serde_json::from_str(&text)
            .unwrap_or_else(|e| panic!("cannot parse {}: {e}", path.display()));
        let formal = &value["formal"];
        if formal.get("language").and_then(serde_json::Value::as_str) != Some("lean4") {
            continue;
        }
        let id = value["id"]
            .as_str()
            .unwrap_or_else(|| panic!("{} has no top-level id", path.display()))
            .to_owned();
        let fragment = formal
            .get("fragment")
            .and_then(serde_json::Value::as_str)
            .unwrap_or("none")
            .to_owned();
        let statement = formal["statement"]
            .as_str()
            .unwrap_or_else(|| panic!("{id} has no formal.statement"))
            .to_owned();
        let kernel_theorem = formal
            .get("kernel_theorem")
            .and_then(serde_json::Value::as_str)
            .map(str::to_owned);
        out.push(LeanFact {
            id,
            fragment,
            statement,
            kernel_theorem,
        });
    }
    out.sort_by(|a, b| a.id.cmp(&b.id));
    out
}

/// Strips a `KEYWORD NAME : ` wrapper (`theorem`/`def`/`axiom`/`inductive`)
/// off a `formal.statement`, leaving exactly the `Kernel::render_lean`
/// fragment `Kernel::read_lean` understands. A statement with no such
/// wrapper (a bare rendered type, as some hand-authored facts carry) is
/// returned unchanged. The name never contains a space or `:`, so the FIRST
/// `" : "` in a wrapped statement is unambiguously the separator — including
/// when the type itself goes on to contain many more `" : "`s from its own
/// binders.
fn strip_wrapper(statement: &str) -> &str {
    for keyword in ["theorem ", "def ", "axiom ", "inductive "] {
        if let Some(rest) = statement.strip_prefix(keyword)
            && let Some(sep) = rest.find(" : ")
        {
            return &rest[sep + 3..];
        }
    }
    statement
}

/// One kernel carrying every prelude this crate exports, so a fact's
/// `formal.fragment` need not be matched to a specific builder by name (the
/// label is sometimes wrong — e.g. a `CReal` theorem filed under `Real`,
/// measured in the ledger) and the report can instead show, per declared
/// fragment, how many of ITS facts this union kernel actually reads.
/// Mirrors `real_lean_replay_census_all.rs`'s `everything` carrier
/// construction (every builder here is idempotent) plus `top_frame`, which
/// that census counts separately.
fn build_everything() -> Kernel {
    let mut k = Kernel::new();
    build_rn_prelude(&mut k).expect("the RN prelude must build");
    build_intspace_prelude(&mut k).expect("the IntSpace prelude must build");
    build_complex_prelude(&mut k).expect("the Complex prelude must build");
    build_characterization(&mut k).expect("the Nat/Int characterization must build");
    build_ipc_soundness_prelude(&mut k).expect("the IPC soundness prelude must build");
    let (list, nat, bridge) =
        build_list_nat_bridge(&mut k).expect("the List/Nat bridge must build");
    build_list_perm(&mut k, &list, &nat, &bridge).expect("List.Perm must build");
    let sp = build_string_prelude(&mut k, nat.logic, 2).expect("the String prelude must build");
    build_string_length_append(&mut k, &sp, &nat).expect("String.length_append must build");
    build_string_substr_arithmetic(&mut k, &sp, &nat)
        .expect("String.substr_append_split must build");
    build_int_model_of_arith(&mut k).expect("the Int model of AxReal must build");
    build_rat_model_of_arith(&mut k).expect("the Rat model of AxReal must build");
    build_creal_model_of_arith(&mut k).expect("the CReal model of AxReal must build");
    build_top_frame_prelude(&mut k).expect("the Top prelude must build");
    // Idempotent safety net: each of these is already reachable transitively
    // above, but calling it directly keeps this list honest against a future
    // change to any one dependency chain.
    build_rat_prelude(&mut k).expect("the Rat prelude must build");
    build_int_prelude(&mut k).expect("the Int prelude must build");
    build_nat_prelude(&mut k).expect("the Nat prelude must build");
    build_logic_prelude(&mut k).expect("the logic prelude must build");
    build_arith_prelude(&mut k).expect("the AxReal prelude must build");
    build_cpoint_prelude(&mut k).expect("the CPoint prelude must build");
    build_metric_prelude(&mut k).expect("the Metric prelude must build");
    k
}

/// Every declaration's `display_name` (the RAW internal spelling
/// `formal.kernel_theorem` is written in — no `AxNat` remap, no `_N` numeric
/// convention; those are `render_lean`-only spellings) mapped to its
/// `NameId`, built once so `kernel_theorem` lookups are O(1) instead of an
/// O(declarations) scan per fact.
fn display_name_index(kernel: &Kernel) -> BTreeMap<String, NameId> {
    let mut map = BTreeMap::new();
    for (name, _decl) in kernel.environment().iter() {
        map.insert(kernel.display_name(*name).to_string(), *name);
    }
    map
}

#[derive(Default)]
struct FragmentStats {
    total: usize,
    read_ok: usize,
    roundtrip_ok: usize,
    defeq_checked: usize,
    defeq_ok: usize,
    failures: BTreeMap<&'static str, usize>,
}

/// The full census: every `lean4` fact, against the union kernel, tabulated
/// per `formal.fragment`.
/// Scores one fact against `kernel`, updating `stats` in place. Split out of
/// the `#[test]` purely to keep that function under clippy's line budget;
/// this is not reusable elsewhere.
fn score_one_fact(
    kernel: &mut Kernel,
    names: &BTreeMap<String, NameId>,
    fact: &LeanFact,
    stats: &mut FragmentStats,
    verbose: bool,
) {
    stats.total += 1;
    let body = strip_wrapper(&fact.statement);

    match kernel.read_lean(body) {
        Ok(expr) => {
            stats.read_ok += 1;
            let rendered = kernel.render_lean(expr);
            if rendered == body {
                stats.roundtrip_ok += 1;
            } else {
                *stats.failures.entry("roundtrip-mismatch").or_insert(0) += 1;
                if verbose {
                    eprintln!(
                        "ROUNDTRIP-MISMATCH {} ({})\n  body:     {body}\n  rendered: {rendered}",
                        fact.id, fact.fragment
                    );
                }
            }
            let Some(theorem_name) = &fact.kernel_theorem else {
                return;
            };
            let Some(&name_id) = names.get(theorem_name) else {
                *stats
                    .failures
                    .entry("kernel-theorem-not-in-union-kernel")
                    .or_insert(0) += 1;
                return;
            };
            stats.defeq_checked += 1;
            let declared_ty = kernel
                .environment()
                .get(name_id)
                .expect("indexed name must be present")
                .ty();
            if kernel.def_eq(expr, declared_ty) {
                stats.defeq_ok += 1;
            } else {
                *stats.failures.entry("def-eq-mismatch").or_insert(0) += 1;
                if verbose {
                    eprintln!(
                        "DEF-EQ-MISMATCH {} ({}) kernel_theorem={theorem_name}\n  body:     {body}\n  declared: {}",
                        fact.id,
                        fact.fragment,
                        kernel.render_lean(declared_ty)
                    );
                }
            }
        }
        Err(e) => {
            *stats.failures.entry(e.class()).or_insert(0) += 1;
            if verbose {
                eprintln!("{} {} ({}): {e}", e.class(), fact.id, fact.fragment);
            }
        }
    }
}

#[test]
fn lean4_ledger_round_trips_against_the_kernel() {
    let facts = load_lean4_facts();
    assert!(
        facts.len() >= 1900,
        "the lean4 population looks too small ({}) -- did the fact scan break? \
         (measured 2026-09-05: 2,020)",
        facts.len()
    );

    let mut kernel = build_everything();
    let names = display_name_index(&kernel);
    assert!(
        names.len() > 3_000,
        "the union kernel looks too small ({} declarations) -- did a builder \
         silently no-op?",
        names.len()
    );

    let verbose = std::env::var("LEAN_READ_ROUND_TRIP_VERBOSE").is_ok();
    let mut per_fragment: BTreeMap<String, FragmentStats> = BTreeMap::new();
    let mut processed = 0usize;

    for fact in &facts {
        processed += 1;
        let stats = per_fragment.entry(fact.fragment.clone()).or_default();
        score_one_fact(&mut kernel, &names, fact, stats, verbose);
    }

    assert_eq!(
        processed,
        facts.len(),
        "every lean4 fact must be processed, none skipped (missing == 0)"
    );

    println!("fragment\ttotal\tread_ok\troundtrip_ok\tdefeq_checked\tdefeq_ok\tfailure_classes");
    let mut totals = FragmentStats::default();
    for (fragment, stats) in &per_fragment {
        println!(
            "{fragment}\t{}\t{}\t{}\t{}\t{}\t{:?}",
            stats.total,
            stats.read_ok,
            stats.roundtrip_ok,
            stats.defeq_checked,
            stats.defeq_ok,
            stats.failures
        );
        totals.total += stats.total;
        totals.read_ok += stats.read_ok;
        totals.roundtrip_ok += stats.roundtrip_ok;
        totals.defeq_checked += stats.defeq_checked;
        totals.defeq_ok += stats.defeq_ok;
        for (class, count) in &stats.failures {
            *totals.failures.entry(class).or_insert(0) += count;
        }
    }
    println!(
        "TOTAL\t{}\t{}\t{}\t{}\t{}\t{:?}",
        totals.total,
        totals.read_ok,
        totals.roundtrip_ok,
        totals.defeq_checked,
        totals.defeq_ok,
        totals.failures
    );

    // The floor this suite pins is on the byte-exact round trip, which is
    // the load-bearing half of item 9's claim (def_eq additionally requires
    // `kernel_theorem` to be both present AND resolvable in this ONE union
    // kernel, which several fragments -- imported-route facts spelled in
    // Mathlib's own names, and package-level facts with no single subject --
    // structurally cannot satisfy). Measured 2026-09-05; see
    // docs/plan/status/lean-statement-reader.md and ADR-1680 for the
    // per-fragment table this floor was set from.
    assert!(
        totals.roundtrip_ok >= 1_850,
        "round-trip floor regressed: {} (expected >= 1,850 of {})",
        totals.roundtrip_ok,
        totals.total
    );
}

/// Negative control: swapping the argument order at a use site of a
/// non-symmetric relation (`AxNat.le x0 x1` -> `AxNat.le x1 x0`) must read
/// (it is still syntactically well-formed) but must NOT be `def_eq` to the
/// original declared type.
#[test]
fn negative_control_swapped_argument_order_reads_but_fails_def_eq() {
    let facts = load_lean4_facts();
    let fact = facts
        .iter()
        .find(|f| f.id == "F:nat-le-of-succ-le-succ")
        .expect("F:nat-le-of-succ-le-succ must be in the ledger");
    let body = strip_wrapper(&fact.statement);
    assert!(
        body.contains("AxNat.le x0 x1"),
        "fixture assumption broken -- the fact's shape changed: {body}"
    );
    let corrupted = body.replace("AxNat.le x0 x1", "AxNat.le x1 x0");
    assert_ne!(
        corrupted, body,
        "the corruption must actually change the text"
    );

    let mut kernel = build_nat_prelude_only();
    let original = kernel
        .read_lean(body)
        .expect("the real statement must read");
    let mutated = kernel
        .read_lean(&corrupted)
        .expect("the swapped-argument statement is still well-formed and must read");
    assert!(
        !kernel.def_eq(mutated, original),
        "a swapped-argument-order statement must not be def_eq to the original"
    );
}

/// Negative control: renaming a constant (`AxNat.succ` -> `AxNat.pred`) must
/// either fail to read (if the replacement name is not declared) or, if it
/// reads, must not be `def_eq` to the original.
#[test]
fn negative_control_renamed_constant_fails_to_read_or_fails_def_eq() {
    let facts = load_lean4_facts();
    let fact = facts
        .iter()
        .find(|f| f.id == "F:nat-le-of-succ-le-succ")
        .expect("F:nat-le-of-succ-le-succ must be in the ledger");
    let body = strip_wrapper(&fact.statement);
    assert!(
        body.contains("AxNat.succ"),
        "fixture assumption broken -- the fact's shape changed: {body}"
    );
    let corrupted = body.replace("AxNat.succ", "AxNat.pred");
    assert_ne!(
        corrupted, body,
        "the corruption must actually change the text"
    );

    let mut kernel = build_nat_prelude_only();
    let original = kernel
        .read_lean(body)
        .expect("the real statement must read");
    match kernel.read_lean(&corrupted) {
        Err(e) => assert_eq!(e.class(), "unknown-constant"),
        Ok(mutated) => assert!(
            !kernel.def_eq(mutated, original),
            "a renamed-constant statement must not be def_eq to the original"
        ),
    }
}

/// Negative control: dropping a universe argument (`Sort (u)` -> `Sort ()`)
/// on a real universe-polymorphic ledger fact must fail to read.
#[test]
fn negative_control_dropped_universe_argument_fails_to_read() {
    let facts = load_lean4_facts();
    let fact = facts
        .iter()
        .find(|f| f.id == "F:acc-inv")
        .expect("F:acc-inv must be in the ledger");
    let body = strip_wrapper(&fact.statement);
    assert!(
        body.contains("Sort (u)"),
        "fixture assumption broken -- the fact's shape changed: {body}"
    );
    let corrupted = body.replacen("Sort (u)", "Sort ()", 1);
    assert_ne!(
        corrupted, body,
        "the corruption must actually change the text"
    );

    let mut kernel = build_everything();
    kernel
        .read_lean(body)
        .expect("the real universe-polymorphic statement must read");
    let err = kernel
        .read_lean(&corrupted)
        .expect_err("dropping the universe argument must fail to read");
    // The direct cause is `bad-level`/`unexpected-token` at the corruption
    // site, but `Sort ()` sits deep inside a `Pi` telescope here: when that
    // inner parse fails, `parse_paren_atom`'s backtracking retries the
    // ENCLOSING `Pi` as a plain parenthesized expression, and the class this
    // test can observe is whatever that fallback interpretation hits first
    // (typically a binder that is no longer in scope once the `Pi`
    // structure is abandoned) -- the same characteristic documented on
    // `a_prior_facts_binder_name_does_not_leak_into_a_later_facts_constant_resolution`
    // in `lean_read.rs`. What this control requires is the outcome, not
    // which fallback class surfaces: the corrupted statement must be
    // REJECTED, cleanly and without a panic.
    assert!(
        matches!(
            err.class(),
            "bad-level" | "unexpected-token" | "unbound-variable" | "unknown-constant"
        ),
        "unexpected failure class for a dropped universe argument: {}",
        err.class()
    );
}

fn build_nat_prelude_only() -> Kernel {
    let mut k = Kernel::new();
    build_nat_prelude(&mut k).expect("the Nat prelude must build");
    k
}

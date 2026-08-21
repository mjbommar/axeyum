//! Regression: an imported recursor's `k` flag must match the one this kernel
//! derives, not the one the stream asserts.
//!
//! Found 2026-08-18 by the adversarial kernel-vs-kernel differential
//! (`real_lean_wire_differential.rs`). Three of its eight violations were this:
//! flip `recs[i].k` on an `inductive` record and our importer admitted the
//! stream, while the recursor Lean's kernel generated for the same family
//! disagreed with the one the stream carried.
//!
//! Why it is not cosmetic. `k` licenses K-like ι-reduction: a recursor
//! application whose major premise is *not* a constructor still reduces,
//! because a `Prop`-valued single-constructor family with no fields has only
//! one inhabitant up to definitional proof irrelevance. Asserting it for a
//! family that has not earned it is a reduction rule no kernel should have. Our
//! importer validated `numParams`, `numIndices`, `numMotives`, `numMinors`, the
//! ι-rules and the recursor type against the recursor this kernel generated —
//! and read `k` only to reject it on nested and mutual groups, never comparing
//! it to the derived value.
//!
//! The controls keep the fix honest: the undamaged stream must still import,
//! and both directions of the flip must be refused — a guard that only caught
//! `false -> true` would leave the export claiming a family is not K-like when
//! it is, which is how a round trip loses a reduction rule.

use std::io::Cursor;

use axeyum_lean_import::{ImportLimits, import_ndjson};
use axeyum_lean_kernel::{Kernel, Lean4ExportMetadata, build_logic_prelude};
use serde_json::Value;

/// The logic prelude as an official `lean4export` NDJSON 3.1.0 stream.
///
/// It carries ten inductive groups, and among them both answers to the K-like
/// question: `True` is K-like (`Prop`, one constructor, no fields), `Or` and
/// `Acc` are not. So one fixture exercises the guard in both directions.
fn exported_logic_prelude() -> String {
    let mut kernel = Kernel::new();
    build_logic_prelude(&mut kernel).expect("logic prelude must build");
    kernel
        .render_lean4export_ndjson(&Lean4ExportMetadata::axeyum("4.30.0"))
        .expect("the checked development must export")
}

/// Flip the `k` flag of the `which`-th recursor record on the stream, and
/// report what it was flipped from.
fn flip_kth_k(stream: &str, which: usize) -> Option<(String, bool)> {
    let mut lines: Vec<String> = stream.lines().map(str::to_owned).collect();
    let mut seen = 0_usize;
    for line in &mut lines {
        let Ok(mut record) = serde_json::from_str::<Value>(line) else {
            continue;
        };
        let Some(recursors) = record["inductive"]["recs"].as_array().cloned() else {
            continue;
        };
        for position in 0..recursors.len() {
            if seen == which {
                let was = recursors[position]["k"].as_bool().expect("k is a boolean");
                record["inductive"]["recs"][position]["k"] = Value::from(!was);
                *line = serde_json::to_string(&record).expect("re-serialize record");
                let mut text = lines.join("\n");
                text.push('\n');
                return Some((text, was));
            }
            seen += 1;
        }
    }
    None
}

#[test]
fn the_undamaged_export_still_imports() {
    let stream = exported_logic_prelude();
    import_ndjson(Cursor::new(stream.as_bytes()), ImportLimits::default())
        .expect("our own export must re-import; without this the guard below is vacuous");
}

#[test]
fn flipping_a_recursor_k_flag_is_refused_in_both_directions() {
    let stream = exported_logic_prelude();
    let mut refused_from_true = 0_usize;
    let mut refused_from_false = 0_usize;
    let mut which = 0_usize;
    while let Some((damaged, was)) = flip_kth_k(&stream, which) {
        which += 1;
        let error = import_ndjson(Cursor::new(damaged.as_bytes()), ImportLimits::default())
            .err()
            .unwrap_or_else(|| {
                panic!(
                    "recursor {} had its K-like flag flipped from {was} and the import \
                     was ADMITTED; the flag licenses reducing a recursor application \
                     whose major premise is not a constructor",
                    which - 1
                )
            });
        let rendered = format!("{error:?}");
        assert!(
            rendered.contains("K-like") || rendered.contains("K target"),
            "recursor {} was refused for an unrelated reason: {rendered}",
            which - 1
        );
        if was {
            refused_from_true += 1;
        } else {
            refused_from_false += 1;
        }
    }
    // Both directions must be exercised, or half the guard is untested and this
    // suite would still be green with it half removed.
    assert!(
        refused_from_true > 0 && refused_from_false > 0,
        "the fixture exercised only one direction of the flip \
         (true->false {refused_from_true}, false->true {refused_from_false}); \
         a fixture without both is not a test of this guard"
    );
}

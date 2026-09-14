#!/usr/bin/env python3
"""ZERO-INST -- split the lever's env read from its SPELLING, so the OFF/ON
polarity is testable without touching process environment.

Same shape as `parse_moderate_pre_sat_envelope` in `dpll_lia.rs`, and for the
same reason: a lever that fails OPEN would silently measure the shipped arm
against itself, and that has to be provable by a test rather than by reading
the code.
"""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
AUTO = ROOT / 'crates/axeyum-solver/src/auto.rs'

OLD = '''fn bool_skeleton_probe_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var("AXEYUM_ZERO_INST_SKELETON").is_ok_and(|v| v == "1"))
}'''

NEW = '''fn bool_skeleton_probe_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| {
        parse_bool_skeleton_lever(std::env::var("AXEYUM_ZERO_INST_SKELETON").ok().as_deref())
    })
}

/// Parses [`bool_skeleton_probe_enabled`]'s spelling. Split out so the OFF/ON
/// polarity is testable **without touching process environment**: every
/// spelling other than exactly `1` must return `false`, because a lever that
/// failed OPEN would silently measure the shipped arm against itself and
/// report the result as a null.
fn parse_bool_skeleton_lever(raw: Option<&str>) -> bool {
    raw == Some("1")
}'''


def main():
    s = AUTO.read_text()
    if 'fn parse_bool_skeleton_lever' in s:
        print('already applied; nothing to do')
        return
    if s.count(OLD) != 1:
        sys.exit(f'ABORT: anchor matched {s.count(OLD)} times, expected exactly 1')
    AUTO.write_text(s.replace(OLD, NEW, 1))
    print(f'patched {AUTO}')


main()

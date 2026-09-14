#!/usr/bin/env python3
"""ZERO-INST -- flip the Boolean-skeleton rung's default to ON.

The A/B cleared every pre-registered rule, so the rung ships enabled and the
environment variable becomes a KILL SWITCH rather than an arming switch.

The polarity therefore INVERTS at this commit, which is stated in the code, in
the runner header, and in the ADR, because a later reader who reuses
`ab-run.sh` without noticing would measure the shipped arm in both halves.
"""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
AUTO = ROOT / 'crates/axeyum-solver/src/auto.rs'

OLD = '''/// Whether the Boolean-skeleton refutation rung is armed.
///
/// **Polarity: OFF is the shipped arm.** Unset, empty, or anything other than
/// exactly `1` returns `false` and the rung does not run, so a typo, a stale
/// export or a malformed value all fail **closed** to shipped behaviour.
///
/// Read through a `OnceLock` so an armed A/B cannot be perturbed mid-run and a
/// disarmed build pays one cached load per call.
fn bool_skeleton_probe_enabled() -> bool {
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

NEW = '''/// Whether the Boolean-skeleton refutation rung is armed.
///
/// **Polarity: ON is the shipped arm, and this INVERTED at ADR-2025.** Before
/// that commit the rung was off unless `AXEYUM_ZERO_INST_SKELETON=1`; it now
/// runs unless `AXEYUM_ZERO_INST_SKELETON=0`, and the variable is a **kill
/// switch**. Anyone reusing `bench-results/zero-inst-20260914/ab-run.sh` on a
/// later binary without noticing would measure the shipped arm in both halves
/// and report the resulting zero as a null, so the inversion is stated here,
/// in that runner's header, and in the ADR.
///
/// Why ON: measured on the 129-row `UFLIA`/`UFNIA` winnable population,
/// interleaved per file, one binary and two env values — **+9 rows, 0 losses,
/// 0 flips**, every gain carrying `q:bool-skeleton` `decided` in its route
/// trail, all 9 STABLE-GAIN over three passes per arm, all 9 agreeing with
/// `:status`, z3 and cvc5, against a same-arm noise floor of **0 of 129** and
/// at **0.93x** the wall clock.
///
/// Read through a `OnceLock` so an A/B cannot be perturbed mid-run.
fn bool_skeleton_probe_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| {
        parse_bool_skeleton_lever(std::env::var("AXEYUM_ZERO_INST_SKELETON").ok().as_deref())
    })
}

/// Parses [`bool_skeleton_probe_enabled`]'s spelling. Split out so the ON/OFF
/// polarity is testable **without touching process environment**.
///
/// Exactly `0` disables. Every other spelling — unset, empty, `1`, a typo —
/// leaves the rung ON, so a malformed kill switch fails **safe** in the sense
/// that matters after shipping: it keeps the measured behaviour rather than
/// silently reverting to the pre-ADR-2025 ladder.
fn parse_bool_skeleton_lever(raw: Option<&str>) -> bool {
    raw != Some("0")
}'''

TEST_OLD = '''    /// The lever's polarity, checked without touching process environment.
    ///
    /// Every spelling other than exactly `1` must be OFF. A lever that failed
    /// OPEN would run the armed arm in both halves of an A/B and report the
    /// resulting zero as a null result, which is the one outcome no later
    /// reader could distinguish from an honest negative.
    #[test]
    fn the_bool_skeleton_lever_is_off_unless_spelled_exactly() {
        assert!(parse_bool_skeleton_lever(Some("1")), "the armed spelling");
        for off in [
            None,
            Some(""),
            Some("0"),
            Some(" 1"),
            Some("1 "),
            Some("true"),
            Some("TRUE"),
            Some("yes"),
            Some("on"),
            Some("11"),
            Some("1,1"),
        ] {
            assert!(
                !parse_bool_skeleton_lever(off),
                "{off:?} must fail CLOSED to the shipped arm"
            );
        }
    }'''

TEST_NEW = '''    /// The lever's polarity, checked without touching process environment.
    ///
    /// **This assertion is inverted from its first version, deliberately.**
    /// The rung shipped ON at ADR-2025, so `0` is the kill switch and every
    /// other spelling leaves it enabled. The test is written this way round so
    /// that a future change back to opt-in cannot land silently: it would have
    /// to edit this test, in this direction, on purpose.
    #[test]
    fn the_bool_skeleton_lever_is_on_unless_killed_exactly() {
        assert!(
            !parse_bool_skeleton_lever(Some("0")),
            "exactly `0` is the kill switch"
        );
        for on in [
            None,
            Some(""),
            Some("1"),
            Some(" 0"),
            Some("0 "),
            Some("false"),
            Some("FALSE"),
            Some("no"),
            Some("off"),
            Some("00"),
        ] {
            assert!(
                parse_bool_skeleton_lever(on),
                "{on:?} is not the kill switch, so the rung stays ON"
            );
        }
    }'''

ARMED_OLD = '''        assert!(
            !skeleton_refutes_quantified_query_armed(&mut arena, &assertions, &config).unwrap(),
            "a query with no quantifier to abstract is not this rung's to claim"
        );'''

ARMED_NEW = '''        assert!(
            !skeleton_refutes_quantified_query_armed(&mut arena, &assertions, &config).unwrap(),
            "a query with no quantifier to abstract is not this rung's to claim"
        );
        // And through the shipped entry point, which since ADR-2025 is ARMED by
        // default -- so this also pins that the default really is on.
        assert!(
            !skeleton_refutes_quantified_query(&mut arena, &assertions, &config).unwrap(),
            "the shipped entry point declines it too"
        );'''


def main():
    s = AUTO.read_text()
    if 'ON is the shipped arm' in s:
        print('already applied; nothing to do')
        return
    for name, needle in (('gate doc', OLD), ('polarity test', TEST_OLD),
                         ('armed test', ARMED_OLD)):
        if s.count(needle) != 1:
            sys.exit(f'ABORT: {name} matched {s.count(needle)} times, expected 1')
    s = s.replace(OLD, NEW, 1)
    s = s.replace(TEST_OLD, TEST_NEW, 1)
    s = s.replace(ARMED_OLD, ARMED_NEW, 1)
    AUTO.write_text(s)
    print(f'patched {AUTO}')


main()

//! Environment levers over compiled caps: an A/B without a rebuild.
//!
//! # Why this exists
//!
//! `axeyum-solver`'s `config_registry` enumerates 481 governing values.
//! Measured 2026-09-11, **74** of them protect COMPLETENESS, refuse or decline
//! when crossed, and carry an undated justification — nobody has measured what
//! their value costs. Nearly all had `env_override: None`, so asking "does this
//! bound decide the division?" meant editing a source file and rebuilding the
//! workspace. That is why none of them had been asked.
//!
//! This module is the one-line answer: a cap wired through [`cap_lever!`] keeps
//! its compiled value exactly, and becomes a one-command arm
//! (`AXEYUM_MAX_ATOMS=64 cargo run …`) when someone wants to measure it.
//!
//! # What a lever is NOT
//!
//! It is **not a licence to raise a cap**. Three of these caps were
//! investigated on 2026-09-11 and all three turned out to be correct as
//! shipped: `ABSOLUTE_CLAUSE_CEILING` rebuilt at 31x decided 4 of 4 refused
//! files still `unknown`, burning 90 s each instead of refusing in 30 s. The
//! deliverable is the ABILITY to measure, and a measurement that comes back
//! "the shipped value was right" is the expected outcome, not a failure.
//!
//! # The contract
//!
//! - **Unset is the shipped value, byte for byte.** [`cap`] reads the
//!   environment only when the variable is present, so a process with no
//!   `AXEYUM_*` set computes the same verdicts it computed before the lever
//!   existed.
//! - **A malformed value is a hard error, never a silent fallback.** A typo
//!   that quietly measured the default arm would produce a number someone
//!   believes. `AXEYUM_MAX_ATOMS=sixtenn` panics naming the variable; it does
//!   not run the default and call it the raised arm. The empty string is
//!   malformed too — `AXEYUM_MAX_ATOMS=` is a mistake, not an unset.
//! - **Read once per process.** [`cap_lever!`] caches in a `OnceLock`, so a
//!   lever at a hot comparison site costs an atomic load, not a scan of the
//!   environment. Levers are process-level arms; setting a variable from inside
//!   a running process does not move an accessor that has already resolved.
//! - **Underscores are allowed** in the value, because that is how the caps are
//!   written in the source (`4_096`): `AXEYUM_X=4_096` and `AXEYUM_X=4096` are
//!   the same arm.
//!
//! # The one failure this cannot catch
//!
//! A misspelled **variable name** sets something nothing reads, and the run
//! looks exactly like the default arm. Nothing here can see that; the check is
//! to run with `--trace` and confirm your variable appears in the `; config`
//! line's `env:` fields (`axeyum_solver::config_registry::active_env_overrides`
//! derives those from the registry, so a variable that is not a registered
//! `env_override` will be absent).

use std::fmt::Display;
use std::str::FromStr;

/// Resolves one cap: the value of `var` if it is set, else `shipped`.
///
/// Prefer [`cap_lever!`], which wraps this in a cached accessor. Call this
/// directly only where a `OnceLock` accessor does not fit.
///
/// # Panics
///
/// Panics when `var` IS set but its value is not a valid literal for `T` —
/// including the empty string and text that is not valid UTF-8. This is
/// deliberate: an operator who sets a lever is running an experiment, and
/// silently running the default arm instead would hand them a measurement of
/// something other than what they asked for.
pub fn cap<T>(var: &str, shipped: T) -> T
where
    T: FromStr,
    <T as FromStr>::Err: Display,
{
    match std::env::var_os(var) {
        None => shipped,
        Some(raw) => {
            let Some(text) = raw.to_str() else {
                panic!(
                    "{var} is set to a value that is not valid UTF-8. A config lever is an \
                     experiment; refusing rather than silently measuring the shipped default."
                )
            };
            parse_cap(var, text)
        }
    }
}

/// The lever's parsing rules, separated from the environment read.
///
/// A test that sets a process-wide environment variable is a gate on one shell
/// and races every other test in a threaded suite, so the decision lives here
/// and [`cap`] is the thin read — the same split `parse_multiple_lever` uses in
/// `axeyum-solver`'s SAT backend.
///
/// # Panics
///
/// Panics when `text` is not a valid literal for `T`. See [`cap`] for why this
/// is not a fallback to the shipped value.
pub fn parse_cap<T>(var: &str, text: &str) -> T
where
    T: FromStr,
    <T as FromStr>::Err: Display,
{
    let trimmed = text.trim();
    // `4_096` is how the shipped caps are written at their definition sites, so
    // it must be how a lever can be written too; `FromStr` does not accept it.
    let literal: String = trimmed.chars().filter(|c| *c != '_').collect();
    if literal.is_empty() {
        panic!(
            "{var} is set but empty. A config lever must name a value; to use the shipped \
             default, UNSET the variable (`env -u {var} …`) rather than clearing it."
        );
    }
    literal.parse::<T>().unwrap_or_else(|error| {
        panic!(
            "{var}={text:?} is not a valid {ty}: {error}. A config lever is an experiment; \
             refusing rather than silently measuring the shipped default.",
            ty = std::any::type_name::<T>()
        )
    })
}

/// Declares a cached accessor for one compiled cap, overridable by one
/// environment variable.
///
/// The compiled `const` stays exactly where it is and keeps its value; the
/// accessor is what comparison sites call. With the variable unset the accessor
/// returns the `const`, so wiring a cap changes no behaviour.
///
/// ```
/// const MAX_ATOMS: usize = 16;
///
/// axeyum_ir::cap_lever! {
///     /// The effective atom ceiling: [`MAX_ATOMS`], or `AXEYUM_EXAMPLE_MAX_ATOMS`.
///     // Deliberately NOT the name of a real lever: `config_registry`'s
///     // `every_env_override_is_read_by_the_code` scans the workspace for the
///     // quoted literal, and an example naming a shipped variable would make
///     // that check pass for a lever whose only read had been deleted.
///     fn max_atoms() -> usize = "AXEYUM_EXAMPLE_MAX_ATOMS" or MAX_ATOMS;
/// }
///
/// assert_eq!(max_atoms(), MAX_ATOMS);
/// ```
#[macro_export]
macro_rules! cap_lever {
    (
        $(#[$attr:meta])*
        $vis:vis fn $name:ident() -> $ty:ty = $var:literal or $shipped:expr;
    ) => {
        $(#[$attr])*
        #[must_use]
        $vis fn $name() -> $ty {
            static RESOLVED: ::std::sync::OnceLock<$ty> = ::std::sync::OnceLock::new();
            *RESOLVED.get_or_init(|| $crate::config_lever::cap::<$ty>($var, $shipped))
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_plain_literal_parses() {
        assert_eq!(parse_cap::<usize>("AXEYUM_X", "4096"), 4096);
        assert_eq!(parse_cap::<u32>("AXEYUM_X", "128"), 128);
        assert_eq!(parse_cap::<i128>("AXEYUM_X", "-5"), -5);
    }

    #[test]
    fn underscores_and_surrounding_space_are_accepted() {
        assert_eq!(parse_cap::<usize>("AXEYUM_X", "4_096"), 4096);
        assert_eq!(parse_cap::<usize>("AXEYUM_X", "  4_096 "), 4096);
    }

    #[test]
    #[should_panic(expected = "is not a valid")]
    fn garbage_is_refused_not_silently_defaulted() {
        let _ = parse_cap::<usize>("AXEYUM_X", "sixteen");
    }

    #[test]
    #[should_panic(expected = "is not a valid")]
    fn an_out_of_range_value_is_refused() {
        let _ = parse_cap::<u32>("AXEYUM_X", "99999999999999999999");
    }

    #[test]
    #[should_panic(expected = "is not a valid")]
    fn a_negative_value_for_an_unsigned_cap_is_refused() {
        let _ = parse_cap::<usize>("AXEYUM_X", "-1");
    }

    #[test]
    #[should_panic(expected = "set but empty")]
    fn the_empty_string_is_refused() {
        let _ = parse_cap::<usize>("AXEYUM_X", "");
    }

    #[test]
    #[should_panic(expected = "set but empty")]
    fn whitespace_only_is_refused() {
        let _ = parse_cap::<usize>("AXEYUM_X", "   ");
    }

    /// The property every wired cap depends on: with the variable absent, the
    /// shipped value comes back unchanged.
    ///
    /// Uses a variable name no lever uses, so it does not race a suite that
    /// sets a real one.
    #[test]
    fn an_absent_variable_keeps_the_shipped_value() {
        assert_eq!(cap("AXEYUM_NO_SUCH_LEVER_FOR_A_TEST", 4_096usize), 4_096);
    }

    /// The macro's accessor is the shipped constant when nothing is set.
    #[test]
    fn the_macro_accessor_defaults_to_the_shipped_constant() {
        const SHIPPED: usize = 37;
        cap_lever! {
            /// Test accessor.
            fn shipped_lever() -> usize = "AXEYUM_NO_SUCH_LEVER_FOR_A_MACRO_TEST" or SHIPPED;
        }
        assert_eq!(shipped_lever(), SHIPPED);
    }
}

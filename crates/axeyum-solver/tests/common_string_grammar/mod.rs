//! Shared **literal-grammar coverage** gate for the string differential fuzzers.
//!
//! # Why this exists (a soundness trap the P0 already sprang)
//!
//! The string differential fuzzers render literals as SMT-LIB text and feed the
//! *same* text to axeyum and the oracle (Z3 / cvc5), so a mistake in axeyum's
//! `\u{…}` escape **decoder** surfaces as a differential disagreement — but only if
//! the generated corpus actually *contains* escapes. The escape-decoding P0
//! (`ba0d9149`) existed precisely because every generator emitted plain ASCII, so
//! the escape decoder was never exercised and the fuzz stayed green while blind.
//!
//! The generators now emit `\u{…}` escapes (and, for the byte-model generators, a
//! `>0x7F` boundary code point) **by convention** — but nothing forced them to. A
//! future cleanup could silently drop that emission back to plain ASCII and every
//! escape-sensitive fuzz would stay green (0 disagreements) while no longer testing
//! the decoder at all.
//!
//! This module turns that convention into an **enforced invariant**: a generator
//! wires a [`GrammarCoverage`] accumulator over the batch it generates and calls
//! [`GrammarCoverage::assert_escape_coverage`] /
//! [`GrammarCoverage::assert_boundary_coverage`]. If the generator regresses to
//! plain ASCII the coverage fractions collapse and the assertion **fails the test**
//! — a hard gate, not a log line.

#![allow(dead_code)]

/// Accumulated escape / boundary coverage over a batch of generated SMT-LIB
/// scripts. Feed every generated script's text through [`GrammarCoverage::observe`],
/// then assert the coverage floors.
#[derive(Debug, Default, Clone)]
pub struct GrammarCoverage {
    /// Total scripts observed.
    total: u64,
    /// Scripts whose text contains at least one `\u` escape (either `\u{…}` or the
    /// bare four-hex-digit `\uXXXX` form).
    with_escape: u64,
    /// Scripts whose text contains at least one code point strictly above `0x7F`
    /// — an escaped code point that decodes to `> 0x7F`, or a raw non-ASCII byte.
    with_boundary: u64,
}

impl GrammarCoverage {
    /// A fresh, empty accumulator.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Record one generated script's SMT-LIB text.
    pub fn observe(&mut self, script_text: &str) {
        self.total += 1;
        if script_contains_escape(script_text) {
            self.with_escape += 1;
        }
        if script_contains_boundary_codepoint(script_text) {
            self.with_boundary += 1;
        }
    }

    /// Fraction of observed scripts that carry an escape.
    #[must_use]
    pub fn escape_fraction(&self) -> f64 {
        fraction(self.with_escape, self.total)
    }

    /// Fraction of observed scripts that carry a `> 0x7F` boundary code point.
    #[must_use]
    pub fn boundary_fraction(&self) -> f64 {
        fraction(self.with_boundary, self.total)
    }

    /// Hard-assert that at least `min_fraction` of the batch carried an escape.
    ///
    /// # Panics
    ///
    /// Panics (failing the test) if fewer than `min_fraction` of the observed
    /// scripts contained a `\u` escape — i.e. the generator has regressed toward
    /// plain ASCII and no longer exercises the escape decoder.
    pub fn assert_escape_coverage(&self, min_fraction: f64, label: &str) {
        assert!(self.total > 0, "[{label}] no scripts observed");
        let frac = self.escape_fraction();
        assert!(
            frac >= min_fraction,
            "[{label}] ESCAPE COVERAGE REGRESSION: only {}/{} ({:.1}%) generated scripts \
             carry a `\\u` escape, below the required {:.1}% floor — the generator has \
             drifted to plain ASCII and no longer exercises the escape decoder (the \
             `ba0d9149` P0 class). Restore escape emission in its literal generator.",
            self.with_escape,
            self.total,
            frac * 100.0,
            min_fraction * 100.0,
        );
    }

    /// Hard-assert that at least `min_fraction` of the batch carried a `> 0x7F`
    /// boundary code point.
    ///
    /// # Panics
    ///
    /// Panics (failing the test) if fewer than `min_fraction` of the observed
    /// scripts contained a code point above `0x7F` — i.e. the generator has stopped
    /// stressing the high half of the byte model where the escape decoder's boundary
    /// arithmetic lives.
    pub fn assert_boundary_coverage(&self, min_fraction: f64, label: &str) {
        assert!(self.total > 0, "[{label}] no scripts observed");
        let frac = self.boundary_fraction();
        assert!(
            frac >= min_fraction,
            "[{label}] BOUNDARY COVERAGE REGRESSION: only {}/{} ({:.1}%) generated scripts \
             carry a `>0x7F` code point, below the required {:.1}% floor — the generator has \
             stopped exercising the high half of the byte model (the escape decoder's \
             boundary path). Restore the `>0x7F` boundary escape in its literal generator.",
            self.with_boundary,
            self.total,
            frac * 100.0,
            min_fraction * 100.0,
        );
    }
}

/// A small-count fraction `numerator / denominator` (both bounded by the batch size,
/// so the widening is lossless in practice). `0.0` for an empty batch.
fn fraction(numerator: u64, denominator: u64) -> f64 {
    if denominator == 0 {
        return 0.0;
    }
    // The counts are bounded by the generated-batch size (< 2^32), so the u32 cast
    // is exact and `f64::from` is lossless — no `cast_precision_loss`.
    let num = u32::try_from(numerator).unwrap_or(u32::MAX);
    let den = u32::try_from(denominator).unwrap_or(u32::MAX);
    f64::from(num) / f64::from(den)
}

/// Does the SMT-LIB text carry at least one `\u` escape? Matches both the SMT-LIB
/// `\u{…}` braced form and the bare `\uXXXX` four-hex-digit form.
#[must_use]
pub fn script_contains_escape(text: &str) -> bool {
    let bytes = text.as_bytes();
    let mut i = 0;
    while i + 1 < bytes.len() {
        if bytes[i] == b'\\' && bytes[i + 1] == b'u' {
            return true;
        }
        i += 1;
    }
    false
}

/// Does the SMT-LIB text carry at least one code point strictly above `0x7F`?
///
/// Counts an escaped code point (`\u{HEX}` or `\uXXXX`) that decodes above `0x7F`,
/// and any raw non-ASCII byte in the text.
#[must_use]
pub fn script_contains_boundary_codepoint(text: &str) -> bool {
    // Any raw non-ASCII scalar already clears the boundary.
    if text.chars().any(|c| c as u32 > 0x7F) {
        return true;
    }
    let bytes = text.as_bytes();
    let mut i = 0;
    while i + 1 < bytes.len() {
        if bytes[i] == b'\\'
            && bytes[i + 1] == b'u'
            && let Some(cp) = decode_escape_at(bytes, i + 2)
            && cp > 0x7F
        {
            return true;
        }
        i += 1;
    }
    false
}

/// Decode the code point of a `\u` escape whose hex payload starts at `start`
/// (either `{HEX}` or four bare hex digits). Returns `None` for a malformed escape.
fn decode_escape_at(bytes: &[u8], start: usize) -> Option<u32> {
    if bytes.get(start) == Some(&b'{') {
        // Braced form `\u{HEX}` (1..=5 hex digits per SMT-LIB).
        let mut j = start + 1;
        let mut value: u32 = 0;
        let mut digits = 0;
        while j < bytes.len() && bytes[j] != b'}' {
            let d = (bytes[j] as char).to_digit(16)?;
            value = value.checked_mul(16)?.checked_add(d)?;
            digits += 1;
            j += 1;
        }
        if digits == 0 { None } else { Some(value) }
    } else {
        // Bare four-hex-digit form `\uXXXX`.
        let mut value: u32 = 0;
        for k in 0..4 {
            let d = (*bytes.get(start + k)? as char).to_digit(16)?;
            value = value * 16 + d;
        }
        Some(value)
    }
}

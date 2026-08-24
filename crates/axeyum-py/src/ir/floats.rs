//! `axeyum.ir.fp` — the 60 floating-point formula builders.
//!
//! Every builder writes IEEE 754 semantics into bit-vector terms over the
//! caller's arena; there is no separate FP solver. Two shapes exist and are
//! kept apart deliberately:
//!
//! * `-> Term` builders always produce a term.
//! * `-> Term | None` builders are **constant folders**: `None` means "the
//!   argument was not a constant", which is not an error and is not `False`.

#![allow(
    // PyO3's calling convention hands `PyRef`/`PyRefMut` guards and owned
    // `Vec<Term>` arguments in by value; there is no by-reference form.
    clippy::needless_pass_by_value,
    clippy::trivially_copy_pass_by_ref
)]

use axeyum_fp::{FloatFormat, RoundingMode};
use pyo3::prelude::*;
use pyo3::types::PyModule;

use crate::ir::arena::Arena;
use crate::ir::types::{Term, map_ir_error};

/// An IEEE 754 (or ML) floating-point format: `(exp_bits, sig_bits)`.
///
/// `sig_bits` includes the hidden bit, so `F32` is `(8, 24)` and a value of
/// this format is `exp_bits + sig_bits` bits wide.
#[pyclass(frozen, from_py_object, module = "axeyum", name = "FloatFormat")]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PyFloatFormat {
    pub(crate) format: FloatFormat,
}

#[pymethods]
impl PyFloatFormat {
    #[new]
    fn new(exp_bits: u32, sig_bits: u32) -> Self {
        Self {
            format: FloatFormat { exp_bits, sig_bits },
        }
    }

    /// Exponent bits.
    #[getter]
    fn exp_bits(&self) -> u32 {
        self.format.exp_bits
    }

    /// Significand bits, including the hidden bit.
    #[getter]
    fn sig_bits(&self) -> u32 {
        self.format.sig_bits
    }

    /// Total bit width of a value in this format.
    fn width(&self) -> u32 {
        self.format.width()
    }

    /// Whether the format follows IEEE conventions.
    ///
    /// `FP8_E4M3` and `FP4_E2M1` do not (no infinities, different NaN rules);
    /// the generic builders are **not** correct for them and their dedicated
    /// `e4m3_*` / `e2m1_*` helpers must be used instead.
    fn is_ieee(&self) -> bool {
        self.format.is_ieee()
    }

    fn __repr__(&self) -> String {
        format!(
            "FloatFormat(exp_bits={}, sig_bits={})",
            self.format.exp_bits, self.format.sig_bits
        )
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        other
            .cast::<Self>()
            .is_ok_and(|o| self.format == o.get().format)
    }

    fn __hash__(&self) -> u64 {
        (u64::from(self.format.exp_bits) << 32) | u64::from(self.format.sig_bits)
    }
}

/// One of the five SMT-LIB rounding modes.
#[pyclass(
    frozen,
    eq,
    eq_int,
    from_py_object,
    module = "axeyum",
    name = "RoundingMode"
)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PyRoundingMode {
    /// Round to nearest, ties to even (`RNE`).
    NearestTiesToEven,
    /// Round to nearest, ties away from zero (`RNA`).
    NearestTiesToAway,
    /// Round toward positive infinity (`RTP`).
    TowardPositive,
    /// Round toward negative infinity (`RTN`).
    TowardNegative,
    /// Round toward zero (`RTZ`).
    TowardZero,
}

impl From<PyRoundingMode> for RoundingMode {
    fn from(mode: PyRoundingMode) -> Self {
        match mode {
            PyRoundingMode::NearestTiesToEven => RoundingMode::NearestEven,
            PyRoundingMode::NearestTiesToAway => RoundingMode::NearestAway,
            PyRoundingMode::TowardPositive => RoundingMode::TowardPositive,
            PyRoundingMode::TowardNegative => RoundingMode::TowardNegative,
            PyRoundingMode::TowardZero => RoundingMode::TowardZero,
        }
    }
}

/// Builds a pyfunction for each uniform floating-point builder shape.
macro_rules! fp_fns {
    // fn(arena, x) -> Term
    (arg1 $($name:ident),* $(,)?) => {
        $(
            #[doc = concat!("`axeyum_fp::", stringify!($name), "`.")]
            #[pyfunction]
            pub fn $name(mut arena: PyRefMut<'_, Arena>, x: Term) -> PyResult<Term> {
                let epoch = arena.epoch;
                let x = x.resolve(epoch)?;
                let id = axeyum_fp::$name(&mut arena.arena, x).map_err(|e| map_ir_error(&e))?;
                Ok(Term::new(epoch, id))
            }
        )*
    };
    // fn(arena, x) -> Option<Term>
    (arg1opt $($name:ident),* $(,)?) => {
        $(
            #[doc = concat!("`axeyum_fp::", stringify!($name), "`. `None` = argument not constant, never an error.")]
            #[pyfunction]
            pub fn $name(mut arena: PyRefMut<'_, Arena>, x: Term) -> PyResult<Option<Term>> {
                let epoch = arena.epoch;
                let x = x.resolve(epoch)?;
                let id = axeyum_fp::$name(&mut arena.arena, x).map_err(|e| map_ir_error(&e))?;
                Ok(id.map(|id| Term::new(epoch, id)))
            }
        )*
    };
    // fn(arena, fmt, x) -> Term
    (fmt1 $($name:ident),* $(,)?) => {
        $(
            #[doc = concat!("`axeyum_fp::", stringify!($name), "` over one operand of `fmt`.")]
            #[pyfunction]
            pub fn $name(mut arena: PyRefMut<'_, Arena>, fmt: PyFloatFormat, x: Term) -> PyResult<Term> {
                let epoch = arena.epoch;
                let x = x.resolve(epoch)?;
                let id = axeyum_fp::$name(&mut arena.arena, fmt.format, x).map_err(|e| map_ir_error(&e))?;
                Ok(Term::new(epoch, id))
            }
        )*
    };
    // fn(arena, fmt, x) -> Option<Term>
    (fmt1opt $($name:ident),* $(,)?) => {
        $(
            #[doc = concat!("`axeyum_fp::", stringify!($name), "`. `None` = argument not constant.")]
            #[pyfunction]
            pub fn $name(mut arena: PyRefMut<'_, Arena>, fmt: PyFloatFormat, x: Term) -> PyResult<Option<Term>> {
                let epoch = arena.epoch;
                let x = x.resolve(epoch)?;
                let id = axeyum_fp::$name(&mut arena.arena, fmt.format, x).map_err(|e| map_ir_error(&e))?;
                Ok(id.map(|id| Term::new(epoch, id)))
            }
        )*
    };
    // fn(arena, fmt, x, y) -> Term
    (fmt2 $($name:ident),* $(,)?) => {
        $(
            #[doc = concat!("`axeyum_fp::", stringify!($name), "` over two operands of `fmt`.")]
            #[pyfunction]
            pub fn $name(mut arena: PyRefMut<'_, Arena>, fmt: PyFloatFormat, x: Term, y: Term) -> PyResult<Term> {
                let epoch = arena.epoch;
                let x = x.resolve(epoch)?;
                let y = y.resolve(epoch)?;
                let id = axeyum_fp::$name(&mut arena.arena, fmt.format, x, y).map_err(|e| map_ir_error(&e))?;
                Ok(Term::new(epoch, id))
            }
        )*
    };
    // fn(arena, fmt, x, y) -> Option<Term>
    (fmt2opt $($name:ident),* $(,)?) => {
        $(
            #[doc = concat!("`axeyum_fp::", stringify!($name), "`. `None` = an operand is not constant.")]
            #[pyfunction]
            pub fn $name(mut arena: PyRefMut<'_, Arena>, fmt: PyFloatFormat, x: Term, y: Term) -> PyResult<Option<Term>> {
                let epoch = arena.epoch;
                let x = x.resolve(epoch)?;
                let y = y.resolve(epoch)?;
                let id = axeyum_fp::$name(&mut arena.arena, fmt.format, x, y).map_err(|e| map_ir_error(&e))?;
                Ok(id.map(|id| Term::new(epoch, id)))
            }
        )*
    };
    // fn(arena, fmt, a, b, mode) -> Term
    (fmt2mode $($name:ident),* $(,)?) => {
        $(
            #[doc = concat!("`axeyum_fp::", stringify!($name), "` with an explicit rounding mode.")]
            #[pyfunction]
            pub fn $name(mut arena: PyRefMut<'_, Arena>, fmt: PyFloatFormat, a: Term, b: Term, mode: PyRoundingMode) -> PyResult<Term> {
                let epoch = arena.epoch;
                let a = a.resolve(epoch)?;
                let b = b.resolve(epoch)?;
                let id = axeyum_fp::$name(&mut arena.arena, fmt.format, a, b, mode.into()).map_err(|e| map_ir_error(&e))?;
                Ok(Term::new(epoch, id))
            }
        )*
    };
}

fp_fns!(arg1 e4m3_is_nan, e4m3_is_zero, e4m3_is_subnormal, e4m3_is_normal,
        e2m1_is_zero, e2m1_is_subnormal, e2m1_is_normal, count_leading_zeros);
fp_fns!(arg1opt e2m1_to_real);
fp_fns!(fmt1 is_nan, is_infinite, is_zero, is_subnormal, is_normal, is_negative,
        is_positive, abs, neg);
fp_fns!(fmt1opt to_real, sqrt_rne);
fp_fns!(fmt2 eq, lt, leq, gt, geq, min, max, rem_sym);
fp_fns!(fmt2opt add_rne, sub_rne, mul_rne, div_rne, rem);
fp_fns!(fmt2mode add, sub, mul, div);

/// `axeyum_fp::sqrt` with an explicit rounding mode.
#[pyfunction]
pub fn sqrt(
    mut arena: PyRefMut<'_, Arena>,
    fmt: PyFloatFormat,
    x: Term,
    mode: PyRoundingMode,
) -> PyResult<Term> {
    let epoch = arena.epoch;
    let x = x.resolve(epoch)?;
    let id = axeyum_fp::sqrt(&mut arena.arena, fmt.format, x, mode.into())
        .map_err(|e| map_ir_error(&e))?;
    Ok(Term::new(epoch, id))
}

/// `axeyum_fp::fma` — fused multiply-add `a * b + c`, one rounding.
#[pyfunction]
pub fn fma(
    mut arena: PyRefMut<'_, Arena>,
    fmt: PyFloatFormat,
    a: Term,
    b: Term,
    c: Term,
    mode: PyRoundingMode,
) -> PyResult<Term> {
    let epoch = arena.epoch;
    let a = a.resolve(epoch)?;
    let b = b.resolve(epoch)?;
    let c = c.resolve(epoch)?;
    let id = axeyum_fp::fma(&mut arena.arena, fmt.format, a, b, c, mode.into())
        .map_err(|e| map_ir_error(&e))?;
    Ok(Term::new(epoch, id))
}

/// `axeyum_fp::fma_rne`; `None` = an operand is not constant.
#[pyfunction]
pub fn fma_rne(
    mut arena: PyRefMut<'_, Arena>,
    fmt: PyFloatFormat,
    x: Term,
    y: Term,
    z: Term,
) -> PyResult<Option<Term>> {
    let epoch = arena.epoch;
    let x = x.resolve(epoch)?;
    let y = y.resolve(epoch)?;
    let z = z.resolve(epoch)?;
    let id =
        axeyum_fp::fma_rne(&mut arena.arena, fmt.format, x, y, z).map_err(|e| map_ir_error(&e))?;
    Ok(id.map(|id| Term::new(epoch, id)))
}

/// `axeyum_fp::to_fp` — reformat between two float formats.
#[pyfunction]
pub fn to_fp(
    mut arena: PyRefMut<'_, Arena>,
    src: PyFloatFormat,
    dst: PyFloatFormat,
    mode: PyRoundingMode,
    x: Term,
) -> PyResult<Term> {
    let epoch = arena.epoch;
    let x = x.resolve(epoch)?;
    let id = axeyum_fp::to_fp(&mut arena.arena, src.format, dst.format, mode.into(), x)
        .map_err(|e| map_ir_error(&e))?;
    Ok(Term::new(epoch, id))
}

/// `axeyum_fp::from_ubv` — unsigned bit-vector to float.
#[pyfunction]
pub fn from_ubv(
    mut arena: PyRefMut<'_, Arena>,
    dst: PyFloatFormat,
    mode: PyRoundingMode,
    x: Term,
) -> PyResult<Term> {
    let epoch = arena.epoch;
    let x = x.resolve(epoch)?;
    let id = axeyum_fp::from_ubv(&mut arena.arena, dst.format, mode.into(), x)
        .map_err(|e| map_ir_error(&e))?;
    Ok(Term::new(epoch, id))
}

/// `axeyum_fp::from_sbv` — signed bit-vector to float.
#[pyfunction]
pub fn from_sbv(
    mut arena: PyRefMut<'_, Arena>,
    dst: PyFloatFormat,
    mode: PyRoundingMode,
    x: Term,
) -> PyResult<Term> {
    let epoch = arena.epoch;
    let x = x.resolve(epoch)?;
    let id = axeyum_fp::from_sbv(&mut arena.arena, dst.format, mode.into(), x)
        .map_err(|e| map_ir_error(&e))?;
    Ok(Term::new(epoch, id))
}

/// `axeyum_fp::from_real` — an exact rational to a float constant;
/// `None` = not representable.
#[pyfunction]
pub fn from_real(
    mut arena: PyRefMut<'_, Arena>,
    dst: PyFloatFormat,
    mode: PyRoundingMode,
    num: i128,
    den: i128,
) -> PyResult<Option<Term>> {
    let epoch = arena.epoch;
    let rational = axeyum_ir::Rational::checked_new(num, den).ok_or_else(|| {
        crate::error::AxeyumError::new_err(format!("{num}/{den} is not a representable rational"))
    })?;
    let id = axeyum_fp::from_real(&mut arena.arena, dst.format, mode.into(), rational)
        .map_err(|e| map_ir_error(&e))?;
    Ok(id.map(|id| Term::new(epoch, id)))
}

/// `axeyum_fp::round_to_integral`; `None` = argument not constant.
#[pyfunction]
pub fn round_to_integral(
    mut arena: PyRefMut<'_, Arena>,
    fmt: PyFloatFormat,
    mode: PyRoundingMode,
    x: Term,
) -> PyResult<Option<Term>> {
    let epoch = arena.epoch;
    let x = x.resolve(epoch)?;
    let id = axeyum_fp::round_to_integral(&mut arena.arena, fmt.format, mode.into(), x)
        .map_err(|e| map_ir_error(&e))?;
    Ok(id.map(|id| Term::new(epoch, id)))
}

/// `axeyum_fp::round_to_integral_sym` — the symbolic (always-a-term) form.
#[pyfunction]
pub fn round_to_integral_sym(
    mut arena: PyRefMut<'_, Arena>,
    fmt: PyFloatFormat,
    mode: PyRoundingMode,
    x: Term,
) -> PyResult<Term> {
    let epoch = arena.epoch;
    let x = x.resolve(epoch)?;
    let id = axeyum_fp::round_to_integral_sym(&mut arena.arena, fmt.format, mode.into(), x)
        .map_err(|e| map_ir_error(&e))?;
    Ok(Term::new(epoch, id))
}

/// `axeyum_fp::ubv_to_fp`; `None` = argument not constant.
#[pyfunction]
pub fn ubv_to_fp(
    mut arena: PyRefMut<'_, Arena>,
    fmt: PyFloatFormat,
    bv: Term,
    mode: PyRoundingMode,
) -> PyResult<Option<Term>> {
    let epoch = arena.epoch;
    let bv = bv.resolve(epoch)?;
    let id = axeyum_fp::ubv_to_fp(&mut arena.arena, fmt.format, bv, mode.into())
        .map_err(|e| map_ir_error(&e))?;
    Ok(id.map(|id| Term::new(epoch, id)))
}

/// `axeyum_fp::sbv_to_fp`; `None` = argument not constant.
#[pyfunction]
pub fn sbv_to_fp(
    mut arena: PyRefMut<'_, Arena>,
    fmt: PyFloatFormat,
    bv: Term,
    mode: PyRoundingMode,
) -> PyResult<Option<Term>> {
    let epoch = arena.epoch;
    let bv = bv.resolve(epoch)?;
    let id = axeyum_fp::sbv_to_fp(&mut arena.arena, fmt.format, bv, mode.into())
        .map_err(|e| map_ir_error(&e))?;
    Ok(id.map(|id| Term::new(epoch, id)))
}

/// `axeyum_fp::to_ubv`; `None` = argument not constant.
#[pyfunction]
pub fn to_ubv(
    mut arena: PyRefMut<'_, Arena>,
    fmt: PyFloatFormat,
    mode: PyRoundingMode,
    x: Term,
    width: u32,
) -> PyResult<Option<Term>> {
    let epoch = arena.epoch;
    let x = x.resolve(epoch)?;
    let id = axeyum_fp::to_ubv(&mut arena.arena, fmt.format, mode.into(), x, width)
        .map_err(|e| map_ir_error(&e))?;
    Ok(id.map(|id| Term::new(epoch, id)))
}

/// `axeyum_fp::to_sbv`; `None` = argument not constant.
#[pyfunction]
pub fn to_sbv(
    mut arena: PyRefMut<'_, Arena>,
    fmt: PyFloatFormat,
    mode: PyRoundingMode,
    x: Term,
    width: u32,
) -> PyResult<Option<Term>> {
    let epoch = arena.epoch;
    let x = x.resolve(epoch)?;
    let id = axeyum_fp::to_sbv(&mut arena.arena, fmt.format, mode.into(), x, width)
        .map_err(|e| map_ir_error(&e))?;
    Ok(id.map(|id| Term::new(epoch, id)))
}

/// `axeyum_fp::to_ubv_sym` — the symbolic form, with the caller's `fresh`
/// bit-vector standing for the out-of-range result.
#[pyfunction]
pub fn to_ubv_sym(
    mut arena: PyRefMut<'_, Arena>,
    fmt: PyFloatFormat,
    mode: PyRoundingMode,
    x: Term,
    width: u32,
    fresh: Term,
) -> PyResult<Term> {
    let epoch = arena.epoch;
    let x = x.resolve(epoch)?;
    let fresh = fresh.resolve(epoch)?;
    let id = axeyum_fp::to_ubv_sym(&mut arena.arena, fmt.format, mode.into(), x, width, fresh)
        .map_err(|e| map_ir_error(&e))?;
    Ok(Term::new(epoch, id))
}

/// `axeyum_fp::to_sbv_sym` — the symbolic signed form.
#[pyfunction]
pub fn to_sbv_sym(
    mut arena: PyRefMut<'_, Arena>,
    fmt: PyFloatFormat,
    mode: PyRoundingMode,
    x: Term,
    width: u32,
    fresh: Term,
) -> PyResult<Term> {
    let epoch = arena.epoch;
    let x = x.resolve(epoch)?;
    let fresh = fresh.resolve(epoch)?;
    let id = axeyum_fp::to_sbv_sym(&mut arena.arena, fmt.format, mode.into(), x, width, fresh)
        .map_err(|e| map_ir_error(&e))?;
    Ok(Term::new(epoch, id))
}

/// `axeyum_fp::to_real_sym` — the symbolic form of the float-to-real bridge.
#[pyfunction]
pub fn to_real_sym(
    mut arena: PyRefMut<'_, Arena>,
    fmt: PyFloatFormat,
    x: Term,
    exceptional: Term,
) -> PyResult<Term> {
    let epoch = arena.epoch;
    let x = x.resolve(epoch)?;
    let exceptional = exceptional.resolve(epoch)?;
    let id = axeyum_fp::to_real_sym(&mut arena.arena, fmt.format, x, exceptional)
        .map_err(|e| map_ir_error(&e))?;
    Ok(Term::new(epoch, id))
}

/// `axeyum_fp::round_significand` — keep `keep` significand bits.
#[pyfunction]
pub fn round_significand(mut arena: PyRefMut<'_, Arena>, sig: Term, keep: u32) -> PyResult<Term> {
    let epoch = arena.epoch;
    let sig = sig.resolve(epoch)?;
    let id =
        axeyum_fp::round_significand(&mut arena.arena, sig, keep).map_err(|e| map_ir_error(&e))?;
    Ok(Term::new(epoch, id))
}

/// `axeyum_fp::round_variable` — the shared rounding gadget.
#[pyfunction]
pub fn round_variable(
    mut arena: PyRefMut<'_, Arena>,
    m: Term,
    drop: Term,
    mode: PyRoundingMode,
    negative: Term,
) -> PyResult<Term> {
    let epoch = arena.epoch;
    let m = m.resolve(epoch)?;
    let drop = drop.resolve(epoch)?;
    let negative = negative.resolve(epoch)?;
    let id = axeyum_fp::round_variable(&mut arena.arena, m, drop, mode.into(), negative)
        .map_err(|e| map_ir_error(&e))?;
    Ok(Term::new(epoch, id))
}

/// `axeyum_fp::isqrt` — the integer square root gadget, as `(root, remainder)`.
#[pyfunction]
pub fn isqrt(mut arena: PyRefMut<'_, Arena>, n: Term) -> PyResult<(Term, Term)> {
    let epoch = arena.epoch;
    let n = n.resolve(epoch)?;
    let (root, rem) = axeyum_fp::isqrt(&mut arena.arena, n).map_err(|e| map_ir_error(&e))?;
    Ok((Term::new(epoch, root), Term::new(epoch, rem)))
}

/// `axeyum_fp::pack_params` — `(m_w, e)` normalization, as `(m, e)` terms.
#[pyfunction]
pub fn pack_params(
    mut arena: PyRefMut<'_, Arena>,
    m_w: Term,
    e: Term,
    sb: u32,
    bias: i64,
) -> PyResult<(Term, Term)> {
    let epoch = arena.epoch;
    let m_w = m_w.resolve(epoch)?;
    let e = e.resolve(epoch)?;
    let (m, e) = axeyum_fp::pack_params(&mut arena.arena, m_w, e, sb, bias)
        .map_err(|err| map_ir_error(&err))?;
    Ok((Term::new(epoch, m), Term::new(epoch, e)))
}

/// `axeyum_fp::pack_value` — assemble a float from sign/significand/exponent.
#[pyfunction]
#[allow(clippy::too_many_arguments)]
pub fn pack_value(
    mut arena: PyRefMut<'_, Arena>,
    eb: u32,
    sb: u32,
    sign: Term,
    m: Term,
    e: Term,
    mode: PyRoundingMode,
) -> PyResult<Term> {
    let epoch = arena.epoch;
    let sign = sign.resolve(epoch)?;
    let m = m.resolve(epoch)?;
    let e = e.resolve(epoch)?;
    let id = axeyum_fp::pack_value(&mut arena.arena, eb, sb, sign, m, e, mode.into())
        .map_err(|err| map_ir_error(&err))?;
    Ok(Term::new(epoch, id))
}

/// `axeyum_fp::round_to_format` — a concrete `f64` rounded into `(eb, sb)`,
/// returned as the raw bit pattern.
#[pyfunction]
pub fn round_to_format(eb: u32, sb: u32, value: f64, mode: PyRoundingMode) -> u128 {
    axeyum_fp::round_to_format(eb, sb, value, mode.into())
}

/// `axeyum_fp::round_rational_to_format`; `None` = not representable.
#[pyfunction]
pub fn round_rational_to_format(
    eb: u32,
    sb: u32,
    num: i128,
    den: i128,
    mode: PyRoundingMode,
) -> Option<u128> {
    axeyum_fp::round_rational_to_format(eb, sb, num, den, mode.into())
}

/// Builds the `ir.fp` submodule.
pub(crate) fn register<'py>(parent: &Bound<'py, PyModule>) -> PyResult<Bound<'py, PyModule>> {
    let py = parent.py();
    let module = PyModule::new(py, "axeyum._native.ir.fp")?;
    module.add(
        "__doc__",
        "tier R -- the 60 IEEE 754 formula builders; the folders return None for \
         'not constant'.",
    )?;
    module.add_class::<PyFloatFormat>()?;
    module.add_class::<PyRoundingMode>()?;

    macro_rules! add {
        ($($name:ident),* $(,)?) => {
            $( module.add_function(wrap_pyfunction!($name, &module)?)?; )*
        };
    }
    add!(
        e4m3_is_nan,
        e4m3_is_zero,
        e4m3_is_subnormal,
        e4m3_is_normal,
        e2m1_is_zero,
        e2m1_is_subnormal,
        e2m1_is_normal,
        e2m1_to_real,
        count_leading_zeros,
        is_nan,
        is_infinite,
        is_zero,
        is_subnormal,
        is_normal,
        is_negative,
        is_positive,
        abs,
        neg,
        to_real,
        sqrt_rne,
        eq,
        lt,
        leq,
        gt,
        geq,
        min,
        max,
        rem_sym,
        add_rne,
        sub_rne,
        mul_rne,
        div_rne,
        rem,
        add,
        sub,
        mul,
        div,
        sqrt,
        fma,
        fma_rne,
        to_fp,
        from_ubv,
        from_sbv,
        from_real,
        round_to_integral,
        round_to_integral_sym,
        ubv_to_fp,
        sbv_to_fp,
        to_ubv,
        to_sbv,
        to_ubv_sym,
        to_sbv_sym,
        to_real_sym,
        round_significand,
        round_variable,
        isqrt,
        pack_params,
        pack_value,
        round_to_format,
        round_rational_to_format,
    );

    for (name, format) in [
        ("F16", FloatFormat::F16),
        ("F32", FloatFormat::F32),
        ("F64", FloatFormat::F64),
        ("F128", FloatFormat::F128),
        ("BF16", FloatFormat::BF16),
        ("TF32", FloatFormat::TF32),
        ("FP8_E5M2", FloatFormat::FP8_E5M2),
        ("FP8_E4M3", FloatFormat::FP8_E4M3),
        ("FP4_E2M1", FloatFormat::FP4_E2M1),
    ] {
        module.add(name, PyFloatFormat { format })?;
    }
    parent.add("fp", &module)?;
    Ok(module)
}

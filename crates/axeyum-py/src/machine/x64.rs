//! Python projection of the source-pinned x86-64 teaching slice.

#![allow(clippy::needless_pass_by_value)]

use axeyum_machine::x64;
use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;
use pyo3::types::{PyBytes, PyModule};

use super::a0::Memory;

fn encoding_error(error: x64::EncodingError) -> PyErr {
    PyValueError::new_err(format!("x86-64 encoding error: {error:?}"))
}

fn projection_error(error: x64::ProjectionError) -> PyErr {
    PyValueError::new_err(format!("x86-64 projection error: {error:?}"))
}

fn condition(value: &str) -> PyResult<x64::Condition> {
    match value.to_ascii_lowercase().as_str() {
        "equal" | "e" | "z" => Ok(x64::Condition::Equal),
        "not-equal" | "ne" | "nz" => Ok(x64::Condition::NotEqual),
        "not-sign" | "ns" => Ok(x64::Condition::NotSign),
        _ => Err(PyValueError::new_err(
            "x86-64 condition must be equal, not-equal, or not-sign",
        )),
    }
}

const fn condition_name(value: x64::Condition) -> &'static str {
    match value {
        x64::Condition::Equal => "equal",
        x64::Condition::NotEqual => "not-equal",
        x64::Condition::NotSign => "not-sign",
    }
}

const fn flag_name(value: x64::FlagValue) -> &'static str {
    match value {
        x64::FlagValue::Clear => "clear",
        x64::FlagValue::Set => "set",
        x64::FlagValue::Undefined => "undefined",
    }
}

fn flag_value(value: &str) -> PyResult<x64::FlagValue> {
    match value.to_ascii_lowercase().as_str() {
        "clear" => Ok(x64::FlagValue::Clear),
        "set" => Ok(x64::FlagValue::Set),
        "undefined" => Ok(x64::FlagValue::Undefined),
        _ => Err(PyValueError::new_err(
            "x86-64 flag value must be clear, set, or undefined",
        )),
    }
}

#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.machine.x64")
)]
#[pyclass(
    frozen,
    eq,
    from_py_object,
    module = "axeyum.machine.x64",
    name = "Instruction"
)]
#[derive(Clone, PartialEq, Eq)]
pub(crate) struct Instruction {
    inner: x64::Instruction,
}

fn validated(inner: x64::Instruction) -> PyResult<Instruction> {
    x64::encode(inner).map_err(encoding_error)?;
    Ok(Instruction { inner })
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl Instruction {
    #[staticmethod]
    fn xor32(destination: u8, source: u8) -> PyResult<Self> {
        validated(x64::Instruction::Xor32 {
            destination,
            source,
        })
    }

    #[staticmethod]
    fn move_immediate32(destination: u8, immediate: u32) -> PyResult<Self> {
        validated(x64::Instruction::MoveImmediate32 {
            destination,
            immediate,
        })
    }

    #[staticmethod]
    fn test64(lhs: u8, rhs: u8) -> PyResult<Self> {
        validated(x64::Instruction::Test64 { lhs, rhs })
    }

    #[staticmethod]
    fn jump_short(condition_value: &str, displacement: i8) -> PyResult<Self> {
        validated(x64::Instruction::JumpShort {
            condition: condition(condition_value)?,
            displacement,
        })
    }

    #[staticmethod]
    fn xor64_memory(destination: u8, base: u8) -> PyResult<Self> {
        validated(x64::Instruction::Xor64Memory { destination, base })
    }

    #[staticmethod]
    fn add_immediate64(destination: u8, immediate: i8) -> PyResult<Self> {
        validated(x64::Instruction::AddImmediate64 {
            destination,
            immediate,
        })
    }

    #[staticmethod]
    fn sub_immediate64(destination: u8, immediate: i8) -> PyResult<Self> {
        validated(x64::Instruction::SubImmediate64 {
            destination,
            immediate,
        })
    }

    #[staticmethod]
    fn move64(destination: u8, source: u8) -> PyResult<Self> {
        validated(x64::Instruction::Move64 {
            destination,
            source,
        })
    }

    #[staticmethod]
    fn negate64(destination: u8) -> PyResult<Self> {
        validated(x64::Instruction::Negate64 { destination })
    }

    #[staticmethod]
    fn load_effective_address64(destination: u8, base: u8, displacement: i8) -> PyResult<Self> {
        validated(x64::Instruction::LoadEffectiveAddress64 {
            destination,
            base,
            displacement,
        })
    }

    #[staticmethod]
    fn push64(source: u8) -> PyResult<Self> {
        validated(x64::Instruction::Push64 { source })
    }

    #[staticmethod]
    fn pop64(destination: u8) -> PyResult<Self> {
        validated(x64::Instruction::Pop64 { destination })
    }

    #[staticmethod]
    fn call_relative(displacement: i32) -> PyResult<Self> {
        validated(x64::Instruction::CallRelative { displacement })
    }

    #[staticmethod]
    fn add64(destination: u8, source: u8) -> PyResult<Self> {
        validated(x64::Instruction::Add64 {
            destination,
            source,
        })
    }

    #[staticmethod]
    fn return_() -> PyResult<Self> {
        validated(x64::Instruction::Return)
    }

    #[staticmethod]
    fn decode(bytes: Vec<u8>) -> PyResult<(Instruction, usize)> {
        let (inner, length) = x64::decode(&bytes).map_err(encoding_error)?;
        Ok((Self { inner }, length))
    }

    fn encode<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyBytes>> {
        let bytes = x64::encode(self.inner).map_err(encoding_error)?;
        Ok(PyBytes::new(py, &bytes))
    }

    #[getter]
    fn kind(&self) -> &'static str {
        match self.inner {
            x64::Instruction::Xor32 { .. } => "xor32",
            x64::Instruction::MoveImmediate32 { .. } => "move-immediate32",
            x64::Instruction::Test64 { .. } => "test64",
            x64::Instruction::JumpShort { .. } => "jump-short",
            x64::Instruction::Xor64Memory { .. } => "xor64-memory",
            x64::Instruction::AddImmediate64 { .. } => "add-immediate64",
            x64::Instruction::SubImmediate64 { .. } => "sub-immediate64",
            x64::Instruction::Move64 { .. } => "move64",
            x64::Instruction::Negate64 { .. } => "negate64",
            x64::Instruction::LoadEffectiveAddress64 { .. } => "load-effective-address64",
            x64::Instruction::Push64 { .. } => "push64",
            x64::Instruction::Pop64 { .. } => "pop64",
            x64::Instruction::CallRelative { .. } => "call-relative",
            x64::Instruction::Add64 { .. } => "add64",
            x64::Instruction::Return => "return",
        }
    }

    #[getter]
    fn destination(&self) -> Option<u8> {
        match self.inner {
            x64::Instruction::Xor32 { destination, .. }
            | x64::Instruction::MoveImmediate32 { destination, .. }
            | x64::Instruction::Xor64Memory { destination, .. }
            | x64::Instruction::AddImmediate64 { destination, .. }
            | x64::Instruction::SubImmediate64 { destination, .. }
            | x64::Instruction::Move64 { destination, .. }
            | x64::Instruction::Negate64 { destination }
            | x64::Instruction::LoadEffectiveAddress64 { destination, .. }
            | x64::Instruction::Pop64 { destination }
            | x64::Instruction::Add64 { destination, .. } => Some(destination),
            _ => None,
        }
    }

    #[getter]
    fn source(&self) -> Option<u8> {
        match self.inner {
            x64::Instruction::Xor32 { source, .. }
            | x64::Instruction::Move64 { source, .. }
            | x64::Instruction::Push64 { source }
            | x64::Instruction::Add64 { source, .. } => Some(source),
            _ => None,
        }
    }

    #[getter]
    fn base(&self) -> Option<u8> {
        match self.inner {
            x64::Instruction::Xor64Memory { base, .. }
            | x64::Instruction::LoadEffectiveAddress64 { base, .. } => Some(base),
            _ => None,
        }
    }

    #[getter]
    fn lhs(&self) -> Option<u8> {
        match self.inner {
            x64::Instruction::Test64 { lhs, .. } => Some(lhs),
            _ => None,
        }
    }

    #[getter]
    fn rhs(&self) -> Option<u8> {
        match self.inner {
            x64::Instruction::Test64 { rhs, .. } => Some(rhs),
            _ => None,
        }
    }

    #[getter]
    fn immediate(&self) -> Option<i64> {
        match self.inner {
            x64::Instruction::MoveImmediate32 { immediate, .. } => Some(i64::from(immediate)),
            x64::Instruction::AddImmediate64 { immediate, .. }
            | x64::Instruction::SubImmediate64 { immediate, .. } => Some(i64::from(immediate)),
            _ => None,
        }
    }

    #[getter]
    fn displacement(&self) -> Option<i64> {
        match self.inner {
            x64::Instruction::JumpShort { displacement, .. }
            | x64::Instruction::LoadEffectiveAddress64 { displacement, .. } => {
                Some(i64::from(displacement))
            }
            x64::Instruction::CallRelative { displacement } => Some(i64::from(displacement)),
            _ => None,
        }
    }

    #[getter]
    fn condition(&self) -> Option<&'static str> {
        match self.inner {
            x64::Instruction::JumpShort { condition, .. } => Some(condition_name(condition)),
            _ => None,
        }
    }

    fn __repr__(&self) -> String {
        format!(
            "Instruction(kind={:?}, detail={:?})",
            self.kind(),
            self.inner
        )
    }
}

#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.machine.x64")
)]
#[pyclass(
    frozen,
    eq,
    from_py_object,
    module = "axeyum.machine.x64",
    name = "Flags"
)]
#[derive(Clone, PartialEq, Eq)]
pub(crate) struct Flags {
    inner: x64::Flags,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl Flags {
    #[new]
    #[pyo3(signature = (carry="clear", parity="clear", auxiliary="clear", zero="clear", sign="clear", overflow="clear"))]
    fn new(
        carry: &str,
        parity: &str,
        auxiliary: &str,
        zero: &str,
        sign: &str,
        overflow: &str,
    ) -> PyResult<Self> {
        Ok(Self {
            inner: x64::Flags {
                carry: flag_value(carry)?,
                parity: flag_value(parity)?,
                auxiliary: flag_value(auxiliary)?,
                zero: flag_value(zero)?,
                sign: flag_value(sign)?,
                overflow: flag_value(overflow)?,
            },
        })
    }

    #[getter]
    fn carry(&self) -> &'static str {
        flag_name(self.inner.carry)
    }
    #[getter]
    fn parity(&self) -> &'static str {
        flag_name(self.inner.parity)
    }
    #[getter]
    fn auxiliary(&self) -> &'static str {
        flag_name(self.inner.auxiliary)
    }
    #[getter]
    fn zero(&self) -> &'static str {
        flag_name(self.inner.zero)
    }
    #[getter]
    fn sign(&self) -> &'static str {
        flag_name(self.inner.sign)
    }
    #[getter]
    fn overflow(&self) -> &'static str {
        flag_name(self.inner.overflow)
    }
}

#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.machine.x64")
)]
#[pyclass(
    frozen,
    from_py_object,
    module = "axeyum.machine.x64",
    name = "Program"
)]
#[derive(Clone)]
pub(crate) struct Program {
    inner: x64::Program,
    base: u64,
    code: Vec<u8>,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl Program {
    #[new]
    fn new(base: u64, code: Vec<u8>) -> Self {
        Self {
            inner: x64::Program::new(base, code.clone()),
            base,
            code,
        }
    }
    #[getter]
    fn base(&self) -> u64 {
        self.base
    }
    #[getter]
    fn code<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(py, &self.code)
    }
}

#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.machine.x64")
)]
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "axeyum.machine.x64",
    name = "Trap"
)]
#[derive(Clone)]
pub(crate) struct Trap {
    inner: x64::Trap,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl Trap {
    #[getter]
    fn kind(&self) -> &'static str {
        match self.inner {
            x64::Trap::IncompleteInstructionFetch { .. } => "incomplete-instruction-fetch",
            x64::Trap::IllegalInstruction { .. } => "illegal-instruction",
            x64::Trap::DataAccessFault { .. } => "data-access-fault",
        }
    }
    #[getter]
    fn rip(&self) -> Option<u64> {
        match self.inner {
            x64::Trap::IncompleteInstructionFetch { rip }
            | x64::Trap::IllegalInstruction { rip } => Some(rip),
            x64::Trap::DataAccessFault { .. } => None,
        }
    }
    #[getter]
    fn address(&self) -> Option<u64> {
        match self.inner {
            x64::Trap::DataAccessFault { address, .. } => Some(address),
            _ => None,
        }
    }
    #[getter]
    fn access_bytes(&self) -> Option<usize> {
        match self.inner {
            x64::Trap::DataAccessFault { bytes, .. } => Some(bytes),
            _ => None,
        }
    }
}

#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.machine.x64")
)]
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "axeyum.machine.x64",
    name = "Outcome"
)]
#[derive(Clone)]
pub(crate) struct Outcome {
    inner: x64::Outcome,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl Outcome {
    #[getter]
    fn kind(&self) -> &'static str {
        match self.inner {
            x64::Outcome::Running => "running",
            x64::Outcome::Trapped(_) => "trapped",
        }
    }
    #[getter]
    fn trap(&self) -> Option<Trap> {
        match &self.inner {
            x64::Outcome::Trapped(inner) => Some(Trap {
                inner: inner.clone(),
            }),
            x64::Outcome::Running => None,
        }
    }
}

#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.machine.x64")
)]
#[pyclass(frozen, from_py_object, module = "axeyum.machine.x64", name = "State")]
#[derive(Clone)]
pub(crate) struct State {
    inner: x64::State,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl State {
    #[new]
    fn new(memory: &Memory, rip: u64) -> Self {
        Self {
            inner: x64::State::new(memory.inner.clone(), rip),
        }
    }
    fn register(&self, index: u8) -> PyResult<u64> {
        if index >= 8 {
            return Err(PyValueError::new_err(
                "x86-64 register index must be 0 through 7",
            ));
        }
        Ok(self.inner.register(index))
    }
    #[getter]
    fn registers(&self) -> Vec<u64> {
        self.inner.registers.to_vec()
    }
    #[getter]
    fn flags(&self) -> Flags {
        Flags {
            inner: self.inner.flags,
        }
    }
    #[getter]
    fn memory(&self) -> Memory {
        Memory {
            inner: self.inner.memory.clone(),
        }
    }
    #[getter]
    fn rip(&self) -> u64 {
        self.inner.rip
    }
    #[getter]
    fn outcome(&self) -> Outcome {
        Outcome {
            inner: self.inner.outcome.clone(),
        }
    }
    fn with_register(&self, index: u8, value: u64) -> PyResult<Self> {
        if index >= 8 {
            return Err(PyValueError::new_err(
                "x86-64 register index must be 0 through 7",
            ));
        }
        let mut inner = self.inner.clone();
        inner.registers[usize::from(index)] = value;
        Ok(Self { inner })
    }
    fn with_flags(&self, flags: Flags) -> Self {
        let mut inner = self.inner.clone();
        inner.flags = flags.inner;
        Self { inner }
    }
}

#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.machine.x64")
)]
#[pyclass(frozen, module = "axeyum.machine.x64", name = "StateProjection")]
pub(crate) struct StateProjection {
    inner: x64::StateProjection,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl StateProjection {
    #[getter]
    fn registers(&self) -> Vec<(u8, u64)> {
        self.inner.registers.clone()
    }
    #[getter]
    fn flags(&self) -> Flags {
        Flags {
            inner: self.inner.flags,
        }
    }
    #[getter]
    fn memory(&self) -> Vec<(u64, u8)> {
        self.inner.memory.clone()
    }
    #[getter]
    fn rip(&self) -> u64 {
        self.inner.rip
    }
    #[getter]
    fn outcome(&self) -> Outcome {
        Outcome {
            inner: self.inner.outcome.clone(),
        }
    }
}

#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.machine.x64")
)]
#[pyfunction]
fn step(program: &Program, state: &State) -> State {
    State {
        inner: x64::step(&program.inner, &state.inner),
    }
}

#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.machine.x64")
)]
#[pyfunction]
fn project_state(state: &State, registers: Vec<u8>) -> PyResult<StateProjection> {
    Ok(StateProjection {
        inner: x64::project_state(&state.inner, registers).map_err(projection_error)?,
    })
}

pub(crate) fn register<'py>(parent: &Bound<'py, PyModule>) -> PyResult<Bound<'py, PyModule>> {
    let py = parent.py();
    let module = PyModule::new(py, "axeyum._native.machine.x64")?;
    module.add(
        "__doc__",
        "tier R -- source-pinned x86-64 teaching slice projected from Rust.",
    )?;
    module.add("SOURCE_REVISION", x64::SOURCE_REVISION)?;
    module.add("SOURCE_SHA256", x64::SOURCE_SHA256)?;
    module.add("SELECTED_FORMS", x64::SELECTED_FORMS.to_vec())?;
    module.add_class::<Instruction>()?;
    module.add_class::<Flags>()?;
    module.add_class::<Program>()?;
    module.add_class::<Trap>()?;
    module.add_class::<Outcome>()?;
    module.add_class::<State>()?;
    module.add_class::<StateProjection>()?;
    module.add_function(wrap_pyfunction!(step, &module)?)?;
    module.add_function(wrap_pyfunction!(project_state, &module)?)?;
    parent.add("x64", &module)?;
    Ok(module)
}

#[cfg(feature = "stub-gen")]
mod stub_variables {
    pyo3_stub_gen::module_variable!("axeyum._native.machine.x64", "SOURCE_REVISION", String);
    pyo3_stub_gen::module_variable!("axeyum._native.machine.x64", "SOURCE_SHA256", String);
    pyo3_stub_gen::module_variable!("axeyum._native.machine.x64", "SELECTED_FORMS", Vec<String>);
}

//! Python projection of the source-pinned RV64I teaching slice.

#![allow(clippy::needless_pass_by_value)]

use axeyum_machine::rv64;
use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;
use pyo3::types::{PyBytes, PyModule};

use super::a0::Memory;

fn encoding_error(error: rv64::EncodingError) -> PyErr {
    PyValueError::new_err(format!("RV64 encoding error: {error:?}"))
}

fn projection_error(error: rv64::ProjectionError) -> PyErr {
    PyValueError::new_err(format!("RV64 projection error: {error:?}"))
}

#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.machine.rv64")
)]
#[pyclass(
    frozen,
    eq,
    from_py_object,
    module = "axeyum.machine.rv64",
    name = "Instruction"
)]
#[derive(Clone, PartialEq, Eq)]
pub(crate) struct Instruction {
    inner: rv64::Instruction,
}

fn validated(inner: rv64::Instruction) -> PyResult<Instruction> {
    rv64::encode(inner).map_err(encoding_error)?;
    Ok(Instruction { inner })
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl Instruction {
    #[staticmethod]
    fn add_immediate(rd: u8, rs1: u8, immediate: i16) -> PyResult<Self> {
        validated(rv64::Instruction::AddImmediate { rd, rs1, immediate })
    }

    #[staticmethod]
    fn add(rd: u8, rs1: u8, rs2: u8) -> PyResult<Self> {
        validated(rv64::Instruction::Add { rd, rs1, rs2 })
    }

    #[staticmethod]
    fn sub(rd: u8, rs1: u8, rs2: u8) -> PyResult<Self> {
        validated(rv64::Instruction::Sub { rd, rs1, rs2 })
    }

    #[staticmethod]
    fn or_(rd: u8, rs1: u8, rs2: u8) -> PyResult<Self> {
        validated(rv64::Instruction::Or { rd, rs1, rs2 })
    }

    #[staticmethod]
    fn xor(rd: u8, rs1: u8, rs2: u8) -> PyResult<Self> {
        validated(rv64::Instruction::Xor { rd, rs1, rs2 })
    }

    #[staticmethod]
    fn load_double(rd: u8, rs1: u8, immediate: i16) -> PyResult<Self> {
        validated(rv64::Instruction::LoadDouble { rd, rs1, immediate })
    }

    #[staticmethod]
    fn store_double(rs1: u8, rs2: u8, immediate: i16) -> PyResult<Self> {
        validated(rv64::Instruction::StoreDouble {
            rs1,
            rs2,
            immediate,
        })
    }

    #[staticmethod]
    fn branch_equal(rs1: u8, rs2: u8, offset: i16) -> PyResult<Self> {
        validated(rv64::Instruction::BranchEqual { rs1, rs2, offset })
    }

    #[staticmethod]
    fn branch_not_equal(rs1: u8, rs2: u8, offset: i16) -> PyResult<Self> {
        validated(rv64::Instruction::BranchNotEqual { rs1, rs2, offset })
    }

    #[staticmethod]
    fn branch_greater_equal(rs1: u8, rs2: u8, offset: i16) -> PyResult<Self> {
        validated(rv64::Instruction::BranchGreaterEqual { rs1, rs2, offset })
    }

    #[staticmethod]
    fn jump_and_link(rd: u8, offset: i32) -> PyResult<Self> {
        validated(rv64::Instruction::JumpAndLink { rd, offset })
    }

    #[staticmethod]
    fn jump_and_link_register(rd: u8, rs1: u8, immediate: i16) -> PyResult<Self> {
        validated(rv64::Instruction::JumpAndLinkRegister { rd, rs1, immediate })
    }

    #[staticmethod]
    fn decode(word: u32) -> PyResult<Self> {
        Ok(Self {
            inner: rv64::decode(word).map_err(encoding_error)?,
        })
    }

    fn encode(&self) -> PyResult<u32> {
        rv64::encode(self.inner).map_err(encoding_error)
    }

    #[getter]
    fn kind(&self) -> &'static str {
        match self.inner {
            rv64::Instruction::AddImmediate { .. } => "addi",
            rv64::Instruction::Add { .. } => "add",
            rv64::Instruction::Sub { .. } => "sub",
            rv64::Instruction::Or { .. } => "or",
            rv64::Instruction::Xor { .. } => "xor",
            rv64::Instruction::LoadDouble { .. } => "ld",
            rv64::Instruction::StoreDouble { .. } => "sd",
            rv64::Instruction::BranchEqual { .. } => "beq",
            rv64::Instruction::BranchNotEqual { .. } => "bne",
            rv64::Instruction::BranchGreaterEqual { .. } => "bge",
            rv64::Instruction::JumpAndLink { .. } => "jal",
            rv64::Instruction::JumpAndLinkRegister { .. } => "jalr",
        }
    }

    #[getter]
    fn rd(&self) -> Option<u8> {
        match self.inner {
            rv64::Instruction::AddImmediate { rd, .. }
            | rv64::Instruction::Add { rd, .. }
            | rv64::Instruction::Sub { rd, .. }
            | rv64::Instruction::Or { rd, .. }
            | rv64::Instruction::Xor { rd, .. }
            | rv64::Instruction::LoadDouble { rd, .. }
            | rv64::Instruction::JumpAndLink { rd, .. }
            | rv64::Instruction::JumpAndLinkRegister { rd, .. } => Some(rd),
            rv64::Instruction::StoreDouble { .. }
            | rv64::Instruction::BranchEqual { .. }
            | rv64::Instruction::BranchNotEqual { .. }
            | rv64::Instruction::BranchGreaterEqual { .. } => None,
        }
    }

    #[getter]
    fn rs1(&self) -> Option<u8> {
        match self.inner {
            rv64::Instruction::AddImmediate { rs1, .. }
            | rv64::Instruction::Add { rs1, .. }
            | rv64::Instruction::Sub { rs1, .. }
            | rv64::Instruction::Or { rs1, .. }
            | rv64::Instruction::Xor { rs1, .. }
            | rv64::Instruction::LoadDouble { rs1, .. }
            | rv64::Instruction::StoreDouble { rs1, .. }
            | rv64::Instruction::BranchEqual { rs1, .. }
            | rv64::Instruction::BranchNotEqual { rs1, .. }
            | rv64::Instruction::BranchGreaterEqual { rs1, .. }
            | rv64::Instruction::JumpAndLinkRegister { rs1, .. } => Some(rs1),
            rv64::Instruction::JumpAndLink { .. } => None,
        }
    }

    #[getter]
    fn rs2(&self) -> Option<u8> {
        match self.inner {
            rv64::Instruction::Add { rs2, .. }
            | rv64::Instruction::Sub { rs2, .. }
            | rv64::Instruction::Or { rs2, .. }
            | rv64::Instruction::Xor { rs2, .. }
            | rv64::Instruction::StoreDouble { rs2, .. }
            | rv64::Instruction::BranchEqual { rs2, .. }
            | rv64::Instruction::BranchNotEqual { rs2, .. }
            | rv64::Instruction::BranchGreaterEqual { rs2, .. } => Some(rs2),
            _ => None,
        }
    }

    #[getter]
    fn immediate(&self) -> Option<i32> {
        match self.inner {
            rv64::Instruction::AddImmediate { immediate, .. }
            | rv64::Instruction::LoadDouble { immediate, .. }
            | rv64::Instruction::StoreDouble { immediate, .. }
            | rv64::Instruction::JumpAndLinkRegister { immediate, .. } => {
                Some(i32::from(immediate))
            }
            _ => None,
        }
    }

    #[getter]
    fn offset(&self) -> Option<i32> {
        match self.inner {
            rv64::Instruction::BranchEqual { offset, .. }
            | rv64::Instruction::BranchNotEqual { offset, .. }
            | rv64::Instruction::BranchGreaterEqual { offset, .. } => Some(i32::from(offset)),
            rv64::Instruction::JumpAndLink { offset, .. } => Some(offset),
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
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.machine.rv64")
)]
#[pyclass(
    frozen,
    from_py_object,
    module = "axeyum.machine.rv64",
    name = "Program"
)]
#[derive(Clone)]
pub(crate) struct Program {
    inner: rv64::Program,
    base: u64,
    code: Vec<u8>,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl Program {
    #[new]
    fn new(base: u64, code: Vec<u8>) -> Self {
        Self {
            inner: rv64::Program::new(base, code.clone()),
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
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.machine.rv64")
)]
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "axeyum.machine.rv64",
    name = "Trap"
)]
#[derive(Clone)]
pub(crate) struct Trap {
    inner: rv64::Trap,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl Trap {
    #[getter]
    fn kind(&self) -> &'static str {
        match self.inner {
            rv64::Trap::InstructionAddressMisaligned { .. } => "instruction-address-misaligned",
            rv64::Trap::IncompleteInstructionFetch { .. } => "incomplete-instruction-fetch",
            rv64::Trap::IllegalInstruction { .. } => "illegal-instruction",
            rv64::Trap::DataAddressMisaligned { .. } => "data-address-misaligned",
            rv64::Trap::DataAccessFault { .. } => "data-access-fault",
        }
    }

    #[getter]
    fn pc(&self) -> Option<u64> {
        match self.inner {
            rv64::Trap::InstructionAddressMisaligned { pc }
            | rv64::Trap::IncompleteInstructionFetch { pc }
            | rv64::Trap::IllegalInstruction { pc, .. } => Some(pc),
            _ => None,
        }
    }

    #[getter]
    fn address(&self) -> Option<u64> {
        match self.inner {
            rv64::Trap::DataAddressMisaligned { address }
            | rv64::Trap::DataAccessFault { address, .. } => Some(address),
            _ => None,
        }
    }

    #[getter]
    fn instruction_word(&self) -> Option<u32> {
        match self.inner {
            rv64::Trap::IllegalInstruction { word, .. } => Some(word),
            _ => None,
        }
    }

    #[getter]
    fn access_bytes(&self) -> Option<usize> {
        match self.inner {
            rv64::Trap::DataAccessFault { bytes, .. } => Some(bytes),
            _ => None,
        }
    }
}

#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.machine.rv64")
)]
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "axeyum.machine.rv64",
    name = "Outcome"
)]
#[derive(Clone)]
pub(crate) struct Outcome {
    inner: rv64::Outcome,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl Outcome {
    #[getter]
    fn kind(&self) -> &'static str {
        match self.inner {
            rv64::Outcome::Running => "running",
            rv64::Outcome::Trapped(_) => "trapped",
        }
    }

    #[getter]
    fn trap(&self) -> Option<Trap> {
        match &self.inner {
            rv64::Outcome::Trapped(inner) => Some(Trap {
                inner: inner.clone(),
            }),
            rv64::Outcome::Running => None,
        }
    }
}

#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.machine.rv64")
)]
#[pyclass(frozen, from_py_object, module = "axeyum.machine.rv64", name = "State")]
#[derive(Clone)]
pub(crate) struct State {
    inner: rv64::State,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl State {
    #[new]
    fn new(memory: &Memory, pc: u64) -> Self {
        Self {
            inner: rv64::State::new(memory.inner.clone(), pc),
        }
    }

    fn register(&self, index: u8) -> PyResult<u64> {
        if index >= 32 {
            return Err(PyValueError::new_err(
                "RV64 register index must be 0 through 31",
            ));
        }
        Ok(self.inner.register(index))
    }

    #[getter]
    fn registers(&self) -> Vec<u64> {
        (0..32).map(|index| self.inner.register(index)).collect()
    }

    #[getter]
    fn memory(&self) -> Memory {
        Memory {
            inner: self.inner.memory.clone(),
        }
    }

    #[getter]
    fn pc(&self) -> u64 {
        self.inner.pc
    }

    #[getter]
    fn outcome(&self) -> Outcome {
        Outcome {
            inner: self.inner.outcome.clone(),
        }
    }

    fn with_register(&self, index: u8, value: u64) -> PyResult<Self> {
        if index >= 32 {
            return Err(PyValueError::new_err(
                "RV64 register index must be 0 through 31",
            ));
        }
        let mut inner = self.inner.clone();
        if index != 0 {
            inner.registers[usize::from(index)] = value;
        }
        inner.registers[0] = 0;
        Ok(Self { inner })
    }
}

#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.machine.rv64")
)]
#[pyclass(frozen, module = "axeyum.machine.rv64", name = "StateProjection")]
pub(crate) struct StateProjection {
    inner: rv64::StateProjection,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl StateProjection {
    #[getter]
    fn registers(&self) -> Vec<(u8, u64)> {
        self.inner.registers.clone()
    }

    #[getter]
    fn memory(&self) -> Vec<(u64, u8)> {
        self.inner.memory.clone()
    }

    #[getter]
    fn pc(&self) -> u64 {
        self.inner.pc
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
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.machine.rv64")
)]
#[pyfunction]
fn step(program: &Program, state: &State) -> State {
    State {
        inner: rv64::step(&program.inner, &state.inner),
    }
}

#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.machine.rv64")
)]
#[pyfunction]
fn project_state(state: &State, registers: Vec<u8>) -> PyResult<StateProjection> {
    Ok(StateProjection {
        inner: rv64::project_state(&state.inner, registers).map_err(projection_error)?,
    })
}

pub(crate) fn register<'py>(parent: &Bound<'py, PyModule>) -> PyResult<Bound<'py, PyModule>> {
    let py = parent.py();
    let module = PyModule::new(py, "axeyum._native.machine.rv64")?;
    module.add(
        "__doc__",
        "tier R -- source-pinned RV64I teaching slice projected from Rust.",
    )?;
    module.add("SOURCE_RELEASE", rv64::SOURCE_RELEASE)?;
    module.add("SOURCE_SHA256", rv64::SOURCE_SHA256)?;
    module.add("RV64I_VERSION", rv64::RV64I_VERSION)?;
    module.add("SELECTED_FORMS", rv64::SELECTED_FORMS.to_vec())?;
    module.add_class::<Instruction>()?;
    module.add_class::<Program>()?;
    module.add_class::<Trap>()?;
    module.add_class::<Outcome>()?;
    module.add_class::<State>()?;
    module.add_class::<StateProjection>()?;
    module.add_function(wrap_pyfunction!(step, &module)?)?;
    module.add_function(wrap_pyfunction!(project_state, &module)?)?;
    parent.add("rv64", &module)?;
    Ok(module)
}

#[cfg(feature = "stub-gen")]
mod stub_variables {
    pyo3_stub_gen::module_variable!("axeyum._native.machine.rv64", "SOURCE_RELEASE", String);
    pyo3_stub_gen::module_variable!("axeyum._native.machine.rv64", "SOURCE_SHA256", String);
    pyo3_stub_gen::module_variable!("axeyum._native.machine.rv64", "RV64I_VERSION", String);
    pyo3_stub_gen::module_variable!("axeyum._native.machine.rv64", "SELECTED_FORMS", Vec<String>);
}

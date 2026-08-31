//! Python projection of the executable A0 teaching machine.

// PyO3 extracts an owned `Vec<u8>` for a Python sequence, and `Result::map_err`
// consumes the Rust error before it becomes a Python exception.
#![allow(clippy::needless_pass_by_value)]

use axeyum_machine::a0;
use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;
use pyo3::types::{PyBytes, PyModule};

fn value_error(error: a0::A0Error) -> PyErr {
    PyValueError::new_err(error.to_string())
}

/// A fixed-width A0 word with arithmetic values reduced modulo `2**width`.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.machine.a0")
)]
#[pyclass(
    frozen,
    eq,
    from_py_object,
    module = "axeyum.machine.a0",
    name = "Word"
)]
#[derive(Clone, PartialEq, Eq)]
pub(crate) struct Word {
    inner: a0::Word,
}

impl From<a0::Word> for Word {
    fn from(inner: a0::Word) -> Self {
        Self { inner }
    }
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl Word {
    /// Construct a word, reducing `value` modulo `2**width`.
    #[new]
    fn new(width: u8, value: u64) -> PyResult<Self> {
        Ok(Self {
            inner: a0::Word::new(width, value).map_err(value_error)?,
        })
    }

    /// Construct a word by joining least-significant byte first.
    #[staticmethod]
    fn from_little_endian(bytes: Vec<u8>) -> PyResult<Self> {
        Ok(Self {
            inner: a0::Word::from_little_endian(&bytes).map_err(value_error)?,
        })
    }

    /// Width in bits.
    #[getter]
    fn width(&self) -> u8 {
        self.inner.width()
    }

    /// Unsigned reading of the stored bit pattern.
    #[getter]
    fn unsigned(&self) -> u64 {
        self.inner.unsigned()
    }

    /// Signed two's-complement reading of the stored bit pattern.
    #[getter]
    fn signed(&self) -> i128 {
        self.inner.signed()
    }

    /// Whether the most-significant bit is one.
    #[getter]
    fn high_bit(&self) -> bool {
        self.inner.high_bit()
    }

    /// Bytes from least significant to most significant.
    fn little_endian_bytes<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(py, &self.inner.little_endian_bytes())
    }

    /// Return the same pattern widened with zero high bits.
    fn zero_extend(&self, new_width: u8) -> PyResult<Self> {
        Ok(Self {
            inner: self.inner.zero_extend(new_width).map_err(value_error)?,
        })
    }

    /// Return the same signed value widened by repeating the sign bit.
    fn sign_extend(&self, new_width: u8) -> PyResult<Self> {
        Ok(Self {
            inner: self.inner.sign_extend(new_width).map_err(value_error)?,
        })
    }

    /// Keep only the least-significant `new_width` bits.
    fn truncate(&self, new_width: u8) -> PyResult<Self> {
        Ok(Self {
            inner: self.inner.truncate(new_width).map_err(value_error)?,
        })
    }

    fn __repr__(&self) -> String {
        format!("Word(width={}, value={:#x})", self.width(), self.unsigned())
    }

    fn __int__(&self) -> u64 {
        self.unsigned()
    }
}

/// A0's zero, negative, carry/no-borrow, and overflow conditions.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.machine.a0")
)]
#[pyclass(
    frozen,
    eq,
    from_py_object,
    module = "axeyum.machine.a0",
    name = "Conditions"
)]
#[derive(Clone, PartialEq, Eq)]
pub(crate) struct Conditions {
    inner: a0::Conditions,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl Conditions {
    #[new]
    #[pyo3(signature = (zero=false, negative=false, carry=false, overflow=false))]
    #[allow(clippy::fn_params_excessive_bools)]
    fn new(zero: bool, negative: bool, carry: bool, overflow: bool) -> Self {
        Self {
            inner: a0::Conditions {
                zero,
                negative,
                carry,
                overflow,
            },
        }
    }

    #[getter]
    fn zero(&self) -> bool {
        self.inner.zero
    }

    #[getter]
    fn negative(&self) -> bool {
        self.inner.negative
    }

    #[getter]
    fn carry(&self) -> bool {
        self.inner.carry
    }

    #[getter]
    fn overflow(&self) -> bool {
        self.inner.overflow
    }

    fn __repr__(&self) -> String {
        format!(
            "Conditions(zero={}, negative={}, carry={}, overflow={})",
            self.zero(),
            self.negative(),
            self.carry(),
            self.overflow()
        )
    }
}

/// Finite, byte-addressed A0 data memory.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.machine.a0")
)]
#[pyclass(
    frozen,
    eq,
    from_py_object,
    module = "axeyum.machine.a0",
    name = "Memory"
)]
#[derive(Clone, PartialEq, Eq)]
pub(crate) struct Memory {
    pub(super) inner: a0::Memory,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl Memory {
    /// Construct dense, zero-filled memory.
    #[staticmethod]
    fn zeroed(length: usize) -> Self {
        Self {
            inner: a0::Memory::zeroed(length),
        }
    }

    /// Construct dense memory whose first byte has address zero.
    #[staticmethod]
    fn from_bytes(bytes: Vec<u8>) -> Self {
        Self {
            inner: a0::Memory::from_bytes(bytes),
        }
    }

    /// Construct a sparse finite map; duplicate addresses are rejected.
    #[staticmethod]
    fn from_entries(entries: Vec<(u64, u8)>) -> PyResult<Self> {
        Ok(Self {
            inner: a0::Memory::from_entries(entries).map_err(value_error)?,
        })
    }

    fn __len__(&self) -> usize {
        self.inner.len()
    }

    fn __bool__(&self) -> bool {
        !self.inner.is_empty()
    }

    /// Read a mapped byte, or `None` when the address is outside the domain.
    fn byte_at(&self, address: u64) -> Option<u8> {
        self.inner.byte_at(address)
    }

    /// Canonically sorted `(address, byte)` pairs.
    fn entries(&self) -> Vec<(u64, u8)> {
        self.inner.entries().collect()
    }

    fn __repr__(&self) -> String {
        format!("Memory(entries={:?})", self.entries())
    }
}

/// Immutable A0 code bytes and their word-valued base address.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.machine.a0")
)]
#[pyclass(frozen, from_py_object, module = "axeyum.machine.a0", name = "Program")]
#[derive(Clone)]
pub(crate) struct Program {
    inner: a0::Program,
    code: Vec<u8>,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl Program {
    #[new]
    fn new(width: u8, base: &Word, code: Vec<u8>) -> PyResult<Self> {
        Ok(Self {
            inner: a0::Program::new(width, base.inner, code.clone()).map_err(value_error)?,
            code,
        })
    }

    #[getter]
    fn entry(&self) -> Word {
        self.inner.entry().into()
    }

    #[getter]
    fn code<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(py, &self.code)
    }

    fn __repr__(&self) -> String {
        format!(
            "Program(entry={}, code_bytes={})",
            self.inner.entry().unsigned(),
            self.code.len()
        )
    }
}

/// One categorized A0 execution trap.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.machine.a0")
)]
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "axeyum.machine.a0",
    name = "Trap"
)]
#[derive(Clone)]
pub(crate) struct Trap {
    inner: a0::Trap,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl Trap {
    #[getter]
    fn kind(&self) -> &'static str {
        match &self.inner {
            a0::Trap::MisalignedProgramCounter { .. } => "misaligned-program-counter",
            a0::Trap::IncompleteCodeFetch { .. } => "incomplete-code-fetch",
            a0::Trap::IllegalEncoding { .. } => "illegal-encoding",
            a0::Trap::DataRange { .. } => "data-range",
        }
    }

    #[getter]
    fn pc(&self) -> Option<u64> {
        match &self.inner {
            a0::Trap::MisalignedProgramCounter { pc }
            | a0::Trap::IncompleteCodeFetch { pc }
            | a0::Trap::IllegalEncoding { pc, .. } => Some(*pc),
            a0::Trap::DataRange { .. } => None,
        }
    }

    #[getter]
    fn address(&self) -> Option<u64> {
        match &self.inner {
            a0::Trap::DataRange { address, .. } => Some(*address),
            _ => None,
        }
    }

    #[getter]
    fn access_bytes(&self) -> Option<usize> {
        match &self.inner {
            a0::Trap::DataRange { bytes, .. } => Some(*bytes),
            _ => None,
        }
    }

    #[getter]
    fn memory_len(&self) -> Option<usize> {
        match &self.inner {
            a0::Trap::DataRange { memory_len, .. } => Some(*memory_len),
            _ => None,
        }
    }

    #[getter]
    fn encoding<'py>(&self, py: Python<'py>) -> Option<Bound<'py, PyBytes>> {
        match &self.inner {
            a0::Trap::IllegalEncoding { bytes, .. } => Some(PyBytes::new(py, bytes)),
            _ => None,
        }
    }

    fn __repr__(&self) -> String {
        format!("Trap(kind={:?}, detail={:?})", self.kind(), self.inner)
    }
}

/// Running, halted, or trapped A0 outcome.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.machine.a0")
)]
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "axeyum.machine.a0",
    name = "Outcome"
)]
#[derive(Clone)]
pub(crate) struct Outcome {
    inner: a0::Outcome,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl Outcome {
    #[getter]
    fn kind(&self) -> &'static str {
        match &self.inner {
            a0::Outcome::Running => "running",
            a0::Outcome::Halted => "halted",
            a0::Outcome::Trapped(_) => "trapped",
        }
    }

    #[getter]
    fn trap(&self) -> Option<Trap> {
        match &self.inner {
            a0::Outcome::Trapped(trap) => Some(Trap {
                inner: trap.clone(),
            }),
            _ => None,
        }
    }

    fn __repr__(&self) -> String {
        format!("Outcome(kind={:?}, detail={:?})", self.kind(), self.inner)
    }
}

/// Complete, owned A0 architectural state snapshot.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.machine.a0")
)]
#[pyclass(frozen, from_py_object, module = "axeyum.machine.a0", name = "State")]
#[derive(Clone)]
pub(crate) struct State {
    inner: a0::State,
}

impl State {
    fn validated(inner: a0::State) -> PyResult<Self> {
        a0::encode_state(&inner).map_err(value_error)?;
        Ok(Self { inner })
    }
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl State {
    #[new]
    fn new(width: u8, memory: &Memory, pc: &Word) -> PyResult<Self> {
        Ok(Self {
            inner: a0::State::new(width, memory.inner.clone(), pc.inner).map_err(value_error)?,
        })
    }

    #[staticmethod]
    fn decode(encoded: Vec<u8>) -> PyResult<Self> {
        Ok(Self {
            inner: a0::decode_state(&encoded).map_err(value_error)?,
        })
    }

    #[getter]
    fn width(&self) -> u8 {
        self.inner.width()
    }

    #[getter]
    fn registers(&self) -> Vec<Word> {
        self.inner.registers.into_iter().map(Word::from).collect()
    }

    fn register(&self, index: u8) -> PyResult<Word> {
        self.inner
            .registers
            .get(usize::from(index))
            .copied()
            .map(Word::from)
            .ok_or_else(|| PyValueError::new_err("A0 register index must be 0 through 7"))
    }

    #[getter]
    fn memory(&self) -> Memory {
        Memory {
            inner: self.inner.memory.clone(),
        }
    }

    #[getter]
    fn pc(&self) -> Word {
        self.inner.pc.into()
    }

    #[getter]
    fn conditions(&self) -> Conditions {
        Conditions {
            inner: self.inner.conditions,
        }
    }

    #[getter]
    fn outcome(&self) -> Outcome {
        Outcome {
            inner: self.inner.outcome.clone(),
        }
    }

    /// Return a validated snapshot with one register replaced.
    fn with_register(&self, index: u8, value: &Word) -> PyResult<Self> {
        let mut inner = self.inner.clone();
        let slot = inner
            .registers
            .get_mut(usize::from(index))
            .ok_or_else(|| PyValueError::new_err("A0 register index must be 0 through 7"))?;
        *slot = value.inner;
        Self::validated(inner)
    }

    /// Return a snapshot with the four condition bits replaced.
    fn with_conditions(&self, conditions: Conditions) -> PyResult<Self> {
        let mut inner = self.inner.clone();
        inner.conditions = conditions.inner;
        Self::validated(inner)
    }

    /// Canonical complete-state artifact bytes.
    fn encode<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyBytes>> {
        let encoded = a0::encode_state(&self.inner).map_err(value_error)?;
        Ok(PyBytes::new(py, &encoded))
    }

    fn __repr__(&self) -> String {
        format!(
            "State(width={}, pc={:#x}, outcome={:?})",
            self.width(),
            self.inner.pc.unsigned(),
            self.outcome().kind()
        )
    }
}

/// One decoded A0 instruction, constructed only through typed factories.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.machine.a0")
)]
#[pyclass(
    frozen,
    eq,
    from_py_object,
    module = "axeyum.machine.a0",
    name = "Instruction"
)]
#[derive(Clone, PartialEq, Eq)]
pub(crate) struct Instruction {
    inner: a0::Instruction,
}

fn validated_instruction(inner: a0::Instruction) -> PyResult<Instruction> {
    a0::encode(inner).map_err(value_error)?;
    Ok(Instruction { inner })
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl Instruction {
    #[staticmethod]
    fn mov(rd: u8, rs1: u8) -> PyResult<Self> {
        validated_instruction(a0::Instruction::Mov { rd, rs1 })
    }

    #[staticmethod]
    fn mov_immediate(rd: u8, immediate: i8) -> PyResult<Self> {
        validated_instruction(a0::Instruction::MovImmediate { rd, immediate })
    }

    #[staticmethod]
    fn load(rd: u8, base: u8, offset: i8) -> PyResult<Self> {
        validated_instruction(a0::Instruction::Load { rd, base, offset })
    }

    #[staticmethod]
    fn store(base: u8, source: u8, offset: i8) -> PyResult<Self> {
        validated_instruction(a0::Instruction::Store {
            base,
            source,
            offset,
        })
    }

    #[staticmethod]
    fn add(rd: u8, rs1: u8, rs2: u8) -> PyResult<Self> {
        validated_instruction(a0::Instruction::Add { rd, rs1, rs2 })
    }

    #[staticmethod]
    fn sub(rd: u8, rs1: u8, rs2: u8) -> PyResult<Self> {
        validated_instruction(a0::Instruction::Sub { rd, rs1, rs2 })
    }

    #[staticmethod]
    fn and_(rd: u8, rs1: u8, rs2: u8) -> PyResult<Self> {
        validated_instruction(a0::Instruction::And { rd, rs1, rs2 })
    }

    #[staticmethod]
    fn or_(rd: u8, rs1: u8, rs2: u8) -> PyResult<Self> {
        validated_instruction(a0::Instruction::Or { rd, rs1, rs2 })
    }

    #[staticmethod]
    fn xor(rd: u8, rs1: u8, rs2: u8) -> PyResult<Self> {
        validated_instruction(a0::Instruction::Xor { rd, rs1, rs2 })
    }

    #[staticmethod]
    fn shift_left(rd: u8, rs1: u8, rs2: u8) -> PyResult<Self> {
        validated_instruction(a0::Instruction::ShiftLeft { rd, rs1, rs2 })
    }

    #[staticmethod]
    fn shift_right(rd: u8, rs1: u8, rs2: u8) -> PyResult<Self> {
        validated_instruction(a0::Instruction::ShiftRight { rd, rs1, rs2 })
    }

    #[staticmethod]
    fn arithmetic_shift_right(rd: u8, rs1: u8, rs2: u8) -> PyResult<Self> {
        validated_instruction(a0::Instruction::ArithmeticShiftRight { rd, rs1, rs2 })
    }

    #[staticmethod]
    fn not_(rd: u8, rs1: u8) -> PyResult<Self> {
        validated_instruction(a0::Instruction::Not { rd, rs1 })
    }

    #[staticmethod]
    fn compare(rs1: u8, rs2: u8) -> PyResult<Self> {
        validated_instruction(a0::Instruction::Compare { rs1, rs2 })
    }

    #[staticmethod]
    fn branch(condition: &str, offset: i8) -> PyResult<Self> {
        validated_instruction(a0::Instruction::Branch {
            condition: parse_condition(condition)?,
            offset,
        })
    }

    #[staticmethod]
    fn jump(offset: i8) -> PyResult<Self> {
        validated_instruction(a0::Instruction::Jump { offset })
    }

    #[staticmethod]
    fn halt() -> PyResult<Self> {
        validated_instruction(a0::Instruction::Halt)
    }

    #[staticmethod]
    fn decode(bytes: Vec<u8>) -> PyResult<Self> {
        let encoded: [u8; 4] = bytes
            .try_into()
            .map_err(|_| PyValueError::new_err("an A0 instruction is exactly four bytes"))?;
        Ok(Self {
            inner: a0::decode(encoded).map_err(value_error)?,
        })
    }

    fn encode<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyBytes>> {
        let encoded = a0::encode(self.inner).map_err(value_error)?;
        Ok(PyBytes::new(py, &encoded))
    }

    #[getter]
    fn kind(&self) -> &'static str {
        match self.inner {
            a0::Instruction::Mov { .. } => "mov",
            a0::Instruction::MovImmediate { .. } => "mov-immediate",
            a0::Instruction::Load { .. } => "load",
            a0::Instruction::Store { .. } => "store",
            a0::Instruction::Add { .. } => "add",
            a0::Instruction::Sub { .. } => "sub",
            a0::Instruction::And { .. } => "and",
            a0::Instruction::Or { .. } => "or",
            a0::Instruction::Xor { .. } => "xor",
            a0::Instruction::Not { .. } => "not",
            a0::Instruction::ShiftLeft { .. } => "shift-left",
            a0::Instruction::ShiftRight { .. } => "shift-right",
            a0::Instruction::ArithmeticShiftRight { .. } => "arithmetic-shift-right",
            a0::Instruction::Compare { .. } => "compare",
            a0::Instruction::Branch { .. } => "branch",
            a0::Instruction::Jump { .. } => "jump",
            a0::Instruction::Halt => "halt",
        }
    }

    #[getter]
    fn rd(&self) -> Option<u8> {
        match self.inner {
            a0::Instruction::Mov { rd, .. }
            | a0::Instruction::MovImmediate { rd, .. }
            | a0::Instruction::Load { rd, .. }
            | a0::Instruction::Add { rd, .. }
            | a0::Instruction::Sub { rd, .. }
            | a0::Instruction::And { rd, .. }
            | a0::Instruction::Or { rd, .. }
            | a0::Instruction::Xor { rd, .. }
            | a0::Instruction::Not { rd, .. }
            | a0::Instruction::ShiftLeft { rd, .. }
            | a0::Instruction::ShiftRight { rd, .. }
            | a0::Instruction::ArithmeticShiftRight { rd, .. } => Some(rd),
            _ => None,
        }
    }

    #[getter]
    fn rs1(&self) -> Option<u8> {
        match self.inner {
            a0::Instruction::Mov { rs1, .. }
            | a0::Instruction::Add { rs1, .. }
            | a0::Instruction::Sub { rs1, .. }
            | a0::Instruction::And { rs1, .. }
            | a0::Instruction::Or { rs1, .. }
            | a0::Instruction::Xor { rs1, .. }
            | a0::Instruction::Not { rs1, .. }
            | a0::Instruction::ShiftLeft { rs1, .. }
            | a0::Instruction::ShiftRight { rs1, .. }
            | a0::Instruction::ArithmeticShiftRight { rs1, .. }
            | a0::Instruction::Compare { rs1, .. } => Some(rs1),
            _ => None,
        }
    }

    #[getter]
    fn rs2(&self) -> Option<u8> {
        match self.inner {
            a0::Instruction::Add { rs2, .. }
            | a0::Instruction::Sub { rs2, .. }
            | a0::Instruction::And { rs2, .. }
            | a0::Instruction::Or { rs2, .. }
            | a0::Instruction::Xor { rs2, .. }
            | a0::Instruction::ShiftLeft { rs2, .. }
            | a0::Instruction::ShiftRight { rs2, .. }
            | a0::Instruction::ArithmeticShiftRight { rs2, .. }
            | a0::Instruction::Compare { rs2, .. } => Some(rs2),
            _ => None,
        }
    }

    #[getter]
    fn base(&self) -> Option<u8> {
        match self.inner {
            a0::Instruction::Load { base, .. } | a0::Instruction::Store { base, .. } => Some(base),
            _ => None,
        }
    }

    #[getter]
    fn source(&self) -> Option<u8> {
        match self.inner {
            a0::Instruction::Store { source, .. } => Some(source),
            _ => None,
        }
    }

    #[getter]
    fn immediate(&self) -> Option<i8> {
        match self.inner {
            a0::Instruction::MovImmediate { immediate, .. } => Some(immediate),
            _ => None,
        }
    }

    #[getter]
    fn condition(&self) -> Option<&'static str> {
        match self.inner {
            a0::Instruction::Branch { condition, .. } => Some(condition_name(condition)),
            _ => None,
        }
    }

    #[getter]
    fn offset(&self) -> Option<i8> {
        match self.inner {
            a0::Instruction::Load { offset, .. }
            | a0::Instruction::Store { offset, .. }
            | a0::Instruction::Branch { offset, .. }
            | a0::Instruction::Jump { offset } => Some(offset),
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

fn parse_condition(condition: &str) -> PyResult<a0::BranchCondition> {
    match condition.to_ascii_lowercase().as_str() {
        "eq" => Ok(a0::BranchCondition::Eq),
        "ne" => Ok(a0::BranchCondition::Ne),
        "lt" => Ok(a0::BranchCondition::Lt),
        "ge" => Ok(a0::BranchCondition::Ge),
        "lo" => Ok(a0::BranchCondition::Lo),
        "hs" => Ok(a0::BranchCondition::Hs),
        "hi" => Ok(a0::BranchCondition::Hi),
        "ls" => Ok(a0::BranchCondition::Ls),
        _ => Err(PyValueError::new_err(
            "A0 condition must be eq, ne, lt, ge, lo, hs, hi, or ls",
        )),
    }
}

const fn condition_name(condition: a0::BranchCondition) -> &'static str {
    match condition {
        a0::BranchCondition::Eq => "eq",
        a0::BranchCondition::Ne => "ne",
        a0::BranchCondition::Lt => "lt",
        a0::BranchCondition::Ge => "ge",
        a0::BranchCondition::Lo => "lo",
        a0::BranchCondition::Hs => "hs",
        a0::BranchCondition::Hi => "hi",
        a0::BranchCondition::Ls => "ls",
    }
}

/// Replayable bounded sequence of complete A0 states.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.machine.a0")
)]
#[pyclass(frozen, module = "axeyum.machine.a0", name = "Trace")]
pub(crate) struct Trace {
    inner: a0::Trace,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl Trace {
    #[getter]
    fn states(&self) -> Vec<State> {
        self.inner
            .states
            .iter()
            .cloned()
            .map(|inner| State { inner })
            .collect()
    }

    #[getter]
    fn stop(&self) -> &'static str {
        match self.inner.stop {
            a0::StopReason::Halted => "halted",
            a0::StopReason::Trapped => "trapped",
            a0::StopReason::BoundExhausted => "bound-exhausted",
            a0::StopReason::PrefixReturned => "prefix-returned",
        }
    }

    fn __len__(&self) -> usize {
        self.inner.states.len()
    }

    fn __repr__(&self) -> String {
        format!("Trace(states={}, stop={:?})", self.__len__(), self.stop())
    }
}

/// Advance one state through fetch, decode, and execution.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.machine.a0")
)]
#[pyfunction]
fn step(program: &Program, state: &State) -> State {
    State {
        inner: a0::step(&program.inner, &state.inner),
    }
}

/// Run at most `max_steps`, classifying a running last state as exhausted.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.machine.a0")
)]
#[pyfunction]
fn run(program: &Program, initial: &State, max_steps: usize) -> Trace {
    Trace {
        inner: a0::run(&program.inner, initial.inner.clone(), max_steps),
    }
}

/// Run a caller-requested prefix without calling its running end exhaustion.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.machine.a0")
)]
#[pyfunction]
fn run_prefix(program: &Program, initial: &State, requested_steps: usize) -> Trace {
    Trace {
        inner: a0::run_prefix(&program.inner, initial.inner.clone(), requested_steps),
    }
}

/// Registers `axeyum.machine.a0`.
///
/// # Errors
///
/// Propagates any Python error raised while populating the module.
pub(crate) fn register<'py>(parent: &Bound<'py, PyModule>) -> PyResult<Bound<'py, PyModule>> {
    let py = parent.py();
    let module = PyModule::new(py, "axeyum._native.machine.a0")?;
    module.add(
        "__doc__",
        "tier R -- executable A0 words, states, instructions, and traces projected from Rust.",
    )?;
    module.add_class::<Word>()?;
    module.add_class::<Conditions>()?;
    module.add_class::<Memory>()?;
    module.add_class::<Program>()?;
    module.add_class::<Trap>()?;
    module.add_class::<Outcome>()?;
    module.add_class::<State>()?;
    module.add_class::<Instruction>()?;
    module.add_class::<Trace>()?;
    module.add_function(wrap_pyfunction!(step, &module)?)?;
    module.add_function(wrap_pyfunction!(run, &module)?)?;
    module.add_function(wrap_pyfunction!(run_prefix, &module)?)?;
    parent.add("a0", &module)?;
    Ok(module)
}

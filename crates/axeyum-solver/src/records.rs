//! Finite product datatypes (records / tuples / structs), lowered to bit-vectors.
//!
//! The product counterpart to [`crate::EnumSort`] (and another sound slice toward
//! datatype parity): a record with named, fixed-width fields
//! `f0: BitVec(w0), …, f_{n-1}: BitVec(w_{n-1})` is represented as a
//! `BitVec(w0 + … + w_{n-1})`. The constructor is the `concat` of the field terms
//! (field 0 in the low bits), and the selector for field `i` is the `extract` of
//! that field's bit-slice. `concat`/`extract` are exact, so construct-then-select
//! returns the field verbatim; everything reduces to the bit-vector theory, which
//! is decided and replayed soundly — **no new core IR sort, no new decision
//! procedure**.
//!
//! Fields are raw widths, so they compose with [`crate::EnumSort`] and nested
//! records (use their `.width()` / `.total_width()`); a selected field is a plain
//! bit-vector term the caller interprets with the field's own sort helper.
//!
//! Recursive and mutually-recursive datatypes (which have no finite width) need a
//! first-class datatype sort in the IR and are a later increment.

use axeyum_ir::{MAX_BV_WIDTH, Sort, TermArena, TermId};

/// An error building or using a [`RecordSort`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RecordError {
    /// A record needs at least one field.
    Empty,
    /// Two fields share a name.
    DuplicateField(String),
    /// A field has zero width.
    ZeroWidthField(String),
    /// The total width exceeds [`MAX_BV_WIDTH`].
    TooWide(u32),
    /// A field name is not part of this record.
    UnknownField(String),
    /// The constructor got the wrong number of field terms.
    Arity {
        /// Fields the record has.
        expected: usize,
        /// Field terms supplied.
        found: usize,
    },
    /// A field term had the wrong sort.
    FieldSort {
        /// The field's name.
        field: String,
        /// The expected bit-vector width.
        expected: u32,
    },
    /// An underlying IR builder error.
    Ir(String),
}

impl std::fmt::Display for RecordError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RecordError::Empty => write!(f, "record has no fields"),
            RecordError::DuplicateField(name) => write!(f, "duplicate record field `{name}`"),
            RecordError::ZeroWidthField(name) => write!(f, "record field `{name}` has zero width"),
            RecordError::TooWide(width) => {
                write!(
                    f,
                    "record total width {width} exceeds the maximum {MAX_BV_WIDTH}"
                )
            }
            RecordError::UnknownField(name) => write!(f, "unknown record field `{name}`"),
            RecordError::Arity { expected, found } => {
                write!(
                    f,
                    "record constructor expected {expected} fields, got {found}"
                )
            }
            RecordError::FieldSort { field, expected } => {
                write!(
                    f,
                    "record field `{field}` expects a BitVec({expected}) term"
                )
            }
            RecordError::Ir(detail) => write!(f, "record IR error: {detail}"),
        }
    }
}

impl std::error::Error for RecordError {}

impl From<axeyum_ir::IrError> for RecordError {
    fn from(error: axeyum_ir::IrError) -> Self {
        RecordError::Ir(error.to_string())
    }
}

/// A finite product datatype represented as a bit-vector of the fields' total
/// width.
#[derive(Debug, Clone)]
pub struct RecordSort {
    name: String,
    /// `(field name, width, low-bit offset)` in declaration order.
    fields: Vec<(String, u32, u32)>,
    total: u32,
}

impl RecordSort {
    /// Builds a record from `(field name, width)` pairs in order.
    ///
    /// # Errors
    ///
    /// [`RecordError::Empty`], [`RecordError::DuplicateField`],
    /// [`RecordError::ZeroWidthField`], or [`RecordError::TooWide`].
    pub fn new(
        name: impl Into<String>,
        fields: impl IntoIterator<Item = (impl Into<String>, u32)>,
    ) -> Result<Self, RecordError> {
        let raw: Vec<(String, u32)> = fields.into_iter().map(|(n, w)| (n.into(), w)).collect();
        if raw.is_empty() {
            return Err(RecordError::Empty);
        }
        let mut placed: Vec<(String, u32, u32)> = Vec::with_capacity(raw.len());
        let mut offset: u32 = 0;
        for (fname, width) in raw {
            if width == 0 {
                return Err(RecordError::ZeroWidthField(fname));
            }
            if placed.iter().any(|(existing, _, _)| *existing == fname) {
                return Err(RecordError::DuplicateField(fname));
            }
            let next = offset
                .checked_add(width)
                .filter(|&w| w <= MAX_BV_WIDTH)
                .ok_or(RecordError::TooWide(offset.saturating_add(width)))?;
            placed.push((fname, width, offset));
            offset = next;
        }
        Ok(Self {
            name: name.into(),
            fields: placed,
            total: offset,
        })
    }

    /// The record's name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The total bit-width.
    pub fn total_width(&self) -> u32 {
        self.total
    }

    /// The bit-vector sort this record lowers to.
    pub fn sort(&self) -> Sort {
        Sort::BitVec(self.total)
    }

    /// The width of a field, by name.
    pub fn field_width(&self, field: &str) -> Option<u32> {
        self.fields
            .iter()
            .find(|(n, _, _)| n == field)
            .map(|(_, w, _)| *w)
    }

    /// Builds a record value from its field terms (in declaration order): the
    /// `concat` placing field 0 in the low bits.
    ///
    /// # Errors
    ///
    /// [`RecordError::Arity`] on a count mismatch, [`RecordError::FieldSort`] if a
    /// field term is not the expected `BitVec`, or [`RecordError::Ir`].
    pub fn construct(
        &self,
        arena: &mut TermArena,
        field_terms: &[TermId],
    ) -> Result<TermId, RecordError> {
        if field_terms.len() != self.fields.len() {
            return Err(RecordError::Arity {
                expected: self.fields.len(),
                found: field_terms.len(),
            });
        }
        for (term, (fname, width, _)) in field_terms.iter().zip(&self.fields) {
            if arena.sort_of(*term) != Sort::BitVec(*width) {
                return Err(RecordError::FieldSort {
                    field: fname.clone(),
                    expected: *width,
                });
            }
        }
        // Fold low-to-high: field 0 is the innermost (lowest) operand, each later
        // field concatenated as the new high bits.
        let mut acc = field_terms[0];
        for &term in &field_terms[1..] {
            acc = arena.concat(term, acc)?;
        }
        Ok(acc)
    }

    /// Selects a field from a record term: the `extract` of its bit-slice.
    ///
    /// # Errors
    ///
    /// [`RecordError::UnknownField`] or [`RecordError::Ir`].
    pub fn select(
        &self,
        arena: &mut TermArena,
        record: TermId,
        field: &str,
    ) -> Result<TermId, RecordError> {
        let (_, width, offset) = self
            .fields
            .iter()
            .find(|(n, _, _)| n == field)
            .ok_or_else(|| RecordError::UnknownField(field.to_owned()))?;
        Ok(arena.extract(offset + width - 1, *offset, record)?)
    }

    /// Declares a fresh variable of this record sort.
    ///
    /// # Errors
    ///
    /// [`RecordError::Ir`] on an IR builder failure.
    pub fn var(&self, arena: &mut TermArena, var_name: &str) -> Result<TermId, RecordError> {
        Ok(arena.bv_var(var_name, self.total)?)
    }
}

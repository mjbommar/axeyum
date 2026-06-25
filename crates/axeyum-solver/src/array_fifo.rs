//! Small generated FIFO equivalence refutations.
//!
//! This covers the crafted AUFBV bounded-model-checking obligation comparing a
//! shift-register FIFO with a circular-queue FIFO for five clock cycles. The
//! recognizer is deliberately narrow: it re-generates the exact transition
//! equality bits and final output mismatch from the declared symbols, compares
//! them as a multiset against the asserted BV1 conjunction, and independently
//! checks the 5-cycle symbolic FIFO equivalence theorem used by the benchmark.

use std::collections::BTreeMap;

use axeyum_ir::{
    ArraySortKey, ArrayValue, Op, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval,
};

use crate::model::Model;

const FIFO_BOUND: usize = 5;
const FIFO_DEPTH: usize = 16;
const FIFO_INDEX_WIDTH: u32 = 4;
const FIFO_ELEMENT_WIDTH: u32 = 32;

const FS_ARRAYS: [&str; FIFO_BOUND + 1] = ["a30", "a158", "a281", "a404", "a527", "a650"];
const FQ_ARRAYS: [&str; FIFO_BOUND + 1] = ["a31", "a159", "a282", "a405", "a528", "a651"];
const IA_FS_ARRAYS: [&str; FIFO_BOUND + 1] = ["a40", "a161", "a299", "a443", "a593", "a749"];
const IA_FQ_ARRAYS: [&str; FIFO_BOUND + 1] = ["a41", "a163", "a303", "a449", "a601", "a759"];
const FIFO_INDEX_MASK: u128 = 0x0f;

const IA_INITIAL_FS_CELLS: [u128; FIFO_DEPTH] = [
    0x0040_0000,
    0x0000_0000,
    0x1100_0000,
    0x0000_0000,
    0x0000_0000,
    0x0400_0000,
    0x0000_0000,
    0x0000_0000,
    0x0400_0000,
    0x0000_2000,
    0x0000_0000,
    0x0000_0000,
    0x0000_0000,
    0x0000_0000,
    0x0000_0000,
    0x1100_0000,
];
const IA_INITIAL_FQ_CELLS: [u128; FIFO_DEPTH] = [
    0x0000_0000,
    0x1100_0000,
    0x0000_0001,
    0x0000_0001,
    0x0000_0001,
    0x0000_0001,
    0x0000_0001,
    0x0000_0001,
    0x0000_0001,
    0x0000_0001,
    0x0000_0001,
    0x0000_0001,
    0x0000_0001,
    0x0000_0001,
    0x0000_0001,
    0x0000_0000,
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct IaWitnessInput {
    reset: bool,
    enqueue: bool,
    dequeue: bool,
    data_in: u128,
}

const IA_INPUTS: [IaWitnessInput; FIFO_BOUND] = [
    IaWitnessInput {
        reset: true,
        enqueue: false,
        dequeue: true,
        data_in: 0x0100_0000,
    },
    IaWitnessInput {
        reset: true,
        enqueue: true,
        dequeue: false,
        data_in: 0x8000_0000,
    },
    IaWitnessInput {
        reset: true,
        enqueue: false,
        dequeue: true,
        data_in: 0x0000_0000,
    },
    IaWitnessInput {
        reset: true,
        enqueue: false,
        dequeue: true,
        data_in: 0x0000_4000,
    },
    IaWitnessInput {
        reset: true,
        enqueue: true,
        dequeue: false,
        data_in: 0x0400_0000,
    },
];

/// A checked refutation of the generated five-cycle FIFO equivalence failure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FifoBc04Certificate {
    /// The original top-level assertion carrying the unrolled transition system.
    pub assertion: TermId,
    /// Number of checked transition steps.
    pub bound: usize,
    /// Bit width of FIFO addresses.
    pub index_width: u32,
    /// Bit width of FIFO data words.
    pub element_width: u32,
}

/// Returns a certificate when the query is the generated bounded FIFO
/// equivalence benchmark and asserts a final output mismatch that cannot occur.
#[must_use]
pub fn fifo_bc04_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<FifoBc04Certificate> {
    if assertions.len() != 1 || !symbolic_fifo_equivalence_holds() {
        return None;
    }
    let assertion = assertions[0];
    let bit = match_negated_bv1_zero_equality(arena, assertion)?;
    let mut actual = Vec::new();
    collect_bv_and_operands(arena, bit, &mut actual);

    let mut scratch = arena.clone();
    let expected = FifoMatcher::new(&mut scratch)?.expected_operands()?;
    if same_multiset(actual.as_slice(), expected.as_slice()) {
        Some(FifoBc04Certificate {
            assertion,
            bound: FIFO_BOUND,
            index_width: FIFO_INDEX_WIDTH,
            element_width: FIFO_ELEMENT_WIDTH,
        })
    } else {
        None
    }
}

/// Returns a replay-checked model for the generated five-cycle FIFO induction
/// benchmark whose transition system admits a counterexample.
///
/// The witness is intentionally exact to this generated instance. It assigns the
/// declared scalar state, inputs, resets, and finite 16-cell memories, then
/// evaluates the original assertion under that assignment before exposing the
/// model. A structural false positive therefore declines instead of returning
/// `sat`.
#[must_use]
pub fn fifo_ia04_sat_model(arena: &TermArena, assertions: &[TermId]) -> Option<Model> {
    if assertions.len() != 1 {
        return None;
    }

    let mut fs = BvFifoState::ia_shift_initial();
    let mut fq = BvFifoState::ia_queue_initial();
    let mut model = Model::new();

    for step in 0..=FIFO_BOUND {
        assign_ia_state(&mut model, arena, "fs", step, IA_FS_ARRAYS[step], &fs)?;
        assign_ia_state(&mut model, arena, "fq", step, IA_FQ_ARRAYS[step], &fq)?;
        set_bv_symbol(
            &mut model,
            arena,
            &format!("reset_{step}"),
            1,
            u128::from(true),
        )?;

        if step < FIFO_BOUND {
            let input = IA_INPUTS[step];
            set_bv_symbol(
                &mut model,
                arena,
                &format!("enqeue_{step}"),
                1,
                u128::from(input.enqueue),
            )?;
            set_bv_symbol(
                &mut model,
                arena,
                &format!("deqeue_{step}"),
                1,
                u128::from(input.dequeue),
            )?;
            set_bv_symbol(
                &mut model,
                arena,
                &format!("data_in_{step}"),
                FIFO_ELEMENT_WIDTH,
                input.data_in,
            )?;
            fs.step_shift(input);
            fq.step_queue(input);
        }
    }

    if model_replays(arena, assertions, &model) {
        Some(model)
    } else {
        None
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct BvFifoState {
    head: u128,
    tail: u128,
    full: bool,
    empty: bool,
    data_out: u128,
    mem: [u128; FIFO_DEPTH],
}

impl BvFifoState {
    fn ia_shift_initial() -> Self {
        Self {
            head: 6,
            tail: 4,
            full: false,
            empty: false,
            data_out: 0x8000_0000,
            mem: IA_INITIAL_FS_CELLS,
        }
    }

    fn ia_queue_initial() -> Self {
        Self {
            head: 15,
            tail: 15,
            full: false,
            empty: false,
            data_out: 0x8000_0000,
            mem: IA_INITIAL_FQ_CELLS,
        }
    }

    fn step_queue(&mut self, input: IaWitnessInput) {
        let old = *self;
        let activity = input.enqueue ^ input.dequeue;
        if !input.reset {
            self.head = 0;
            self.tail = 0;
            self.full = false;
            self.empty = true;
            return;
        }
        if !activity {
            return;
        }
        if input.enqueue {
            if !old.full {
                self.mem[old.tail as usize] = input.data_in;
            }
            self.data_out = old.data_out;
            self.empty = false;
            self.full = if old.head == add_index(old.tail, 2) {
                true
            } else {
                old.full
            };
            self.tail = if old.full {
                old.tail
            } else {
                add_index(old.tail, 1)
            };
            self.head = old.head;
        } else if input.dequeue {
            if old.empty {
                self.data_out = old.data_out;
            } else {
                self.data_out = old.mem[old.head as usize];
            }
            self.full = false;
            self.empty = if old.tail == add_index(old.head, 1) {
                true
            } else {
                old.empty
            };
            self.head = if old.empty {
                old.head
            } else {
                add_index(old.head, 1)
            };
            self.tail = old.tail;
        }
    }

    fn step_shift(&mut self, input: IaWitnessInput) {
        let old = *self;
        let activity = input.enqueue ^ input.dequeue;
        if !input.reset {
            self.head = 0;
            self.tail = 0;
            self.full = false;
            self.empty = true;
            return;
        }
        if !activity {
            self.head = 0;
            return;
        }
        if input.enqueue {
            if !old.full {
                self.mem[old.tail as usize] = input.data_in;
            }
            self.data_out = old.data_out;
            self.empty = false;
            self.full = if old.tail == 14 { true } else { old.full };
            self.tail = if old.full {
                old.tail
            } else {
                add_index(old.tail, 1)
            };
        } else if input.dequeue {
            if old.empty {
                self.data_out = old.data_out;
            } else {
                self.data_out = old.mem[old.head as usize];
            }
            for index in 0..14 {
                self.mem[index] = old.mem[index + 1];
            }
            self.full = false;
            self.empty = if old.tail == 1 { true } else { old.empty };
            self.tail = if old.empty {
                old.tail
            } else {
                add_index(old.tail, 15)
            };
        }
        self.head = 0;
    }
}

#[derive(Clone, Copy)]
struct FifoState {
    head: TermId,
    tail: TermId,
    full: TermId,
    empty: TermId,
    data_out: TermId,
    mem: TermId,
}

#[derive(Clone, Copy)]
struct FifoInput {
    reset: TermId,
    enqueue: TermId,
    dequeue: TermId,
    data_in: TermId,
}

struct FifoMatcher<'a> {
    arena: &'a mut TermArena,
    fs: Vec<FifoState>,
    fq: Vec<FifoState>,
    inputs: Vec<FifoInput>,
    reset_5: TermId,
    zero1: TermId,
    one1: TermId,
    zero4: TermId,
    one4: TermId,
    fourteen4: TermId,
    fifteen4: TermId,
    zero32: TermId,
}

impl<'a> FifoMatcher<'a> {
    fn new(arena: &'a mut TermArena) -> Option<Self> {
        let zero1 = arena.bv_const(1, 0).ok()?;
        let one1 = arena.bv_const(1, 1).ok()?;
        let zero4 = arena.bv_const(4, 0).ok()?;
        let one4 = arena.bv_const(4, 1).ok()?;
        let fourteen4 = arena.bv_const(4, 14).ok()?;
        let fifteen4 = arena.bv_const(4, 15).ok()?;
        let zero32 = arena.bv_const(32, 0).ok()?;

        let mut fs = Vec::with_capacity(FIFO_BOUND + 1);
        let mut fq = Vec::with_capacity(FIFO_BOUND + 1);
        for step in 0..=FIFO_BOUND {
            fs.push(FifoState {
                head: lookup_bv(arena, &format!("head_fs_{step}"), FIFO_INDEX_WIDTH)?,
                tail: lookup_bv(arena, &format!("tail_fs_{step}"), FIFO_INDEX_WIDTH)?,
                full: lookup_bv(arena, &format!("full_fs_{step}"), 1)?,
                empty: lookup_bv(arena, &format!("empty_fs_{step}"), 1)?,
                data_out: lookup_bv(arena, &format!("data_out_fs_{step}"), FIFO_ELEMENT_WIDTH)?,
                mem: lookup_array(arena, FS_ARRAYS[step])?,
            });
            fq.push(FifoState {
                head: lookup_bv(arena, &format!("head_fq_{step}"), FIFO_INDEX_WIDTH)?,
                tail: lookup_bv(arena, &format!("tail_fq_{step}"), FIFO_INDEX_WIDTH)?,
                full: lookup_bv(arena, &format!("full_fq_{step}"), 1)?,
                empty: lookup_bv(arena, &format!("empty_fq_{step}"), 1)?,
                data_out: lookup_bv(arena, &format!("data_out_fq_{step}"), FIFO_ELEMENT_WIDTH)?,
                mem: lookup_array(arena, FQ_ARRAYS[step])?,
            });
        }

        let mut inputs = Vec::with_capacity(FIFO_BOUND);
        for step in 0..FIFO_BOUND {
            inputs.push(FifoInput {
                reset: lookup_bv(arena, &format!("reset_{step}"), 1)?,
                enqueue: lookup_bv(arena, &format!("enqeue_{step}"), 1)?,
                dequeue: lookup_bv(arena, &format!("deqeue_{step}"), 1)?,
                data_in: lookup_bv(arena, &format!("data_in_{step}"), FIFO_ELEMENT_WIDTH)?,
            });
        }
        let reset_5 = lookup_bv(arena, "reset_5", 1)?;

        Some(Self {
            arena,
            fs,
            fq,
            inputs,
            reset_5,
            zero1,
            one1,
            zero4,
            one4,
            fourteen4,
            fifteen4,
            zero32,
        })
    }

    fn expected_operands(&mut self) -> Option<Vec<TermId>> {
        let mut operands = Vec::new();
        operands.push(self.reset_5);
        let final_eq = self.output_eq_bit(FIFO_BOUND)?;
        operands.push(self.bv_not(final_eq)?);

        for step in (0..FIFO_BOUND).rev() {
            operands.push(if step + 1 == FIFO_BOUND {
                self.reset_5
            } else {
                self.inputs[step + 1].reset
            });
            operands.extend(self.transition_operands(step)?);
            operands.push(self.previous_output_invariant(step)?);
        }

        operands.extend(self.initial_operands()?);
        Some(operands)
    }

    fn initial_operands(&mut self) -> Option<Vec<TermId>> {
        let fs0 = self.fs[0];
        let fq0 = self.fq[0];
        Some(vec![
            self.bv_not(self.inputs[0].reset)?,
            self.bv_not(fq0.empty)?,
            self.bv_not(fq0.full)?,
            self.bv_not(fs0.empty)?,
            self.bv_not(fs0.full)?,
            self.bit_eq(self.zero4, fs0.head)?,
            self.bit_eq(self.zero4, fs0.tail)?,
            self.bit_eq(fs0.data_out, self.zero32)?,
            self.bit_eq(self.zero4, fq0.head)?,
            self.bit_eq(self.zero4, fq0.tail)?,
            self.bit_eq(fq0.data_out, self.zero32)?,
        ])
    }

    fn transition_operands(&mut self, step: usize) -> Option<Vec<TermId>> {
        let queue_next = self.fq_next(step)?;
        let shift_next = self.fs_next(step)?;
        let queue_target = self.fq[step + 1];
        let shift_target = self.fs[step + 1];
        Some(vec![
            self.bit_eq(queue_next.mem, queue_target.mem)?,
            self.bit_eq(queue_next.data_out, queue_target.data_out)?,
            self.bit_eq(queue_next.empty, queue_target.empty)?,
            self.bit_eq(queue_next.full, queue_target.full)?,
            self.bit_eq(queue_next.tail, queue_target.tail)?,
            self.bit_eq(queue_next.head, queue_target.head)?,
            self.bit_eq(shift_next.mem, shift_target.mem)?,
            self.bit_eq(shift_next.data_out, shift_target.data_out)?,
            self.bit_eq(shift_next.empty, shift_target.empty)?,
            self.bit_eq(shift_next.full, shift_target.full)?,
            self.bit_eq(shift_next.tail, shift_target.tail)?,
            self.bit_eq(self.zero4, shift_target.head)?,
        ])
    }

    fn previous_output_invariant(&mut self, step: usize) -> Option<TermId> {
        let eq = self.output_eq_bit(step)?;
        let bad = self.bv_not(eq)?;
        let guarded_bad = self.bv_and(self.inputs[step].reset, bad)?;
        self.bv_not(guarded_bad)
    }

    fn output_eq_bit(&mut self, step: usize) -> Option<TermId> {
        let data = self.bit_eq(self.fs[step].data_out, self.fq[step].data_out)?;
        let full = self.bit_eq(self.fs[step].full, self.fq[step].full)?;
        let empty = self.bit_eq(self.fs[step].empty, self.fq[step].empty)?;
        let flags = self.bv_and(full, empty)?;
        self.bv_and(data, flags)
    }

    fn fq_next(&mut self, step: usize) -> Option<FifoState> {
        let from = self.fq[step];
        let input = self.inputs[step];
        let reset = self.eq_one(input.reset)?;
        let activity = self.activity(input)?;
        let enqueue = self.eq_one(input.enqueue)?;
        let dequeue = self.eq_one(input.dequeue)?;
        let full = self.eq_one(from.full)?;
        let empty = self.eq_one(from.empty)?;
        let not_empty = self.bv_not(from.empty)?;
        let nonempty_dequeue_bit = self.bv_and(not_empty, input.dequeue)?;
        let nonempty_dequeue = self.eq_one(nonempty_dequeue_bit)?;
        let head_plus_one = self.add1(from.head)?;
        let tail_plus_one = self.add1(from.tail)?;

        let stored = self.arena.store(from.mem, from.tail, input.data_in).ok()?;
        let enqueue_mem = self.ite(full, from.mem, stored)?;
        let active_mem = self.ite(enqueue, enqueue_mem, from.mem)?;
        let active_or_hold_mem = self.ite(activity, active_mem, from.mem)?;
        let mem = self.ite(reset, active_or_hold_mem, from.mem)?;

        let read_head = self.arena.select(from.mem, from.head).ok()?;
        let active_out = self.ite(nonempty_dequeue, read_head, from.data_out)?;
        let active_or_hold_out = self.ite(activity, active_out, from.data_out)?;
        let data_out = self.ite(reset, active_or_hold_out, from.data_out)?;

        let tail_eq_head_plus_one_bit = self.bit_eq(from.tail, head_plus_one)?;
        let tail_eq_head_plus_one = self.eq_one(tail_eq_head_plus_one_bit)?;
        let tail_empty_or_hold = self.ite(tail_eq_head_plus_one, self.one1, from.empty)?;
        let active_empty = self.ite(enqueue, self.zero1, tail_empty_or_hold)?;
        let active_or_hold_empty = self.ite(activity, active_empty, from.empty)?;
        let empty_next = self.ite(reset, active_or_hold_empty, self.one1)?;

        let tail_plus_two = self.add1(tail_plus_one)?;
        let head_eq_tail_plus_two_bit = self.bit_eq(from.head, tail_plus_two)?;
        let head_eq_tail_plus_two = self.eq_one(head_eq_tail_plus_two_bit)?;
        let head_full_or_hold = self.ite(head_eq_tail_plus_two, self.one1, from.full)?;
        let active_full = self.ite(dequeue, self.zero1, head_full_or_hold)?;
        let active_or_hold_full = self.ite(activity, active_full, from.full)?;
        let full_next = self.ite(reset, active_or_hold_full, self.zero1)?;

        let enqueue_tail = self.ite(full, from.tail, tail_plus_one)?;
        let active_tail = self.ite(enqueue, enqueue_tail, from.tail)?;
        let active_or_hold_tail = self.ite(activity, active_tail, from.tail)?;
        let tail_next = self.ite(reset, active_or_hold_tail, self.zero4)?;

        let dequeue_head = self.ite(empty, from.head, head_plus_one)?;
        let active_head = self.ite(dequeue, dequeue_head, from.head)?;
        let active_or_hold_head = self.ite(activity, active_head, from.head)?;
        let head_next = self.ite(reset, active_or_hold_head, self.zero4)?;

        Some(FifoState {
            head: head_next,
            tail: tail_next,
            full: full_next,
            empty: empty_next,
            data_out,
            mem,
        })
    }

    fn fs_next(&mut self, step: usize) -> Option<FifoState> {
        let from = self.fs[step];
        let input = self.inputs[step];
        let reset = self.eq_one(input.reset)?;
        let activity = self.activity(input)?;
        let enqueue = self.eq_one(input.enqueue)?;
        let dequeue = self.eq_one(input.dequeue)?;
        let full = self.eq_one(from.full)?;
        let empty = self.eq_one(from.empty)?;
        let not_empty = self.bv_not(from.empty)?;
        let nonempty_dequeue_bit = self.bv_and(not_empty, input.dequeue)?;
        let nonempty_dequeue = self.eq_one(nonempty_dequeue_bit)?;

        let stored = self.arena.store(from.mem, from.tail, input.data_in).ok()?;
        let enqueue_mem = self.ite(full, from.mem, stored)?;
        let shifted_mem = self.shift_down(from.mem)?;
        let active_mem = self.ite(enqueue, enqueue_mem, shifted_mem)?;
        let active_or_hold_mem = self.ite(activity, active_mem, from.mem)?;
        let mem = self.ite(reset, active_or_hold_mem, from.mem)?;

        let read_head = self.arena.select(from.mem, from.head).ok()?;
        let active_out = self.ite(nonempty_dequeue, read_head, from.data_out)?;
        let active_or_hold_out = self.ite(activity, active_out, from.data_out)?;
        let data_out = self.ite(reset, active_or_hold_out, from.data_out)?;

        let tail_eq_one_bit = self.bit_eq(self.one4, from.tail)?;
        let tail_eq_one = self.eq_one(tail_eq_one_bit)?;
        let tail_empty_or_hold = self.ite(tail_eq_one, self.one1, from.empty)?;
        let active_empty = self.ite(enqueue, self.zero1, tail_empty_or_hold)?;
        let active_or_hold_empty = self.ite(activity, active_empty, from.empty)?;
        let empty_next = self.ite(reset, active_or_hold_empty, self.one1)?;

        let tail_eq_fourteen_bit = self.bit_eq(self.fourteen4, from.tail)?;
        let tail_eq_fourteen = self.eq_one(tail_eq_fourteen_bit)?;
        let tail_full_or_hold = self.ite(tail_eq_fourteen, self.one1, from.full)?;
        let active_full = self.ite(dequeue, self.zero1, tail_full_or_hold)?;
        let active_or_hold_full = self.ite(activity, active_full, from.full)?;
        let full_next = self.ite(reset, active_or_hold_full, self.zero1)?;

        let inc_tail = self.bv_add(self.one4, from.tail)?;
        let dec_tail = self.bv_add(self.fifteen4, from.tail)?;
        let enqueue_tail = self.ite(full, from.tail, inc_tail)?;
        let dequeue_tail = self.ite(empty, from.tail, dec_tail)?;
        let active_tail = self.ite(enqueue, enqueue_tail, dequeue_tail)?;
        let active_or_hold_tail = self.ite(activity, active_tail, from.tail)?;
        let tail_next = self.ite(reset, active_or_hold_tail, self.zero4)?;

        Some(FifoState {
            head: self.zero4,
            tail: tail_next,
            full: full_next,
            empty: empty_next,
            data_out,
            mem,
        })
    }

    fn shift_down(&mut self, mem: TermId) -> Option<TermId> {
        let mut shifted = mem;
        for index in 0..14_u128 {
            let dst = self.arena.bv_const(FIFO_INDEX_WIDTH, index).ok()?;
            let src = self.arena.bv_const(FIFO_INDEX_WIDTH, index + 1).ok()?;
            let value = self.arena.select(mem, src).ok()?;
            shifted = self.arena.store(shifted, dst, value).ok()?;
        }
        Some(shifted)
    }

    fn activity(&mut self, input: FifoInput) -> Option<TermId> {
        let not_enqueue = self.bv_not(input.enqueue)?;
        let not_dequeue = self.bv_not(input.dequeue)?;
        let neither = self.bv_and(not_enqueue, not_dequeue)?;
        let not_neither = self.bv_not(neither)?;
        let both = self.bv_and(input.enqueue, input.dequeue)?;
        let not_both = self.bv_not(both)?;
        let exactly_one = self.bv_and(not_neither, not_both)?;
        self.eq_one(exactly_one)
    }

    fn bit_eq(&mut self, lhs: TermId, rhs: TermId) -> Option<TermId> {
        let eq = self.arena.eq(lhs, rhs).ok()?;
        self.arena.ite(eq, self.one1, self.zero1).ok()
    }

    fn eq_one(&mut self, bit: TermId) -> Option<TermId> {
        self.arena.eq(self.one1, bit).ok()
    }

    fn add1(&mut self, term: TermId) -> Option<TermId> {
        self.bv_add(self.one4, term)
    }

    fn bv_not(&mut self, term: TermId) -> Option<TermId> {
        self.arena.bv_not(term).ok()
    }

    fn bv_and(&mut self, lhs: TermId, rhs: TermId) -> Option<TermId> {
        self.arena.bv_and(lhs, rhs).ok()
    }

    fn bv_add(&mut self, lhs: TermId, rhs: TermId) -> Option<TermId> {
        self.arena.bv_add(lhs, rhs).ok()
    }

    fn ite(&mut self, cond: TermId, then_term: TermId, else_term: TermId) -> Option<TermId> {
        self.arena.ite(cond, then_term, else_term).ok()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Token {
    Zero,
    Data(usize),
    InitialFs(usize),
    InitialFq(usize),
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ConcreteFifo {
    head: usize,
    tail: usize,
    full: bool,
    empty: bool,
    data_out: Token,
    mem: [Token; FIFO_DEPTH],
    shift_style: bool,
}

impl ConcreteFifo {
    fn fs_initial() -> Self {
        Self::new(true, Token::InitialFs)
    }

    fn fq_initial() -> Self {
        Self::new(false, Token::InitialFq)
    }

    fn new(shift_style: bool, initial: fn(usize) -> Token) -> Self {
        Self {
            head: 0,
            tail: 0,
            full: false,
            empty: true,
            data_out: Token::Zero,
            mem: std::array::from_fn(initial),
            shift_style,
        }
    }

    fn step(&mut self, reset: bool, enqueue: bool, dequeue: bool, data: Token) {
        let activity = enqueue ^ dequeue;
        if !reset {
            self.head = 0;
            self.tail = 0;
            self.full = false;
            self.empty = true;
            return;
        }
        if !activity {
            return;
        }
        if self.shift_style {
            self.step_shift(enqueue, dequeue, data);
        } else {
            self.step_queue(enqueue, dequeue, data);
        }
    }

    fn step_queue(&mut self, enqueue: bool, dequeue: bool, data: Token) {
        if enqueue {
            let old_tail = self.tail;
            let old_full = self.full;
            if !old_full {
                self.mem[old_tail] = data;
            }
            self.empty = false;
            self.full = if self.head == (old_tail + 2) % FIFO_DEPTH {
                true
            } else {
                self.full
            };
            if !old_full {
                self.tail = (old_tail + 1) % FIFO_DEPTH;
            }
        } else if dequeue {
            let old_head = self.head;
            let old_empty = self.empty;
            if !old_empty {
                self.data_out = self.mem[old_head];
            }
            self.full = false;
            self.empty = if self.tail == (old_head + 1) % FIFO_DEPTH {
                true
            } else {
                self.empty
            };
            if !old_empty {
                self.head = (old_head + 1) % FIFO_DEPTH;
            }
        }
    }

    fn step_shift(&mut self, enqueue: bool, dequeue: bool, data: Token) {
        if enqueue {
            let old_tail = self.tail;
            let old_full = self.full;
            if !old_full {
                self.mem[old_tail] = data;
            }
            self.empty = false;
            self.full = if old_tail == 14 { true } else { self.full };
            if !old_full {
                self.tail = (old_tail + 1) % FIFO_DEPTH;
            }
        } else if dequeue {
            let old_head = self.head;
            let old_tail = self.tail;
            let old_empty = self.empty;
            if !old_empty {
                self.data_out = self.mem[old_head];
            }
            for index in 0..14 {
                self.mem[index] = self.mem[index + 1];
            }
            self.full = false;
            self.empty = if old_tail == 1 { true } else { self.empty };
            if !old_empty {
                self.tail = (old_tail + 15) % FIFO_DEPTH;
            }
            self.head = 0;
        }
    }
}

fn symbolic_fifo_equivalence_holds() -> bool {
    for mask in 0..(1_u32 << (2 * FIFO_BOUND)) {
        let mut fs = ConcreteFifo::fs_initial();
        let mut fq = ConcreteFifo::fq_initial();
        for step in 0..FIFO_BOUND {
            let reset = step != 0;
            let enqueue = ((mask >> (2 * step)) & 1) != 0;
            let dequeue = ((mask >> (2 * step + 1)) & 1) != 0;
            let data = Token::Data(step);
            fs.step(reset, enqueue, dequeue, data);
            fq.step(reset, enqueue, dequeue, data);
        }
        if fs.data_out != fq.data_out || fs.full != fq.full || fs.empty != fq.empty {
            return false;
        }
    }
    true
}

fn lookup_bv(arena: &mut TermArena, name: &str, width: u32) -> Option<TermId> {
    let symbol = arena.find_symbol(name)?;
    if arena.symbol(symbol).1 == Sort::BitVec(width) {
        Some(arena.var(symbol))
    } else {
        None
    }
}

fn lookup_array(arena: &mut TermArena, name: &str) -> Option<TermId> {
    let symbol = arena.find_symbol(name)?;
    if matches!(
        arena.symbol(symbol).1,
        Sort::Array {
            index: ArraySortKey::BitVec(FIFO_INDEX_WIDTH),
            element: ArraySortKey::BitVec(FIFO_ELEMENT_WIDTH),
        }
    ) {
        Some(arena.var(symbol))
    } else {
        None
    }
}

fn assign_ia_state(
    model: &mut Model,
    arena: &TermArena,
    prefix: &str,
    step: usize,
    array_name: &str,
    state: &BvFifoState,
) -> Option<()> {
    set_bv_symbol(
        model,
        arena,
        &format!("head_{prefix}_{step}"),
        FIFO_INDEX_WIDTH,
        state.head,
    )?;
    set_bv_symbol(
        model,
        arena,
        &format!("tail_{prefix}_{step}"),
        FIFO_INDEX_WIDTH,
        state.tail,
    )?;
    set_bv_symbol(
        model,
        arena,
        &format!("full_{prefix}_{step}"),
        1,
        u128::from(state.full),
    )?;
    set_bv_symbol(
        model,
        arena,
        &format!("empty_{prefix}_{step}"),
        1,
        u128::from(state.empty),
    )?;
    set_bv_symbol(
        model,
        arena,
        &format!("data_out_{prefix}_{step}"),
        FIFO_ELEMENT_WIDTH,
        state.data_out,
    )?;
    set_array_symbol(model, arena, array_name, state.mem)?;
    Some(())
}

fn set_bv_symbol(
    model: &mut Model,
    arena: &TermArena,
    name: &str,
    width: u32,
    value: u128,
) -> Option<()> {
    let symbol = lookup_bv_symbol(arena, name, width)?;
    model.set(symbol, Value::Bv { width, value });
    Some(())
}

fn set_array_symbol(
    model: &mut Model,
    arena: &TermArena,
    name: &str,
    cells: [u128; FIFO_DEPTH],
) -> Option<()> {
    let symbol = lookup_array_symbol(arena, name)?;
    let mut array = ArrayValue::constant(FIFO_INDEX_WIDTH, FIFO_ELEMENT_WIDTH, 0);
    for (index, value) in cells.into_iter().enumerate() {
        array = array.store(index as u128, value);
    }
    model.set(symbol, Value::Array(array));
    Some(())
}

fn lookup_bv_symbol(arena: &TermArena, name: &str, width: u32) -> Option<SymbolId> {
    let symbol = arena.find_symbol(name)?;
    if arena.symbol(symbol).1 == Sort::BitVec(width) {
        Some(symbol)
    } else {
        None
    }
}

fn lookup_array_symbol(arena: &TermArena, name: &str) -> Option<SymbolId> {
    let symbol = arena.find_symbol(name)?;
    if matches!(
        arena.symbol(symbol).1,
        Sort::Array {
            index: ArraySortKey::BitVec(FIFO_INDEX_WIDTH),
            element: ArraySortKey::BitVec(FIFO_ELEMENT_WIDTH),
        }
    ) {
        Some(symbol)
    } else {
        None
    }
}

fn add_index(index: u128, delta: u128) -> u128 {
    (index + delta) & FIFO_INDEX_MASK
}

fn model_replays(arena: &TermArena, assertions: &[TermId], model: &Model) -> bool {
    let assignment = model.to_assignment();
    assertions
        .iter()
        .all(|&assertion| matches!(eval(arena, assertion, &assignment), Ok(Value::Bool(true))))
}

fn same_multiset(lhs: &[TermId], rhs: &[TermId]) -> bool {
    if lhs.len() != rhs.len() {
        return false;
    }
    counts(lhs) == counts(rhs)
}

fn counts(terms: &[TermId]) -> BTreeMap<TermId, usize> {
    let mut counts = BTreeMap::new();
    for &term in terms {
        *counts.entry(term).or_insert(0) += 1;
    }
    counts
}

fn collect_bv_and_operands(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    match arena.node(term) {
        TermNode::App {
            op: Op::BvAnd,
            args,
        } if args.len() == 2 && arena.sort_of(term) == Sort::BitVec(1) => {
            collect_bv_and_operands(arena, args[0], out);
            collect_bv_and_operands(arena, args[1], out);
        }
        _ => out.push(term),
    }
}

fn match_negated_bv1_zero_equality(arena: &TermArena, term: TermId) -> Option<TermId> {
    let TermNode::App {
        op: Op::BoolNot,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [inner] = &**args else {
        return None;
    };
    let TermNode::App { op: Op::Eq, args } = arena.node(*inner) else {
        return None;
    };
    let [lhs, rhs] = &**args else {
        return None;
    };
    if is_bv_const(arena, *lhs, 1, 0) && arena.sort_of(*rhs) == Sort::BitVec(1) {
        Some(*rhs)
    } else if is_bv_const(arena, *rhs, 1, 0) && arena.sort_of(*lhs) == Sort::BitVec(1) {
        Some(*lhs)
    } else {
        None
    }
}

fn is_bv_const(arena: &TermArena, term: TermId, expected_width: u32, expected_value: u128) -> bool {
    matches!(
        arena.node(term),
        TermNode::BvConst { width, value }
            if *width == expected_width && *value == expected_value
    )
}

#[cfg(test)]
mod tests {
    use axeyum_smtlib::parse_script;

    use super::*;

    #[test]
    fn refutes_fifo32bc04k05_regression() {
        let text = include_str!(
            "../../../corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__fifo32bc04k05.smt2"
        );
        let script = parse_script(text).expect("parse fifo32bc04k05");
        let cert = fifo_bc04_refutation(&script.arena, &script.assertions)
            .expect("fifo32bc04k05 is the generated five-cycle FIFO contradiction");
        assert_eq!(cert.bound, FIFO_BOUND);
        assert_eq!(cert.index_width, FIFO_INDEX_WIDTH);
        assert_eq!(cert.element_width, FIFO_ELEMENT_WIDTH);
    }

    #[test]
    fn models_fifo32ia04k05_regression() {
        let text = include_str!(
            "../../../corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__fifo32ia04k05.smt2"
        );
        let script = parse_script(text).expect("parse fifo32ia04k05");
        let model = fifo_ia04_sat_model(&script.arena, &script.assertions)
            .expect("fifo32ia04k05 has the generated five-cycle FIFO counterexample");
        assert!(model_replays(&script.arena, &script.assertions, &model));
    }

    #[test]
    fn finite_fifo_equivalence_theorem_holds() {
        assert!(symbolic_fifo_equivalence_holds());
    }
}

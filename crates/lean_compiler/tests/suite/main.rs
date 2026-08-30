//! Every lean_compiler integration test, in ONE binary.
//!
//! Each file under `suite/` used to be its own test binary, and each one paid
//! the BLAKE2s R1CS again: a slow sequential symbolic circuit build, cached per
//! process, so thirteen processes meant thirteen builds. Those
//! matrices are no longer built at all (the walks of doc/leanvm Annex C
//! replaced them), so the original reason is gone; one binary still saves
//! thirteen process startups and thirteen guest compilations. None of these
//! tests engages
//! the proving arena (`lean_vm::init_prover`), so sharing a process is safe;
//! a test that does open a phase must not (see `rec_aggregation`'s `arena_prove`).

mod common;

mod assert_ne;
mod const_placeholder;
mod cse;
mod disassemble;
mod field_div;
mod field_towers;
mod filler;
mod hint_log2_ceil;
mod inline_expr;
mod pack64x2;
mod print_debug;
mod py_source;
mod range_check;
mod soundness;
mod stack_bits;
mod stack_buf;
mod statements;
mod transcript_helpers;
mod vm_proofs;

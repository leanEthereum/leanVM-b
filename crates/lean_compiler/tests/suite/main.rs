//! Every lean_compiler integration test, in ONE binary.
//!
//! Each file under `suite/` used to be its own test binary, and each one paid
//! `flock::blake2s::build_matrices` again: ~1.9 s of sequential symbolic circuit
//! building, cached per process, so thirteen processes meant thirteen builds.
//! As modules of a single binary they build it once. None of these tests engages
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
mod python_verifier;
mod range_check;
mod stack_buf;
mod transcript_helpers;
mod vm_proofs;
mod whir_query_table;

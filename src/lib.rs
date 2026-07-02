//! leanVM-b — arithmetization of a minimal binary-field zkVM (see `doc.tex`).
//!
//! **v2 design (in progress):** every machine value is an element of GF(2^128),
//! and logical indices are powers of a fixed generator `g`, so incrementing an
//! index is multiplication by `g` — a free virtual operation needing no
//! addition gadget. The witness is field-valued and committed directly by a
//! dense multilinear PCS (no bit-decomposition, no ring-switching).
//!
//! Modules:
//!
//! - [`compiler`] — a minimal Python-like zkDSL front end: parse → lower to the
//!   ISA (calls, `mul_range` loops in the exponent, `assert`, `blake3`) → witness,
//!   producing a provable [`cpu::Program`].
//! - [`field`] — GF(2^128) in GHASH form (flock), the generator `g`, and the
//!   g-power index helpers.
//! - [`transcript`] — Fiat–Shamir transcript (observe-and-fold in one op).
//! - [`multilinear`] — eq polynomial, folding, MLE evaluation, Lagrange eval.
//! - [`pcs`] — field-valued witness commitment via flock's Ligerito, opened at a
//!   plain point (§3).
//! - [`witness`] — field-valued columns stacked into one committed witness.
//! - [`gkr`] — the grand product via GKR (§4.3), which balances the bus.
//! - [`leaf`] — the shared bus: grand-product balance with g-power addresses /
//!   counts and the index column, decomposed to per-column claims (§4.2–§4.4, §5).
//! - [`constraints`] — the per-table degree-2 field zerocheck (§4.1): addresses,
//!   `XOR` sum, `MUL_NATIVE` product, `JUMP` selection.
//! - [`cpu`] — whole-program assembly: all six opcodes (`XOR`, `MUL_NATIVE`,
//!   `SET_CONSTANT`, `DEREF`, `JUMP`, `BLAKE3`) as tables sharing the
//!   state/memory/bytecode buses, with control flow, bound to one commitment and
//!   verified oracle-free.
//! - [`blake3_flock`] — the `BLAKE3` glue: flock's R1CS validity proof of the
//!   compressions, discharged against the SAME committed stack as the rest of the
//!   witness (single PCS), bound to the VM's memory values.

pub mod blake3_flock;
pub mod compiler;
pub mod constraints;
pub mod cpu;
pub mod field;
pub mod gkr;
pub mod leaf;
pub mod multilinear;
pub mod pcs;
pub mod tables;
pub mod transcript;
pub mod witness;

/// Below this many parallelizable items (sumcheck-round summands, per-block leaf
/// rows) a pass runs serially: rayon's fan-out overhead is not worth it for small
/// inputs. Shared by [`constraints`], [`gkr`], and [`leaf`].
pub(crate) const PAR_THRESHOLD: usize = 1 << 11;

/// `log2(n)` for a power-of-two `n`; panics otherwise (mirrors leanVM).
pub(crate) fn log2_strict_usize(n: usize) -> usize {
    assert!(n.is_power_of_two(), "not a power of two: {n}");
    n.trailing_zeros() as usize
}

/// `ceil(log2(n))` (mirrors leanVM).
pub(crate) const fn log2_ceil_usize(n: usize) -> usize {
    (usize::BITS - n.saturating_sub(1).leading_zeros()) as usize
}

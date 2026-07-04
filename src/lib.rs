//! leanVM-b — arithmetization of a minimal binary-field zkVM (see `doc.tex`).
//!
//! Every machine value is an element of GF(2^128), and logical indices are powers
//! of a fixed generator `g`, so incrementing an index is a multiplication by `g` —
//! a free virtual operation needing no addition gadget. The witness is field-valued
//! and committed directly by a dense multilinear PCS (no bit-decomposition).
//!
//! - [`compiler`] — Python-like zkDSL front end: parse → lower to the ISA → [`cpu::Program`].
//! - [`field`] — GF(2^128) in GHASH form, the generator `g`, and g-power helpers.
//! - [`transcript`] — Fiat–Shamir transcript (observe-and-fold in one op).
//! - [`multilinear`] — eq polynomial, folding, MLE and Lagrange evaluation.
//! - [`pcs`] — field-valued witness commitment via flock's Ligerito (§3).
//! - [`witness`] — field-valued columns stacked into one committed witness.
//! - [`gkr`] — the grand product via GKR (§4.3), balancing the bus.
//! - [`leaf`] — the shared bus: grand-product balance, decomposed to per-column claims (§4.2–§4.4, §5).
//! - [`constraints`] — the per-table degree-2 field zerocheck (§4.1).
//! - [`tables`] — the six instruction tables (columns, flushes, constraints).
//! - [`cpu`] — whole-program assembly, control flow, and the prove/verify entry points.
//! - [`blake3_flock`] — the `BLAKE3` glue: flock's R1CS validity proof over the same commitment.

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

/// Target soundness of the whole proof, in bits. Every round is designed to clear
/// this: the PCS runs the Ligerito `Secure` profile ([`pcs::PROFILE`], 120-bit),
/// and the bus grand product grinds up to it before its multiset challenge
/// ([`leaf`]). Raising it means bumping BOTH (a stronger profile and more grinding).
pub const SECURITY_BITS: u32 = 120;

/// Below this many parallelizable items a pass runs serially: rayon's fan-out
/// overhead is not worth it for small inputs. Shared by [`constraints`], [`gkr`], [`leaf`].
pub(crate) const PAR_THRESHOLD: usize = 1 << 11;

/// `log2(n)` for a power-of-two `n`; panics otherwise.
pub(crate) fn log2_strict_usize(n: usize) -> usize {
    assert!(n.is_power_of_two(), "not a power of two: {n}");
    n.trailing_zeros() as usize
}

/// `ceil(log2(n))`.
pub(crate) const fn log2_ceil_usize(n: usize) -> usize {
    (usize::BITS - n.saturating_sub(1).leading_zeros()) as usize
}

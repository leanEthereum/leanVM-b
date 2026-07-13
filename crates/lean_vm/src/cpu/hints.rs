//! Runtime hint machinery shared by the interpreter and the compiler: the
//! resolved hint ops a [`super::Program`] carries ([`RHint`]), and the g-power
//! table + reverse index the hint interpreter grows on demand.

use primitives::field::F64;
use std::collections::HashMap;

/// Frame-relative offset operand (matches the compiler's `ir::Off`).
pub type Off = u32;

/// A fast [`std::hash::Hasher`] for the g-power reverse index (`g^k ↦ k`). The
/// keys are field elements that are effectively uniform, so one multiplicative
/// mix of the two 64-bit limbs distributes well — far cheaper than the default
/// SipHash across the interpreter's millions of reverse-index lookups/inserts
/// (e.g. growing the index to `2^20` on a dynamic allocation).
#[derive(Default)]
pub struct GPowHasher(u64);

impl std::hash::Hasher for GPowHasher {
    #[inline]
    fn finish(&self) -> u64 {
        self.0
    }
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        // Fallback for non-u64 writes (F64's derived Hash uses `write_u64`, so
        // this is not on the hot path).
        for &b in bytes {
            self.0 = (self.0 ^ b as u64).wrapping_mul(0x0100_0000_01b3);
        }
    }
    #[inline]
    fn write_u64(&mut self, i: u64) {
        // F64 hashes its single limb through here.
        self.0 = (self.0 ^ i).wrapping_mul(0x9E37_79B9_7F4A_7C15);
    }
}

/// The g-power reverse index type: `F64 → u32` keyed by [`GPowHasher`].
pub type GPowMap = HashMap<F64, u32, std::hash::BuildHasherDefault<GPowHasher>>;

/// A hint resolved to concrete offsets/sizes, keyed by global program counter.
#[derive(Clone, Debug)]
pub enum RHint {
    /// Allocate a fresh region of `size` cells and write `g^{base}` to the cell.
    Alloc { ptr: Off, size: u32 },
    /// `Alloc` with the cell count read at runtime as the g-power exponent of
    /// `m[fp+size]`.
    AllocDyn { ptr: Off, size: Off },
    /// Pop stream `name`'s next entry (`len` values) into frame cells `fp+base+k`.
    WitnessStack { name: String, base: Off, len: u32 },
    /// Pop stream `name`'s next entry (`len` values) into heap cells `m[fp+ptr]·g^{lo+k}`.
    WitnessHeap { name: String, ptr: Off, lo: u32, len: u32 },
    /// Write `g^max(log2_ceil(value), floor)` into `fp+dst`, where `value` is the
    /// integer reconstructed from the `nbits` bits at the buffer `m[fp+bits_ptr]`.
    Log2Ceil { bits_ptr: Off, dst: Off, nbits: u32, floor: u32 },
    /// Write the `nbits` bits of `m[fp+value]` into the buffer `m[fp+bits_ptr]`.
    BitDecompose { value: Off, bits_ptr: Off, nbits: u32 },
    /// Write the `nbits` bits of `n`, where `m[fp+value] = g^n` (a bounded
    /// discrete log at witness generation), into the buffer `m[fp+bits_ptr]`.
    BitDecomposeExp { value: Off, bits_ptr: Off, nbits: u32 },
    /// Prover-side debug print (`print(...)` in the zkDSL): display the value
    /// of `m[fp+cell]` at this program point. Witness generation only.
    Print { label: String, cell: Off },
}

/// Extend the `g^j` table and its reverse index `g^j ↦ j` to cover index `upto`.
pub fn grow_gpow(gpow: &mut Vec<F64>, gmap: &mut GPowMap, upto: usize) {
    assert!(upto < (1 << 28), "address space overflow (program too large)");
    while gpow.len() <= upto {
        // ×g is ×x = `mul_by_g` (shift+fold), not a PMULL.
        let next = primitives::field::mul_by_g(*gpow.last().unwrap());
        gmap.insert(next, gpow.len() as u32);
        gpow.push(next);
    }
}

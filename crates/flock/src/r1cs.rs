// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Block-diagonal R1CS over GF(2).
//!
//! The standard R1CS is `(A·z) ⊙ (B·z) ⊕ (C·z) = 0`. We fix `C = I` (the
//! circuit-R1CS shape `(A·z) ⊙ (B·z) = z`), so the c-claim emitted by
//! zerocheck is already a `z`-claim, no transformation needed downstream.
//!
//! We further specialize to **block-diagonal `A` and `B`**:
//!   `A = I_{2^n_log} ⊗ A_0`, etc. The base matrices are `k × k` sparse
//! boolean (`k = 2^k_log`). `C_0 = I_k` is implicit, but the materialized
//! `c_0` matrix is still carried because [`BlockR1cs::r1cs_digest`] absorbs
//! it.

/// Sparse boolean matrix. `rows[i]` lists the column indices where the entry is 1.
#[derive(Clone, Debug)]
pub struct SparseBinaryMatrix {
    pub num_rows: usize,
    pub num_cols: usize,
    pub rows: Vec<Vec<usize>>,
}

/// Memory/variable layout of the committed witness (address bit `i` of the
/// packed buffer = MLE variable `i`): `addr = [k_log inner bits | n_log batch
/// bits]`, each instance one contiguous `2^k_log`-bit block. A one-variant
/// enum so the layout byte stays an explicit part of [`BlockR1cs::r1cs_digest`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum WitnessLayout {
    #[default]
    RowMajor,
}

/// Block-diagonal R1CS instance.
///
/// Total witness length: `N = 2^m = 2^k_log · 2^n_log`.
/// Base matrices `A_0`, `B_0`, `C_0` are each `k × k` with `k = 2^k_log`.
///
/// `k_skip` is the zerocheck's univariate-skip dimension (`k_skip ≤ k_log`).
/// It defines how the m-dim claim point is laid out in the protocol: one
/// univariate F192 coord binds the LSB `k_skip` bits, `k_log − k_skip`
/// multilinear F192 coords bind the next inner bits, and `n_log` multilinear
/// F192 coords bind the outer bits.
#[derive(Debug)]
pub struct BlockR1cs {
    pub m: usize,
    pub k_log: usize,
    pub k_skip: usize,
    /// Useful bits per block: rows `[0, useful_bits)` of each block carry real
    /// witness data; rows `[useful_bits, 2^k_log)` are zero padding (and have
    /// empty rows in `a_0/b_0`). Default `1 << k_log` (no padding). The prover
    /// can use this to skip URM work on chunks that fall entirely in padding.
    pub useful_bits: usize,
    pub a_0: SparseBinaryMatrix,
    pub b_0: SparseBinaryMatrix,
    pub c_0: SparseBinaryMatrix,
    /// Memory/variable layout of the committed witness (see [`WitnessLayout`]).
    /// Bound into [`Self::r1cs_digest`].
    pub layout: WitnessLayout,
    /// Column of a constant-one wire to pin to 1 across all blocks, or `None`.
    /// Drives the lincheck constant-wire pin (see
    /// [`crate::lincheck::LincheckCircuit::const_pin_col`]): without it, the
    /// all-zero witness satisfies every homogeneous constraint row.
    pub const_pin: Option<usize>,
    /// Lazily-cached CSC transpose of `(a_0, b_0)` for lincheck's
    /// `fold_alpha_batched`, see [`Self::csc_lincheck_circuit`]. The matrices
    /// are public fields, so mutating them after the cache is populated leaves
    /// a stale cache, so don't do that.
    #[doc(hidden)]
    pub csc_cache: std::sync::OnceLock<crate::lincheck::CscCircuit>,
}

// Manual Clone so the clone starts with an empty cache: it recomputes lazily on
// first use, which is what a copy of the matrices should do.
impl Clone for BlockR1cs {
    fn clone(&self) -> Self {
        Self {
            m: self.m,
            k_log: self.k_log,
            k_skip: self.k_skip,
            useful_bits: self.useful_bits,
            a_0: self.a_0.clone(),
            b_0: self.b_0.clone(),
            c_0: self.c_0.clone(),
            layout: self.layout,
            const_pin: self.const_pin,
            csc_cache: std::sync::OnceLock::new(),
        }
    }
}

impl BlockR1cs {
    /// Total witness length = 2^m.
    pub fn n(&self) -> usize {
        1usize << self.m
    }

    /// CSC-transposed `LincheckCircuit` over this R1CS's sparse matrices:
    /// the fastest `fold_alpha_batched` when `a_0`/`b_0` are materialized
    /// (gather per column instead of scatter per row). Built lazily on first
    /// access and cached; call once at setup to keep the build cost (one pass
    /// over the nonzeros) out of the prove path.
    pub fn csc_lincheck_circuit(&self) -> &crate::lincheck::CscCircuit {
        self.csc_cache.get_or_init(|| {
            crate::lincheck::CscCircuit::from_matrices(&self.a_0, &self.b_0).with_const_pin(self.const_pin)
        })
    }

    /// Apply `A = I_{2^n_log} ⊗ A_0` to a Boolean witness `z`. Returns
    /// `a = A · z` ∈ GF(2)^N (length 2^m).
    #[cfg(test)]
    pub fn apply_a(&self, z: &[bool]) -> Vec<bool> {
        apply_block_diag(&self.a_0, z, self.k_log)
    }

    /// Apply `B = I_{2^n_log} ⊗ B_0` to `z`.
    #[cfg(test)]
    pub fn apply_b(&self, z: &[bool]) -> Vec<bool> {
        apply_block_diag(&self.b_0, z, self.k_log)
    }

    /// Apply `C = I_{2^n_log} ⊗ C_0` to `z`.
    #[cfg(test)]
    pub fn apply_c(&self, z: &[bool]) -> Vec<bool> {
        apply_block_diag(&self.c_0, z, self.k_log)
    }

    /// Check whether `(A·z) ⊙ (B·z) = C·z` (over GF(2), Hadamard product).
    #[cfg(test)]
    pub fn satisfies(&self, z: &[bool]) -> bool {
        assert_eq!(z.len(), self.n());
        let a = self.apply_a(z);
        let b = self.apply_b(z);
        let c = self.apply_c(z);
        a.iter()
            .zip(b.iter())
            .zip(c.iter())
            .all(|((ai, bi), ci)| (*ai & *bi) == *ci)
    }

    /// BLAKE2s hash of the R1CS itself: the per-block matrices, the shape
    /// parameters and the constant-wire pin, explicitly WITHOUT the instance
    /// count `m`. It therefore identifies every block-diagonal instance built
    /// from these matrices at once, whatever the count. The full instance is `m`
    /// copies of them, so a protocol that binds this digest and `m` separately
    /// has bound the whole statement; embedding protocols (leanVM-b) seed their
    /// transcript with it and announce the count.
    pub fn r1cs_digest(&self) -> [u8; 32] {
        let mut h = primitives::blake2s::Hasher::new();
        // v3: v1 absorbed the matrices in sparse form, v2 their dense bit image
        // (see `absorb_matrix`), and this one adds the constant-wire pin.
        h.update(b"flock-r1cs-digest-v3");
        h.update(&(self.k_log as u64).to_le_bytes());
        h.update(&(self.k_skip as u64).to_le_bytes());
        // The layout determines which polynomial a given witness commits
        // to, so it is part of the statement.
        h.update(&[match self.layout {
            WitnessLayout::RowMajor => 0u8,
        }]);
        // So is the constant-wire pin: it enters the verifier's own equation as
        // lincheck's `β = α³` term. `useful_bits` stays out, no verifier reads it.
        match self.const_pin {
            None => h.update(&[0u8]),
            Some(col) => h.update(&[1u8]).update(&(col as u64).to_le_bytes()),
        };
        absorb_matrix(&mut h, &self.a_0);
        absorb_matrix(&mut h, &self.b_0);
        absorb_matrix(&mut h, &self.c_0);
        h.finalize()
    }
}

/// Absorb a matrix into a BLAKE2s hasher as its DENSE bit image: the shape as
/// two little-endian u64, then each row's `num_cols` bits packed LSB-first and
/// padded to a byte boundary.
///
/// Dense rather than sparse for two reasons. It is canonical: over GF(2) a
/// repeated column index cancels and a reordered row is the same matrix, so the
/// sparse form commits to an encoding rather than to the matrix. And at these
/// densities (13% to 20%) it is seven times shorter, one bit per entry against
/// eight bytes per nonzero, which is the whole cost of [`BlockR1cs::r1cs_digest`].
fn absorb_matrix(h: &mut primitives::blake2s::Hasher, m: &SparseBinaryMatrix) {
    assert_eq!(m.rows.len(), m.num_rows);
    h.update(&(m.num_rows as u64).to_le_bytes());
    h.update(&(m.num_cols as u64).to_le_bytes());
    // A row at a time: the scatter stays inside an L1-resident buffer, and the
    // full bit image is never materialized.
    let mut bits = vec![0u8; m.num_cols.div_ceil(8)];
    for row in &m.rows {
        for &col in row {
            assert!(col < m.num_cols, "column index out of range");
            bits[col / 8] ^= 1 << (col % 8);
        }
        h.update(&bits);
        bits.fill(0);
    }
}

/// Block-diagonal `(I_{2^n_log} ⊗ M_0) · z` over GF(2).
#[cfg(test)]
pub(crate) fn apply_block_diag(m_0: &SparseBinaryMatrix, z: &[bool], k_log: usize) -> Vec<bool> {
    let k = 1usize << k_log;
    assert_eq!(m_0.num_rows, k);
    assert_eq!(m_0.num_cols, k);
    assert_eq!(z.len() % k, 0);
    let mut out = Vec::with_capacity(z.len());
    for z_block in z.chunks_exact(k) {
        out.extend(
            m_0.rows
                .iter()
                .map(|row| row.iter().fold(false, |acc, &col| acc ^ z_block[col])),
        );
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::witness::identity;

    #[test]
    fn identity_matrices_accept_any_witness() {
        // A_0 = B_0 = C_0 = I_k ⇒ a = z, b = z, c = z. Boolean idempotence
        // makes the circuit-R1CS constraint trivially satisfied for any z.
        let k_log = 3;
        let m = 6;
        let r1cs = BlockR1cs {
            m,
            k_log,
            k_skip: 2,
            useful_bits: 1 << k_log,
            a_0: identity(1 << k_log),
            b_0: identity(1 << k_log),
            c_0: identity(1 << k_log),
            layout: WitnessLayout::RowMajor,
            const_pin: None,
            csc_cache: std::sync::OnceLock::new(),
        };
        for seed in 0..4 {
            let z: Vec<bool> = (0..(1 << m)).map(|i| ((i ^ seed) & 1) == 1).collect();
            assert!(r1cs.satisfies(&z), "seed={seed}");
        }
    }

    #[test]
    fn zero_matrices_require_zero_witness() {
        // A_0 = B_0 = 0, C_0 = I ⇒ a·b = 0 ⇒ z = 0.
        let k_log = 3;
        let m = 6;
        let zero = SparseBinaryMatrix {
            num_rows: 1 << k_log,
            num_cols: 1 << k_log,
            rows: vec![Vec::new(); 1 << k_log],
        };
        let r1cs = BlockR1cs {
            m,
            k_log,
            k_skip: 2,
            useful_bits: 1 << k_log,
            a_0: zero.clone(),
            b_0: zero,
            c_0: identity(1 << k_log),
            layout: WitnessLayout::RowMajor,
            const_pin: None,
            csc_cache: std::sync::OnceLock::new(),
        };
        let z_zero = vec![false; 1 << m];
        assert!(r1cs.satisfies(&z_zero));
        let mut z_nonzero = vec![false; 1 << m];
        z_nonzero[5] = true;
        assert!(!r1cs.satisfies(&z_nonzero));
    }
}

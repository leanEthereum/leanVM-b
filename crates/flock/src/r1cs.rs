// Credit: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Block-diagonal R1CS over GF(2).
//!
//! The standard R1CS is `(A·z) ⊙ (B·z) ⊕ (C·z) = 0`. We fix `C = I` (the
//! circuit-R1CS shape `(A·z) ⊙ (B·z) = z`), so the c-claim emitted by
//! zerocheck is already a `z`-claim — no transformation needed downstream.
//!
//! We further specialize to **block-diagonal `A` and `B`**:
//!   `A = I_{2^n_log} ⊗ A_0`, etc. The base matrices are `k × k` sparse
//! boolean (`k = 2^k_log`). `C_0 = I_k` is implicit (we still carry the
//! materialized `c_0` matrix for utilities like `satisfies`).

/// Sparse boolean matrix. `rows[i]` lists the column indices where the entry is 1.
#[derive(Clone, Debug)]
pub struct SparseBinaryMatrix {
    pub num_rows: usize,
    pub num_cols: usize,
    pub rows: Vec<Vec<usize>>,
}

/// Memory/variable layout of the committed witness (address bit `i` of the
/// packed buffer = MLE variable `i`).
///
/// - **RowMajor** (legacy): `addr = [k_log inner bits | n_log batch bits]` —
///   each instance is one contiguous `2^k_log`-bit block.
/// - **BatchMajor**: `addr = [7 in-word bits | n_log batch | k_log−7 chunk]`
///   — column-major at 128-bit chunk granularity. The sumcheck binds the
///   batch dims right after the univariate skip + one in-word round (the
///   fold-log_n-first order required for jagged multi-table composition),
///   the batch dims live over the ring-switch suffix (packed words), and
///   per-block zero padding coalesces into one contiguous buffer suffix.
///
/// Convention for **`ZClaim` points under BatchMajor**: `x_inner_rest`
/// holds only the address-dim-6 coordinate and `x_outer` holds
/// `[batch…, chunk…]`, so the PCS-side concatenation
/// `x_inner_rest ++ x_outer` yields the address-ordered suffix for the
/// committed polynomial. (Lincheck's *semantic* `QuirkyPoint` is unchanged
/// in both layouts.) Requires `k_log ≥ 7` and `k_skip = 6`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum WitnessLayout {
    #[default]
    RowMajor,
    BatchMajor,
}

/// Block-diagonal R1CS instance.
///
/// Total witness length: `N = 2^m = 2^k_log · 2^n_log`.
/// Base matrices `A_0`, `B_0`, `C_0` are each `k × k` with `k = 2^k_log`.
///
/// `k_skip` is the zerocheck's univariate-skip dimension (`k_skip ≤ k_log`).
/// It defines how the m-dim claim point is laid out in the protocol: one
/// univariate F128 coord binds the LSB `k_skip` bits, `k_log − k_skip`
/// multilinear F128 coords bind the next inner bits, and `n_log` multilinear
/// F128 coords bind the outer bits.
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
    /// Bound into [`Self::statement_digest`]; the prover and verifier derive
    /// their claim-point assembly from it.
    pub layout: WitnessLayout,
    /// Column of a constant-one wire to pin to 1 across all blocks, or `None`.
    /// Drives the lincheck constant-wire pin for matrix-based encoders whose
    /// circuit is built from these matrices (BLAKE3, SHA-2 via
    /// [`Self::csc_lincheck_circuit`]). Walker-based encoders (Keccak) set this
    /// `None` and carry the pin on their own `LincheckCircuit`. See
    /// `docs/const-wire-pin.md`.
    pub const_pin: Option<usize>,
    /// Lazily-cached CSC transpose of `(a_0, b_0)` for lincheck's
    /// `fold_alpha_batched` — see [`Self::csc_lincheck_circuit`]. The matrices
    /// are public fields, so mutating them after the cache is populated leaves
    /// a stale cache — don't do that.
    #[doc(hidden)]
    pub csc_cache: std::sync::OnceLock<crate::lincheck::CscCircuit>,
}

// Manual Clone — std::sync::OnceLock doesn't derive Clone, and a fresh cache
// after cloning is the right behavior (recomputes lazily on first use).
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
    /// Inner dimension = 2^k_log = base-matrix side.
    pub fn k(&self) -> usize {
        1usize << self.k_log
    }
    /// Total witness length = 2^m.
    pub fn n(&self) -> usize {
        1usize << self.m
    }

    /// CSC-transposed `LincheckCircuit` over this R1CS's sparse matrices —
    /// the fastest `fold_alpha_batched` when `a_0`/`b_0` are materialized
    /// (gather per column instead of scatter per row). Built lazily on first
    /// access and cached; call once at setup to keep the build cost (one pass
    /// over the nonzeros) out of the prove path. NOT meaningful for setups
    /// whose `BlockR1cs` carries empty matrix stubs (e.g. Keccak) — those
    /// must keep their circuit walkers.
    pub fn csc_lincheck_circuit(&self) -> &crate::lincheck::CscCircuit {
        self.csc_cache.get_or_init(|| {
            crate::lincheck::CscCircuit::from_matrices(&self.a_0, &self.b_0)
                .with_const_pin(self.const_pin)
        })
    }

    /// Apply `A = I_{2^n_log} ⊗ A_0` to a Boolean witness `z`. Returns
    /// `a = A · z` ∈ GF(2)^N (length 2^m).
    pub fn apply_a(&self, z: &[bool]) -> Vec<bool> {
        apply_block_diag(&self.a_0, z, self.k_log)
    }

    /// Apply `B = I_{2^n_log} ⊗ B_0` to `z`.
    pub fn apply_b(&self, z: &[bool]) -> Vec<bool> {
        apply_block_diag(&self.b_0, z, self.k_log)
    }

    /// Apply `C = I_{2^n_log} ⊗ C_0` to `z`.
    pub fn apply_c(&self, z: &[bool]) -> Vec<bool> {
        apply_block_diag(&self.c_0, z, self.k_log)
    }

    /// Check whether `(A·z) ⊙ (B·z) = C·z` (over GF(2), Hadamard product).
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

    // -----------------------------------------------------------------------
    // Packed variants: operate on F_{2^128}-packed witnesses (polynomial-basis
    // bit layout: bit r of z_packed[i] = logical bit i·128 + r). This is the
    // canonical witness form throughout the protocol.
    // -----------------------------------------------------------------------

    // -----------------------------------------------------------------------
    // Layout-aware protocol bookkeeping — the single source of truth for how
    // the zerocheck's address-ordered challenges map to lincheck's semantic
    // quirky point and to the PCS claims' address-ordered points. Shared by
    // `flock_prover::prover::prove_fast_core` and `verifier::verify_core`
    // (any divergence between the two is a transcript break, so both call
    // these).
    // -----------------------------------------------------------------------

    /// BLAKE3 hash of the circuit FAMILY: the per-block matrices and the
    /// shape parameters, explicitly WITHOUT the instance count `m`. The full
    /// instance is block-diagonal — `m` copies of these matrices — so a
    /// protocol that binds this digest and `m` separately has bound the whole
    /// statement; embedding protocols (leanVM-b) seed their transcript with it
    /// and announce the count, instead of absorbing the per-instance
    /// [`Self::statement_digest`] mid-proof.
    pub fn family_digest(&self) -> [u8; 32] {
        let mut h = blake3::Hasher::new();
        h.update(b"flock-r1cs-family-v1");
        h.update(&(self.k_log as u64).to_le_bytes());
        h.update(&(self.k_skip as u64).to_le_bytes());
        // The layout determines which polynomial a given witness commits
        // to — it is part of the statement.
        h.update(&[match self.layout {
            WitnessLayout::RowMajor => 0u8,
            WitnessLayout::BatchMajor => 1u8,
        }]);
        absorb_matrix(&mut h, &self.a_0);
        absorb_matrix(&mut h, &self.b_0);
        absorb_matrix(&mut h, &self.c_0);
        *h.finalize().as_bytes()
    }

}

/// Length-prefixed absorption of a sparse matrix into a BLAKE3 hasher.
/// `(num_rows, num_cols, [(row_len, col_indices...) for each row])`, all
/// little-endian u64, so two matrices with different shapes/contents always
/// produce different states.
fn absorb_matrix(h: &mut blake3::Hasher, m: &SparseBinaryMatrix) {
    h.update(&(m.num_rows as u64).to_le_bytes());
    h.update(&(m.num_cols as u64).to_le_bytes());
    for row in &m.rows {
        h.update(&(row.len() as u64).to_le_bytes());
        for &col in row {
            h.update(&(col as u64).to_le_bytes());
        }
    }
}

/// Block-diagonal `(I_{2^n_log} ⊗ M_0) · z` over GF(2).
fn apply_block_diag(m_0: &SparseBinaryMatrix, z: &[bool], k_log: usize) -> Vec<bool> {
    let k = 1usize << k_log;
    assert_eq!(m_0.num_rows, k);
    assert_eq!(m_0.num_cols, k);
    assert_eq!(z.len() % k, 0);
    let n_outer = z.len() / k;
    let mut out = vec![false; z.len()];
    for i_outer in 0..n_outer {
        let z_block = &z[i_outer * k..(i_outer + 1) * k];
        let a_block = matrix_vector_product(m_0, z_block);
        out[i_outer * k..(i_outer + 1) * k].copy_from_slice(&a_block);
    }
    out
}

/// `out[i] = ⊕_{j: M[i, j] = 1} z[j]` (over GF(2)).
fn matrix_vector_product(m: &SparseBinaryMatrix, z: &[bool]) -> Vec<bool> {
    assert_eq!(z.len(), m.num_cols);
    m.rows
        .iter()
        .map(|row| {
            let mut acc = false;
            for &col in row {
                acc ^= z[col];
            }
            acc
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Identity base matrix: `A_0 = I_k`. Each row has exactly one nonzero at
    /// the diagonal.
    fn identity(k: usize) -> SparseBinaryMatrix {
        SparseBinaryMatrix {
            num_rows: k,
            num_cols: k,
            rows: (0..k).map(|i| vec![i]).collect(),
        }
    }

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
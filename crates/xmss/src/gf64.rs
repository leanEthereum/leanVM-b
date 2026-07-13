//! A minimal GF(2^64) — `x^64 + x^4 + x^3 + x + 1`, bits little-endian (bit `k`
//! is the coefficient of `x^k`) — just enough to compute the `g^{num_bytes}`
//! size element of the Merkle-Damgard IV. Matches the VM's field
//! (`primitives::field::F64`) without depending on it.

/// Multiply by `x` (the generator `g`): one shift, one conditional fold of
/// the reduction pentanomial (`0x1B`).
#[inline]
const fn mul_by_x(z: u64) -> u64 {
    let carry = z >> 63;
    (z << 1) ^ (0x1B * carry)
}

/// `g^n` as the 8 little-endian bytes of the field element. Linear in `n`
/// (one shift per step); `n` is a byte count — small, and computed once per
/// hash call.
pub fn g_pow_bytes(n: usize) -> [u8; 8] {
    let mut z: u64 = 1;
    let mut i = 0;
    while i < n {
        z = mul_by_x(z);
        i += 1;
    }
    z.to_le_bytes()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn small_powers_are_monomials() {
        // For n < 64, g^n is the monomial x^n: bit n set.
        assert_eq!(g_pow_bytes(0), 1u64.to_le_bytes());
        assert_eq!(g_pow_bytes(1), 2u64.to_le_bytes());
        assert_eq!(g_pow_bytes(48), (1u64 << 48).to_le_bytes());
        // Past x^63 the reduction folds in 0x1B.
        assert_eq!(g_pow_bytes(64), 0x1Bu64.to_le_bytes());
    }
}

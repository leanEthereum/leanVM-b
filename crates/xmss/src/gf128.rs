//! A minimal GF(2^128) in GHASH form — `x^128 + x^7 + x^2 + x + 1`, bits
//! little-endian (bit `k` is the coefficient of `x^k`) — just enough to
//! compute the `g^{num_bytes}` size element of the Merkle-Damgard IV.
//! Matches the VM's field (`primitives::field::F128`) without
//! depending on it.

/// Multiply by `x` (the generator `g`): one shift, one conditional fold of
/// the reduction polynomial (`0x87`).
#[inline]
const fn mul_by_x(z: u128) -> u128 {
    let carry = z >> 127;
    (z << 1) ^ (0x87 * carry)
}

/// `g^n` as the 16 little-endian bytes of the field element. Linear in `n`
/// (one shift per step); `n` is a byte count — small, and computed once per
/// hash call.
pub fn g_pow_bytes(n: usize) -> [u8; 16] {
    let mut z: u128 = 1;
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
        // For n < 128, g^n is the monomial x^n: bit n set.
        assert_eq!(g_pow_bytes(0), 1u128.to_le_bytes());
        assert_eq!(g_pow_bytes(1), 2u128.to_le_bytes());
        assert_eq!(g_pow_bytes(96), (1u128 << 96).to_le_bytes());
        // Past x^127 the reduction folds in 0x87.
        assert_eq!(g_pow_bytes(128), 0x87u128.to_le_bytes());
    }
}

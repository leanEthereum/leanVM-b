use primitives::field::F192;

/// Deterministic SplitMix64 generator shared by the crate's unit tests.
pub(crate) struct Rng(u64);

impl Rng {
    pub(crate) fn new(seed: u64) -> Self {
        Self(seed)
    }

    pub(crate) fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    pub(crate) fn bit(&mut self) -> bool {
        self.next_u64() & 1 != 0
    }

    pub(crate) fn bits(&mut self, n: usize) -> Vec<bool> {
        (0..n).map(|_| self.bit()).collect()
    }

    pub(crate) fn ext(&mut self) -> F192 {
        F192::new(self.next_u64(), self.next_u64(), self.next_u64())
    }

    pub(crate) fn ext_vec(&mut self, n: usize) -> Vec<F192> {
        (0..n).map(|_| self.ext()).collect()
    }
}

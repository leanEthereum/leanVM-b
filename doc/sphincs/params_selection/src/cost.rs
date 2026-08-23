//! Signature size and hash counts for one SPHINCS+ parameter set.
//!
//! Ported from `costs.sage` of BlockstreamResearch/SPHINCS-Parameters, which is
//! the companion to "Hash-based Signature Schemes for Bitcoin". `tests/goldens`
//! pins every number this module produces against that repo's frozen fixtures
//! and against the report's own tables.

use std::ops::{Add, Mul, Sub};

/// The WOTS+C grinding counter, carried once per hypertree layer.
pub const COUNTER_BYTES: u64 = 4;

/// What something costs.
///
/// `compressions` is the number everything here is measured in and the only one
/// reported. `hashes`, the number of tweakable-hash and PRF invocations, is
/// carried alongside it only because the report publishes hash counts too, so
/// `tests/goldens` can check this model against both of its columns.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Cost {
    pub hashes: u64,
    pub compressions: u64,
}

impl Cost {
    pub const fn new(hashes: u64, compressions: u64) -> Self {
        Self { hashes, compressions }
    }
}

impl Add for Cost {
    type Output = Self;
    fn add(self, o: Self) -> Self {
        Self::new(
            self.hashes.saturating_add(o.hashes),
            self.compressions.saturating_add(o.compressions),
        )
    }
}

impl Sub for Cost {
    type Output = Self;
    fn sub(self, o: Self) -> Self {
        Self::new(self.hashes - o.hashes, self.compressions - o.compressions)
    }
}

impl Mul<u64> for Cost {
    type Output = Self;
    fn mul(self, m: u64) -> Self {
        Self::new(self.hashes.saturating_mul(m), self.compressions.saturating_mul(m))
    }
}

/// One compression per 64 bytes of hash input.
pub const BLOCK: u64 = 64;

/// The message a signature covers: a 256-bit digest of it.
pub const MESSAGE_BYTES: u64 = 32;

/// What each kind of hash costs, in compression calls.
///
/// Every hash here is `Th(P, tweak, payload)`, whose input is the n-byte public
/// parameter, the n-byte tweak, and then the payload, and the compression
/// function takes 64 bytes of it at a time. BLAKE2s absorbs 64 bytes per call
/// and carries the byte counter and final-block flag as compression inputs
/// rather than as a block, so nothing is spent on padding; SHA-256 under the
/// length-prefixed Merkle-Damgard of `primitives::sha2` behaves the same way.
///
/// At n = 16 that makes a chain step and a Merkle node one compression each,
/// the message hash two, and the compression of `m` hash values
/// `ceil((32 + 16m) / 64)`. Which is, for every m, exactly what the report's
/// SHA-2 layout with the PK.seed midstate cached comes to, so its published
/// compression counts are still the yardstick in `tests/goldens`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Blocks {
    pub n: u64,
}

impl Blocks {
    pub const fn new(n: u64) -> Self {
        Self { n }
    }
    /// Compressions for a hash over `payload` bytes.
    pub const fn of(&self, payload: u64) -> u64 {
        (2 * self.n + payload).div_ceil(BLOCK)
    }
    /// A secret key element from the seed.
    pub const fn prf(&self) -> u64 {
        self.of(self.n)
    }
    /// One step along a WOTS chain.
    pub const fn chain_step(&self) -> u64 {
        self.of(self.n)
    }
    /// The same, plus the WOTS+C counter the verifier hashes in once per layer.
    pub const fn chain_step_with_counter(&self) -> u64 {
        self.of(self.n + COUNTER_BYTES)
    }
    /// One Merkle node from its two children.
    pub const fn merkle_node(&self) -> u64 {
        self.of(2 * self.n)
    }
    /// Compressing `values` hash values into one: a WOTS public key, or the
    /// FORS roots.
    pub const fn compress(&self, values: u64) -> u64 {
        self.of(values * self.n)
    }
    /// The randomized message digest, over R, PK.root and the message.
    pub const fn message_hash(&self) -> u64 {
        self.of(2 * self.n + MESSAGE_BYTES)
    }
    /// Deriving that randomness from the secret seed and the message.
    pub const fn message_prf(&self) -> u64 {
        self.of(self.n + MESSAGE_BYTES)
    }
}

/// Which one-time and few-time schemes a parameter set is built from.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Scheme {
    /// Plain SPHINCS+ / SLH-DSA: WOTS-TW + FORS.
    Spx,
    /// WOTS+C (fixed digit sum, no checksum chains) + FORS.
    Wc,
    /// WOTS+C + FORS+C (last FORS tree removed by grinding).
    WcFc,
}

pub const SCHEMES: [Scheme; 3] = [Scheme::Spx, Scheme::Wc, Scheme::WcFc];

impl Scheme {
    pub const fn wots_c(self) -> bool {
        !matches!(self, Scheme::Spx)
    }
    pub const fn fors_c(self) -> bool {
        matches!(self, Scheme::WcFc)
    }
    pub const fn label(self) -> &'static str {
        match self {
            Scheme::Spx => "SPX",
            Scheme::Wc => "W+C",
            Scheme::WcFc => "W+C_F+C",
        }
    }
    pub fn parse(s: &str) -> Option<Self> {
        SCHEMES.into_iter().find(|x| x.label().eq_ignore_ascii_case(s))
    }
    /// FORS trees actually built and authenticated: FORS+C grinds the last away.
    pub const fn trees(self, k: u64) -> u64 {
        if self.fors_c() { k - 1 } else { k }
    }
}

/// How a WOTS+C digest is cut into base-w chain positions.
///
/// The report drops chains by forcing their digits to zero (its parameter z).
/// This uses the bit-pinning variant it offers as an alternative in "Complexity
/// Analysis of WOTS+C" (its z_b), which is what `doc/xmss/main.tex` does,
/// because it keeps the digest a whole number of chunks and needs no
/// partial-digit handling anywhere:
///
/// ```text
/// chain_bits = log2(w)                     bits one chain carries
/// pinned     = (8n) mod chain_bits          + chain_bits * dropped_chains
/// chains     = (8n - pinned) / chain_bits   = floor(8n/chain_bits) - dropped
/// ```
///
/// The signer grinds the counter until the digest has its `pinned` top bits zero
/// AND its `chains` digits summing to S_wn, so out of the 2^(8n) digests exactly
/// nu = |{tuples summing to S_wn}| are admissible (see [`NuTable`]).
///
/// Pinning is not free: every pinned bit halves the admissible fraction, so
/// `pinned` bits multiply the expected grinding by 2^pinned. It buys chains
/// cheaply though. The default is the minimum that leaves `8n - pinned` a
/// multiple of `chain_bits`, and what it saves is the extra, only partly used
/// chain that `ceil(8n / chain_bits)` would need: n bytes of signature for a
/// factor 2^(8n mod chain_bits), which at chain_bits = 3 is 16 bytes for 4x on a
/// per-layer grind of a few hundred hashes. Each further dropped chain then
/// saves another n bytes for a factor of about w.
///
/// `doc/xmss/main.tex` is the (n=128, chain_bits=3) instance: 128 mod 3 = 2 bits
/// pinned, v = 42 chains, T = 195. Dropping one more chain there would pin
/// 2 + 3 = 5 bits and leave 41 chains. For every w the report itself uses (16
/// and 256) chain_bits divides 128, so nothing is pinned.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Encoding {
    pub w: u64,
    pub n: u64,
    pub dropped_chains: u64,
    pub chain_bits: u64,
    pub pinned_bits: u64,
    pub chains: u64,
}

impl Encoding {
    /// `None` when `w` is not a power of two, or when nothing is left to sign.
    pub fn new(w: u64, n: u64, dropped_chains: u64) -> Option<Self> {
        if w < 2 || !w.is_power_of_two() {
            return None;
        }
        let chain_bits = w.trailing_zeros() as u64;
        let pinned_bits = (8 * n) % chain_bits + chain_bits * dropped_chains;
        let chains = (8 * n).checked_sub(pinned_bits)? / chain_bits;
        if chains < 1 {
            return None;
        }
        Some(Self {
            w,
            n,
            dropped_chains,
            chain_bits,
            pinned_bits,
            chains,
        })
    }

    /// Mean digit sum, where the admissible digests are densest.
    pub const fn default_swn(&self) -> u64 {
        self.chains * (self.w - 1) / 2
    }

    /// Largest reachable digit sum: every chain at the top.
    pub const fn max_swn(&self) -> u64 {
        self.chains * (self.w - 1)
    }
}

/// How many digests a target sum admits, and what that costs the signer.
///
/// `counts[s]` is the number of `l`-tuples over `[0, w-1]` summing to `s`, that
/// is the coefficient of `x^s` in `(1 + x + ... + x^(w-1))^l`. Built by the
/// obvious convolution rather than by the report's inclusion-exclusion formula,
/// because the formula's intermediate binomials dwarf its result and would need
/// bignums, while every coefficient here is bounded by the total `w^l <= 2^128`.
///
/// `trials[s]` is the expected number of counter values the signer tries per
/// hypertree layer, `ceil(2^(8n) / counts[s])`, saturated at `u64::MAX`: a set
/// needing more counters than that is beyond any budget anyway.
#[derive(Clone, Debug)]
pub struct NuTable {
    pub l: u64,
    pub w: u64,
    pub digest_bits: u32,
    counts: Vec<u128>,
    trials: Vec<u64>,
}

impl NuTable {
    pub fn new(l: u64, w: u64, digest_bits: u32) -> Self {
        assert!(
            digest_bits <= 128,
            "a digest wider than 128 bits overflows the u128 counts"
        );
        let degree = (l * (w - 1)) as usize;
        let mut cur = vec![0u128; degree + 1];
        let mut next = vec![0u128; degree + 1];
        cur[0] = 1;
        for round in 1..=l {
            let hi = (round * (w - 1)) as usize;
            // next[s] = sum of the w preceding entries of cur, kept as a running
            // window: the window's value is itself a coefficient of the next
            // row, so it cannot exceed w^round <= 2^128.
            let mut window = 0u128;
            for s in 0..=hi {
                window = window.checked_add(cur[s]).expect("digit-sum count overflowed u128");
                if s >= w as usize {
                    window -= cur[s - w as usize];
                }
                next[s] = window;
            }
            std::mem::swap(&mut cur, &mut next);
            cur[hi + 1..].fill(0);
        }
        let total_minus_1 = if digest_bits == 128 {
            u128::MAX
        } else {
            (1u128 << digest_bits) - 1
        };
        let trials = cur
            .iter()
            .map(|&nu| {
                if nu == 0 {
                    return u64::MAX;
                }
                // ceil(2^digest_bits / nu) = floor((2^digest_bits - 1)/nu) + 1,
                // saturating: nu = 1 would otherwise carry the +1 past u128.
                u64::try_from((total_minus_1 / nu).saturating_add(1)).unwrap_or(u64::MAX)
            })
            .collect();
        Self {
            l,
            w,
            digest_bits,
            counts: cur,
            trials,
        }
    }

    /// Digests with the pinned bits zero and digits summing to `swn`.
    pub fn nu(&self, swn: u64) -> u128 {
        self.counts.get(swn as usize).copied().unwrap_or(0)
    }

    /// Counter values tried per layer at this target sum.
    pub fn trials(&self, swn: u64) -> u64 {
        self.trials.get(swn as usize).copied().unwrap_or(u64::MAX)
    }

    /// The least grinding any target sum can ask for.
    ///
    /// Read off the table rather than assumed to sit at the mean, so nothing
    /// downstream depends on where the distribution peaks.
    pub fn min_trials(&self) -> u64 {
        self.trials.iter().copied().min().unwrap_or(u64::MAX)
    }
}

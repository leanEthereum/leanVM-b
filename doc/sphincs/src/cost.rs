//! Signature size and hash counts for one SPHINCS+ parameter set.
//!
//! Ported from `costs.sage` of BlockstreamResearch/SPHINCS-Parameters, which is
//! the companion to "Hash-based Signature Schemes for Bitcoin". `tests/goldens`
//! pins every number this module produces against that repo's frozen fixtures
//! and against the report's own tables.

use std::ops::{Add, Mul, Sub};

/// The WOTS+C grinding counter, carried once per hypertree layer.
pub const COUNTER_BYTES: u64 = 4;

/// A cost in both units the report uses.
///
/// `hashes` counts tweakable-hash and PRF invocations (its "hash" columns),
/// `compressions` counts SHA-256 compression calls (its Compr. columns).
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

/// Compression calls charged to each kind of hash invocation.
///
/// `cached_midstate` is the FIPS 205 SHA-2 layout with the PK.seed midstate
/// cached; without it every call pays for its full input.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Convention {
    pub cached_midstate: bool,
}

impl Default for Convention {
    fn default() -> Self {
        Self { cached_midstate: true }
    }
}

impl Convention {
    /// PK.seed + ADRS + one n-byte value.
    pub const fn th1(self) -> u64 {
        1
    }
    /// ... and the 4-byte WOTS+C counter.
    pub const fn th1c(self) -> u64 {
        1
    }
    /// Two n-byte children.
    pub const fn th2(self) -> u64 {
        if self.cached_midstate { 1 } else { 2 }
    }
    /// PK.seed + PK.root + R + message digest.
    pub const fn hmsg(self) -> u64 {
        2
    }
    /// SK.prf + opt + message.
    pub const fn prfmsg(self) -> u64 {
        2
    }
    /// PK.seed + SK.seed + ADRS.
    pub const fn prf(self) -> u64 {
        1
    }
    /// Compressions for a tweakable hash over `m` n-byte values.
    pub const fn th(self, m: u64, n: u64) -> u64 {
        let prefix = if self.cached_midstate { 22 * 8 } else { 8 * (n + 12) };
        (prefix + 8 * n * m + 65).div_ceil(512)
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

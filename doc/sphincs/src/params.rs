//! One parameter set, and the costs it implies.

use crate::cost::{COUNTER_BYTES, Convention, Cost, Encoding, NuTable, Scheme};

/// A SPHINCS+ parameter set. `q_s` is not part of it: see [`crate::security`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Params {
    pub scheme: Scheme,
    /// Hypertree height, a multiple of `d`.
    pub h: u64,
    /// Hypertree layers, so each XMSS tree has height `h' = h/d`.
    pub d: u64,
    /// FORS trees have `2^a` leaves.
    pub a: u64,
    /// Number of FORS trees.
    pub k: u64,
    /// Winternitz parameter, a power of two.
    pub w: u64,
    /// Hash output in bytes.
    pub n: u64,
    /// Chains dropped beyond the digest bits that have to be pinned anyway.
    pub dropped_chains: u64,
    /// Height above the leaves of the cached top-tree level; `None` is `h'/2`.
    pub cache_height: Option<u64>,
    /// Cache one level rather than it and everything above.
    pub cache_level_only: bool,
    pub convention: Convention,
}

impl Params {
    pub fn h_prime(&self) -> u64 {
        self.h / self.d
    }

    pub fn encoding(&self) -> Option<Encoding> {
        Encoding::new(self.w, self.n, self.dropped_chains)
    }

    /// Chains actually signed: `l1 + l2` for WOTS-TW, the encoding's for WOTS+C.
    pub fn chains(&self) -> Option<u64> {
        let enc = self.encoding()?;
        if self.scheme.wots_c() {
            return Some(enc.chains);
        }
        // WOTS-TW pads the digest to whole digits and appends a checksum
        // (FIPS 205): l1 = ceil(8n / log2 w), l2 = floor(log_w(l1*(w-1))) + 1.
        let l1 = (8 * self.n).div_ceil(enc.chain_bits);
        Some(l1 + self.wots_tw_len2(l1))
    }

    fn wots_tw_len2(&self, l1: u64) -> u64 {
        let bits = self.encoding().expect("checked by the caller").chain_bits;
        let c = l1 * (self.w - 1);
        // floor(log2(c) / log2(w)) + 1, integer-only
        (c.ilog2() as u64) / bits + 1
    }

    /// Verifier chain steps for WOTS-TW when every message digit is zero.
    fn wots_tw_worst_steps(&self) -> u64 {
        let enc = self.encoding().expect("checked by the caller");
        let l1 = (8 * self.n).div_ceil(enc.chain_bits);
        let l2 = self.wots_tw_len2(l1);
        let c = l1 * (self.w - 1);
        let digit_sum: u64 = {
            let mut rem = c;
            let mut sum = 0;
            while rem > 0 {
                sum += rem % self.w;
                rem /= self.w;
            }
            sum
        };
        l1 * (self.w - 1) + l2 * (self.w - 1) - digit_sum
    }
}

/// Everything about a parameter set that does not depend on the target sum.
///
/// Split this way so a search can reject a candidate on size, keygen, or the
/// least grinding any target sum could ask for, without pretending to know
/// where the good target sums are.
#[derive(Clone, Debug)]
pub struct Skeleton {
    pub params: Params,
    pub l: u64,
    pub chain_bits: u64,
    pub pinned_bits: u64,
    pub max_swn: u64,
    pub default_swn: u64,
    pub sig_bytes: u64,
    pub keygen: Cost,
    pub cache_bytes: u64,
    pub cache_depth: u64,
    pub fors_c_grinding: u64,
    /// Signing, less the WOTS+C counter grinding.
    sign_base: Cost,
    /// The same with the top tree's cached part rebuilt instead of the whole tree.
    sign_cached_base: Cost,
    /// One counter trial, at one layer.
    grind_step: Cost,
    /// Verification, less the chain walk that the target sum shortens.
    verify_base: Cost,
    /// One chain step, across all layers.
    verify_step: Cost,
    /// WOTS-TW only; for WOTS+C verification is deterministic.
    verify_worst_extra: Cost,
}

impl Skeleton {
    /// `None` if the parameters are not self-consistent (`d` must divide `h`,
    /// `w` must be a power of two, FORS+C needs `k >= 2`).
    pub fn new(p: Params) -> Option<Self> {
        if p.h == 0 || p.d == 0 || !p.h.is_multiple_of(p.d) || p.k < 1 || p.a < 1 {
            return None;
        }
        if p.scheme.fors_c() && p.k < 2 {
            return None;
        }
        if !p.scheme.wots_c() && p.dropped_chains > 0 {
            return None; // WOTS-TW has no counter to grind
        }
        // A tree of 2^64 leaves does not fit a u64 count, and could not be
        // generated under any budget expressible in one either: keygen alone is
        // at least 2^h' hashes, and one FORS tree at least 2^a.
        if p.h_prime() > 63 || p.a > 63 {
            return None;
        }
        let enc = p.encoding()?;
        let l = p.chains()?;
        let (n, cv, d, hp) = (p.n, p.convention, p.d, p.h_prime());
        let trees = p.scheme.trees(p.k);
        let t = 1u64 << p.a;

        // ---- size ----------------------------------------------------------
        let layer = hp * n + l * n + if p.scheme.wots_c() { COUNTER_BYTES } else { 0 };
        let sig_bytes = n + d * layer + trees * n + trees * p.a * n;

        // ---- one WOTS key pair, and one XMSS tree over 2^x of them ---------
        let leaf = Cost::new(
            l + l * (p.w - 1) + 1,
            l * cv.prf() + l * (p.w - 1) * cv.th1() + cv.th(l, n),
        );
        let tree = |leaves: u64| leaf * leaves + Cost::new(leaves - 1, (leaves - 1) * cv.th2());
        let top_tree = tree(1 << hp);

        // ---- signing -------------------------------------------------------
        let msg_hash = Cost::new(2, cv.hmsg() + cv.prfmsg());
        let fors_build = Cost::new(
            trees * t + trees * t + trees * (t - 1) + 1,
            trees * t * cv.prf() + trees * t * cv.th1() + trees * (t - 1) * cv.th2() + cv.th(trees, n),
        );
        // FORS+C grinds the digest until its last a bits vanish, so the last
        // FORS tree always opens leaf 0 and needs no authentication path.
        let fors_grind = if p.scheme.fors_c() { msg_hash * t } else { msg_hash };
        let sign_base = top_tree * d + fors_build + fors_grind;

        // ---- signing with the top tree's half top cached -------------------
        // Only the top tree is worth caching: it is the same for every
        // signature, while the trees below it are picked by the (pseudorandom)
        // index. Its auth path splits at the cached level: below, rebuild the
        // 2^c-leaf subtree the signing leaf sits in; above, the nodes are
        // already in state. Rebuilt leaves are charged a full WOTS public key,
        // as everywhere else here.
        //
        // A BDS-style traversal would amortize a tree to h' leaves per
        // signature with O(h') state, but it only works walking the leaves in
        // order. SPHINCS+ picks its index by hashing the message, so
        // consecutive signatures land on unrelated leaves and nothing
        // amortizes; an index-independent cache like this one is what is left,
        // hence sqrt rather than h'.
        let c = p.cache_height.unwrap_or(hp / 2);
        if c > hp {
            return None;
        }
        let stored_level = 1u64 << (hp - c);
        let mut cached_tree = tree(1 << c);
        let cache_bytes;
        if p.cache_level_only {
            cached_tree = cached_tree + Cost::new(stored_level - 1, (stored_level - 1) * cv.th2());
            cache_bytes = stored_level * n;
        } else {
            cache_bytes = (2 * stored_level - 1) * n;
        }
        let sign_cached_base = sign_base - top_tree + cached_tree;

        // ---- verification --------------------------------------------------
        let fors_verify = Cost::new(
            trees + trees * p.a + 1,
            trees * cv.th1() + trees * p.a * cv.th2() + cv.th(trees, n),
        );
        let auth = Cost::new(p.h, p.h * cv.th2());
        let mut verify_base = Cost::new(1, cv.hmsg()) + fors_verify + auth;
        let mut verify_step = Cost::default();
        let mut verify_worst_extra = Cost::default();
        if p.scheme.wots_c() {
            // the digits sum to S_wn, so the remaining chain steps are fixed at
            // (w-1)*l - S_wn, and the counter has to be hashed once per layer
            verify_base = verify_base + Cost::new(2, cv.th1c() + cv.th(l, n)) * d;
            verify_step = Cost::new(1, cv.th1()) * d;
        } else {
            let avg = (p.w - 1) * l / 2;
            verify_base = verify_base + Cost::new(avg + 1, avg * cv.th1() + cv.th(l, n)) * d;
            let worst = p.wots_tw_worst_steps();
            verify_worst_extra = Cost::new(worst - avg, (worst - avg) * cv.th1()) * d;
        }

        Some(Self {
            params: p,
            l,
            chain_bits: enc.chain_bits,
            pinned_bits: if p.scheme.wots_c() { enc.pinned_bits } else { 0 },
            max_swn: (p.w - 1) * l,
            default_swn: if p.scheme.wots_c() { enc.default_swn() } else { 0 },
            sig_bytes,
            keygen: top_tree,
            cache_bytes,
            cache_depth: hp - c,
            fors_c_grinding: if p.scheme.fors_c() { fors_grind.hashes } else { 0 },
            sign_base,
            sign_cached_base,
            grind_step: Cost::new(1, p.convention.th1c()),
            verify_base,
            verify_step,
            verify_worst_extra,
        })
    }

    /// Expected signing cost when each layer grinds `trials` counters.
    pub fn sign(&self, trials: u64) -> Cost {
        self.sign_base + self.grind_step * trials.saturating_mul(self.params.d)
    }

    /// The same with the top tree's half top cached.
    pub fn sign_cached(&self, trials: u64) -> Cost {
        self.sign_cached_base + self.grind_step * trials.saturating_mul(self.params.d)
    }

    /// Verification at this target sum. `swn` is ignored for WOTS-TW.
    pub fn verify(&self, swn: u64) -> Cost {
        self.verify_base + self.verify_step * (self.max_swn - swn.min(self.max_swn))
    }

    /// Verification when every message digit is zero (WOTS-TW only).
    pub fn verify_worst(&self, swn: u64) -> Cost {
        self.verify(swn) + self.verify_worst_extra
    }

    /// The full picture at one target sum.
    pub fn finish(&self, swn: u64, trials: u64) -> Costs {
        Costs {
            l: self.l,
            chain_bits: self.chain_bits,
            pinned_bits: self.pinned_bits,
            dropped_chains: self.params.dropped_chains,
            swn: self.params.scheme.wots_c().then_some(swn),
            sig_bytes: self.sig_bytes,
            keygen: self.keygen,
            sign: self.sign(trials),
            sign_cached: self.sign_cached(trials),
            verify: self.verify(swn),
            verify_worst: self.verify_worst(swn),
            wots_c_grinding: trials.saturating_mul(self.params.d),
            fors_c_grinding: self.fors_c_grinding,
            cache_depth: self.cache_depth,
            cache_bytes: self.cache_bytes,
        }
    }

    /// The full picture at the mean target sum, the report's default.
    pub fn at_default_swn(&self, nu: Option<&NuTable>) -> Costs {
        let swn = self.default_swn;
        let trials = nu.map_or(0, |t| t.trials(swn));
        self.finish(swn, trials)
    }
}

/// Every cost of a parameter set at one target sum.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Costs {
    pub l: u64,
    pub chain_bits: u64,
    pub pinned_bits: u64,
    pub dropped_chains: u64,
    pub swn: Option<u64>,
    pub sig_bytes: u64,
    pub keygen: Cost,
    pub sign: Cost,
    pub sign_cached: Cost,
    pub verify: Cost,
    pub verify_worst: Cost,
    pub wots_c_grinding: u64,
    pub fors_c_grinding: u64,
    pub cache_depth: u64,
    pub cache_bytes: u64,
}

impl Costs {
    pub fn grinding(&self) -> u64 {
        self.wots_c_grinding + self.fors_c_grinding
    }
}

/// Costs of one parameter set, building the digit-sum table as needed.
///
/// Convenient for a single evaluation; a search should hold the [`NuTable`] and
/// drive [`Skeleton`] itself, since the table depends only on `(l, w)`.
pub fn costs(p: Params, swn: Option<u64>) -> Option<Costs> {
    let sk = Skeleton::new(p)?;
    if !p.scheme.wots_c() {
        return Some(sk.finish(0, 0));
    }
    let table = NuTable::new(sk.l, p.w, (8 * p.n) as u32);
    let swn = swn.unwrap_or(sk.default_swn);
    Some(sk.finish(swn, table.trials(swn)))
}

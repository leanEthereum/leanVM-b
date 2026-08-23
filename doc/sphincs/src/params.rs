//! One parameter set, and the costs it implies.

use crate::cost::{COUNTER_BYTES, Convention, Cost, Encoding, NuTable, Scheme};

/// A SPHINCS+ parameter set. `q_s` is not part of it: see [`crate::security`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Params {
    pub scheme: Scheme,
    /// Total hypertree height, the sum of the layer heights.
    pub h: u64,
    /// Hypertree layers.
    pub d: u64,
    /// Height of the top XMSS tree. `None` spreads `h` as evenly as it goes,
    /// which for `d | h` is the classic `h' = h/d` on every layer.
    pub h_top: Option<u64>,
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
    /// Height above the leaves of the cached top-tree level; `None` is half of it.
    pub cache_height: Option<u64>,
    /// Cache one level rather than it and everything above.
    pub cache_level_only: bool,
    pub convention: Convention,
}

/// The height of every XMSS tree in the hypertree.
///
/// Only the top tree is worth caching, and the layers below it are otherwise
/// interchangeable, so the only profile shape worth considering is "the top one,
/// then the rest as equal as they go". For a fixed `(h, d, h_top)` that shape is
/// no worse than any other on every cost: size and verification depend only on
/// `(h, d)`, keygen only on `h_top`, and signing sums `2^height` over the
/// layers, which for a fixed total is smallest when they are equal. So
/// enumerating `(h, d, h_top)` covers the cost-optimal representative of every
/// layer profile, and the `d - 1` lower heights differ by at most one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Profile {
    pub h_top: u64,
    /// The taller of the two lower heights, and how many layers have it.
    pub tall: u64,
    pub n_tall: u64,
    /// The shorter of the two, and how many layers have it.
    pub short: u64,
    pub n_short: u64,
}

impl Profile {
    /// `None` if some layer would be empty, or too tall for `2^height` to count.
    pub fn new(h: u64, d: u64, h_top: Option<u64>) -> Option<Self> {
        if d == 0 || h == 0 {
            return None;
        }
        let h_top = h_top.unwrap_or(h / d).max(1);
        let lower_total = h.checked_sub(h_top)?;
        let m = d - 1;
        if m == 0 {
            if lower_total != 0 {
                return None; // one layer has to be the whole height
            }
            return Self::checked(Self {
                h_top,
                tall: 0,
                n_tall: 0,
                short: 0,
                n_short: 0,
            });
        }
        if lower_total < m {
            return None; // every layer needs at least one level
        }
        let (q, r) = (lower_total / m, lower_total % m);
        Self::checked(Self {
            h_top,
            tall: q + 1,
            n_tall: r,
            short: q,
            n_short: m - r,
        })
    }

    /// A tree of `2^63` leaves is already past any budget a `u64` can hold, and
    /// `2^64` does not fit the count at all.
    fn checked(self) -> Option<Self> {
        (self.h_top <= 63 && self.tall <= 63).then_some(self)
    }

    pub fn total(&self) -> u64 {
        self.h_top + self.tall * self.n_tall + self.short * self.n_short
    }

    pub fn layers(&self) -> u64 {
        1 + self.n_tall + self.n_short
    }

    /// Is every layer the same height?
    pub fn uniform(&self) -> bool {
        (self.n_tall == 0 || self.tall == self.h_top) && (self.n_short == 0 || self.short == self.h_top)
    }
}

impl std::fmt::Display for Profile {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.uniform() {
            return write!(f, "{} x {}", self.layers(), self.h_top);
        }
        write!(f, "top {}", self.h_top)?;
        for (height, count) in [(self.tall, self.n_tall), (self.short, self.n_short)] {
            if count > 0 {
                write!(f, " + {count} x {height}")?;
            }
        }
        Ok(())
    }
}

impl Params {
    pub fn profile(&self) -> Option<Profile> {
        Profile::new(self.h, self.d, self.h_top)
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
        (l1 * (self.w - 1)).ilog2() as u64 / bits + 1
    }

    /// Verifier chain steps for WOTS-TW when every message digit is zero.
    fn wots_tw_worst_steps(&self) -> u64 {
        let enc = self.encoding().expect("checked by the caller");
        let l1 = (8 * self.n).div_ceil(enc.chain_bits);
        let l2 = self.wots_tw_len2(l1);
        let c = l1 * (self.w - 1);
        let digit_sum: u64 = {
            let (mut rem, mut sum) = (c, 0);
            while rem > 0 {
                sum += rem % self.w;
                rem /= self.w;
            }
            sum
        };
        l1 * (self.w - 1) + l2 * (self.w - 1) - digit_sum
    }

    /// One WOTS key pair, plus the compression of its `l` chain ends into a leaf.
    fn wots_leaf(&self, l: u64) -> Cost {
        let cv = self.convention;
        Cost::new(
            l + l * (self.w - 1) + 1,
            l * cv.prf() + l * (self.w - 1) * cv.th1() + cv.th(l, self.n),
        )
    }
}

/// The hypertree side: what the layer heights cost, at any `(a, k)` and any
/// target sum.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Layers {
    pub profile: Profile,
    /// Generating the top tree, which is all key generation does.
    pub keygen: Cost,
    /// Regrowing every layer, which is what signing does.
    pub trees: Cost,
    /// The same with the top tree's half top already in state.
    pub trees_cached: Cost,
    pub cache_bytes: u64,
    pub cache_depth: u64,
}

impl Layers {
    pub fn new(p: &Params) -> Option<Self> {
        let profile = p.profile()?;
        let l = p.chains()?;
        let leaf = p.wots_leaf(l);
        let cv = p.convention;
        let tree = |height: u64| {
            let leaves = 1u64 << height;
            leaf * leaves + Cost::new(leaves - 1, (leaves - 1) * cv.th2())
        };
        let top = tree(profile.h_top);
        let lower = tree(profile.tall) * profile.n_tall + tree(profile.short) * profile.n_short;

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
        let c = p.cache_height.unwrap_or(profile.h_top / 2);
        if c > profile.h_top {
            return None;
        }
        let stored_level = 1u64 << (profile.h_top - c);
        let mut cached = tree(c);
        let cache_bytes;
        if p.cache_level_only {
            cached = cached + Cost::new(stored_level - 1, (stored_level - 1) * cv.th2());
            cache_bytes = stored_level * p.n;
        } else {
            cache_bytes = (2 * stored_level - 1) * p.n;
        }

        Some(Self {
            profile,
            keygen: top,
            trees: top + lower,
            trees_cached: cached + lower,
            cache_bytes,
            cache_depth: profile.h_top - c,
        })
    }
}

/// Everything else: the FORS side, the signature size and the verifier, none of
/// which depends on how the hypertree's height is split between its layers.
///
/// Split from [`Layers`] and from the target sum so that a search can reject a
/// candidate on size, or on the least any layer profile and any target sum could
/// cost, without pretending to know which of those are good.
#[derive(Clone, Debug)]
pub struct Skeleton {
    pub params: Params,
    pub l: u64,
    pub chain_bits: u64,
    pub pinned_bits: u64,
    pub max_swn: u64,
    pub default_swn: u64,
    pub sig_bytes: u64,
    pub fors_c_grinding: u64,
    /// The `(a, k)` part of signing: growing the FORS trees, and any grinding
    /// FORS+C does. Common to both signing costs, cached or not.
    pub fors_part: Cost,
    /// One counter trial, at one layer.
    pub grind_step: Cost,
    /// Verification, less the chain walk that the target sum shortens.
    verify_base: Cost,
    /// One chain step, across all layers.
    verify_step: Cost,
    /// WOTS-TW only; for WOTS+C verification is deterministic.
    verify_worst_extra: Cost,
}

impl Skeleton {
    /// `None` if the parameters are not self-consistent: `w` must be a power of
    /// two, FORS+C needs `k >= 2`, WOTS-TW cannot drop chains, and `2^a` has to
    /// be countable.
    pub fn new(p: Params) -> Option<Self> {
        if p.k < 1 || p.a < 1 || p.a > 63 || p.d == 0 {
            return None;
        }
        if p.scheme.fors_c() && p.k < 2 {
            return None;
        }
        if !p.scheme.wots_c() && p.dropped_chains > 0 {
            return None;
        }
        let enc = p.encoding()?;
        let l = p.chains()?;
        let profile = p.profile()?;
        let (n, cv, d) = (p.n, p.convention, p.d);
        let trees = p.scheme.trees(p.k);
        let t = 1u64 << p.a;

        // The signature carries the whole authentication path, h nodes however
        // the layers divide it, plus one WOTS signature per layer.
        let layer = l * n + if p.scheme.wots_c() { COUNTER_BYTES } else { 0 };
        let sig_bytes = n + profile.total() * n + d * layer + trees * n + trees * p.a * n;

        let msg_hash = Cost::new(2, cv.hmsg() + cv.prfmsg());
        let fors_build = Cost::new(
            trees * t + trees * t + trees * (t - 1) + 1,
            trees * t * cv.prf() + trees * t * cv.th1() + trees * (t - 1) * cv.th2() + cv.th(trees, n),
        );
        // FORS+C grinds the digest until its last a bits vanish, so the last
        // FORS tree always opens leaf 0 and needs no authentication path.
        let fors_grind = if p.scheme.fors_c() { msg_hash * t } else { msg_hash };

        let fors_verify = Cost::new(
            trees + trees * p.a + 1,
            trees * cv.th1() + trees * p.a * cv.th2() + cv.th(trees, n),
        );
        let auth = Cost::new(profile.total(), profile.total() * cv.th2());
        let mut verify_base = Cost::new(1, cv.hmsg()) + fors_verify + auth;
        let mut verify_step = Cost::default();
        let mut verify_worst_extra = Cost::default();
        if p.scheme.wots_c() {
            // the digits sum to S_wn, so the remaining chain steps are fixed at
            // (w-1)*l - S_wn, and the counter is hashed once per layer
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
            fors_c_grinding: if p.scheme.fors_c() { fors_grind.hashes } else { 0 },
            fors_part: fors_build + fors_grind,
            grind_step: Cost::new(1, cv.th1c()),
            verify_base,
            verify_step,
            verify_worst_extra,
        })
    }

    /// Expected signing cost when each layer grinds `trials` counters.
    pub fn sign(&self, lay: &Layers, trials: u64) -> Cost {
        lay.trees + self.fors_part + self.grinding(trials)
    }

    /// The same with the top tree's half top cached.
    pub fn sign_cached(&self, lay: &Layers, trials: u64) -> Cost {
        lay.trees_cached + self.fors_part + self.grinding(trials)
    }

    /// What `trials` counter values per layer cost across the hypertree.
    pub fn grinding(&self, trials: u64) -> Cost {
        self.grind_step * trials.saturating_mul(self.params.d)
    }

    /// Verification at this target sum. `swn` is ignored for WOTS-TW.
    pub fn verify(&self, swn: u64) -> Cost {
        self.verify_base + self.verify_step * (self.max_swn - swn.min(self.max_swn))
    }

    /// Verification when every message digit is zero (WOTS-TW only).
    pub fn verify_worst(&self, swn: u64) -> Cost {
        self.verify(swn) + self.verify_worst_extra
    }

    /// The full picture at one layer profile and one target sum.
    pub fn finish(&self, lay: &Layers, swn: u64, trials: u64) -> Costs {
        Costs {
            l: self.l,
            chain_bits: self.chain_bits,
            pinned_bits: self.pinned_bits,
            dropped_chains: self.params.dropped_chains,
            swn: self.params.scheme.wots_c().then_some(swn),
            profile: lay.profile,
            sig_bytes: self.sig_bytes,
            keygen: lay.keygen,
            sign: self.sign(lay, trials),
            sign_cached: self.sign_cached(lay, trials),
            verify: self.verify(swn),
            verify_worst: self.verify_worst(swn),
            wots_c_grinding: trials.saturating_mul(self.params.d),
            fors_c_grinding: self.fors_c_grinding,
            cache_depth: lay.cache_depth,
            cache_bytes: lay.cache_bytes,
        }
    }
}

/// Every cost of a parameter set at one layer profile and one target sum.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Costs {
    pub l: u64,
    pub chain_bits: u64,
    pub pinned_bits: u64,
    pub dropped_chains: u64,
    pub swn: Option<u64>,
    pub profile: Profile,
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
/// drive [`Skeleton`] and [`Layers`] itself, since the table depends only on
/// `(l, w)` and the layer costs only on the profile.
pub fn costs(p: Params, swn: Option<u64>) -> Option<Costs> {
    let sk = Skeleton::new(p)?;
    let lay = Layers::new(&p)?;
    if !p.scheme.wots_c() {
        return Some(sk.finish(&lay, 0, 0));
    }
    let table = NuTable::new(sk.l, p.w, (8 * p.n) as u32);
    let swn = swn.unwrap_or(sk.default_swn);
    Some(sk.finish(&lay, swn, table.trials(swn)))
}

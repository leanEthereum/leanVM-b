//! One parameter set, and the costs it implies.

use crate::cost::{Blocks, COUNTER_BYTES, Cost, Encoding, NuTable, Scheme};

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
}

/// The height of every XMSS tree in the hypertree, top first.
///
/// Any heights are expressible, but a search only ever needs
/// [`Profile::canonical`]: the top tree at some height and the rest dividing
/// what is left as evenly as it goes. For a fixed `(h, d, h_top)` that shape is
/// no worse than any other on every cost, since size and verification depend
/// only on `(h, d)`, keygen only on `h_top`, and signing sums `2^height` over
/// the layers, which at a fixed total is smallest when they are equal. So
/// enumerating `(h, d, h_top)` covers the cost-optimal representative of every
/// profile. `profile_shape_is_never_beaten` in `tests/goldens` checks that
/// against every composition of a few small `(h, d)`.
///
/// Only the heights vary per layer: every layer signs with the same WOTS
/// parameters. Giving each its own `w`, target sum and dropped chain count was
/// implemented and reverted, because it never won. Size charges every layer the
/// same `l * n` and verification charges every layer its own walk, so the
/// exchange rate between them is identical everywhere, and the walk
/// `(2^(8n/l) - 1) * l` is convex in `l`, so at a fixed total `l` an equal split
/// is what a size budget wants. Only signing distinguishes the layers, a tall
/// tree wanting cheap leaves, so it pays only where the signing budget binds and
/// the heights are uneven; searched there, the uniform choice still won, the
/// per-layer target sums differing by one step. The reverted commit carries the
/// working code and the reasoning, including why a search would never need more
/// than two distinct WOTS instances.
///
/// Heights are at most 63, since `2^height` has to be countable, and there are
/// at most [`MAX_LAYERS`] of them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Profile {
    heights: [u8; MAX_LAYERS],
    len: u8,
}

/// The most hypertree layers a [`Profile`] can hold.
pub const MAX_LAYERS: usize = 32;

impl Profile {
    /// Any heights at all, the top tree first.
    pub fn new(heights: &[u64]) -> Option<Self> {
        if heights.is_empty() || heights.len() > MAX_LAYERS || heights.iter().any(|&x| !(1..=63).contains(&x)) {
            return None;
        }
        let mut out = Self {
            heights: [0; MAX_LAYERS],
            len: heights.len() as u8,
        };
        for (slot, &h) in out.heights.iter_mut().zip(heights) {
            *slot = h as u8;
        }
        Some(out)
    }

    /// The top tree at `h_top`, the other `d - 1` layers dividing `h - h_top` as
    /// evenly as it goes. `None` for `h_top` is the classic `h/d` split.
    pub fn canonical(h: u64, d: u64, h_top: Option<u64>) -> Option<Self> {
        if d == 0 || d as usize > MAX_LAYERS || h == 0 {
            return None;
        }
        let h_top = h_top.unwrap_or(h / d).max(1);
        let lower_total = h.checked_sub(h_top)?;
        let m = d - 1;
        if m == 0 {
            return (lower_total == 0).then(|| Self::new(&[h_top]))?;
        }
        if lower_total < m {
            return None; // every layer needs at least one level
        }
        let (q, r) = (lower_total / m, lower_total % m);
        let mut heights = vec![h_top];
        heights.extend(std::iter::repeat_n(q + 1, r as usize));
        heights.extend(std::iter::repeat_n(q, (m - r) as usize));
        Self::new(&heights)
    }

    pub fn heights(&self) -> impl Iterator<Item = u64> + '_ {
        self.heights[..self.len as usize].iter().map(|&x| x as u64)
    }

    /// The top tree's height: the one layer that is the same for every signature.
    pub fn h_top(&self) -> u64 {
        self.heights().next().unwrap_or(0)
    }

    pub fn total(&self) -> u64 {
        self.heights().sum()
    }

    pub fn layers(&self) -> u64 {
        self.len as u64
    }

    pub fn uniform(&self) -> bool {
        self.heights().all(|x| x == self.h_top())
    }
}

impl std::fmt::Display for Profile {
    /// Every height, top first: `12 + 7 + 7`.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let listed: Vec<String> = self.heights().map(|h| h.to_string()).collect();
        write!(f, "{}", listed.join(" + "))
    }
}

impl Params {
    pub fn profile(&self) -> Option<Profile> {
        Profile::canonical(self.h, self.d, self.h_top)
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

    /// The compression counts of the hashes this parameter set uses.
    pub fn blocks(&self) -> Blocks {
        Blocks::new(self.n)
    }

    /// One WOTS key pair, plus the compression of its `l` chain ends into a leaf.
    fn wots_leaf(&self, l: u64) -> Cost {
        let b = self.blocks();
        Cost::new(
            l + l * (self.w - 1) + 1,
            l * b.prf() + l * (self.w - 1) * b.chain_step() + b.compress(l),
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
    /// The canonical profile of `p`: see [`Profile::canonical`].
    pub fn new(p: &Params) -> Option<Self> {
        Self::from_profile(p, p.profile()?)
    }

    /// Any profile, as long as its heights add up to `p.h` over `p.d` layers.
    pub fn from_profile(p: &Params, profile: Profile) -> Option<Self> {
        if profile.total() != p.h || profile.layers() != p.d {
            return None;
        }
        let l = p.chains()?;
        let leaf = p.wots_leaf(l);
        let b = p.blocks();
        let tree = |height: u64| {
            let leaves = 1u64 << height;
            leaf * leaves + Cost::new(leaves - 1, (leaves - 1) * b.merkle_node())
        };
        let top = tree(profile.h_top());
        let lower = profile
            .heights()
            .skip(1)
            .map(tree)
            .fold(Cost::default(), |acc, x| acc + x);

        // Only the top tree is worth caching: it is the same for every
        // signature, while the trees below it are picked by the (pseudorandom)
        // index. Its auth path splits at the cached level: below, rebuild the
        // 2^c-leaf subtree the signing leaf sits in; above, refold the stored
        // level. Rebuilt leaves are charged a full WOTS public key, as
        // everywhere else here.
        //
        // A BDS-style traversal would amortize a tree to h' leaves per
        // signature with O(h') state, but it only works walking the leaves in
        // order. SPHINCS+ picks its index by hashing the message, so
        // consecutive signatures land on unrelated leaves and nothing
        // amortizes; an index-independent cache like this one is what is left,
        // hence sqrt rather than h'.
        let c = p.cache_height.unwrap_or(profile.h_top() / 2);
        if c > profile.h_top() {
            return None;
        }
        // Only the level itself is stored, not the triangle above it: refolding
        // that is 2^(h-c)-1 node calls, nothing next to the subtree rebuild,
        // while storing it would double the bytes.
        let stored_level = 1u64 << (profile.h_top() - c);
        let cached = tree(c) + Cost::new(stored_level - 1, (stored_level - 1) * b.merkle_node());
        let cache_bytes = stored_level * p.n;

        Some(Self {
            profile,
            keygen: top,
            trees: top + lower,
            trees_cached: cached + lower,
            cache_bytes,
            cache_depth: profile.h_top() - c,
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
    /// What FORS+C's digest grinding costs, zero for the other schemes.
    pub fors_c_grinding: Cost,
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
        let (n, b, d) = (p.n, p.blocks(), p.d);
        let trees = p.scheme.trees(p.k);
        let t = 1u64 << p.a;

        // The signature carries the whole authentication path, h nodes however
        // the layers divide it, plus one WOTS signature per layer.
        let layer = l * n + if p.scheme.wots_c() { COUNTER_BYTES } else { 0 };
        let sig_bytes = n + profile.total() * n + d * layer + trees * n + trees * p.a * n;

        let msg_hash = Cost::new(2, b.message_hash() + b.message_prf());
        let fors_build = Cost::new(
            trees * t + trees * t + trees * (t - 1) + 1,
            trees * t * b.prf() + trees * t * b.chain_step() + trees * (t - 1) * b.merkle_node() + b.compress(trees),
        );
        // FORS+C grinds the digest until its last a bits vanish, so the last
        // FORS tree always opens leaf 0 and needs no authentication path.
        let fors_grind = if p.scheme.fors_c() { msg_hash * t } else { msg_hash };

        let fors_verify = Cost::new(
            trees + trees * p.a + 1,
            trees * b.chain_step() + trees * p.a * b.merkle_node() + b.compress(trees),
        );
        let auth = Cost::new(profile.total(), profile.total() * b.merkle_node());
        let mut verify_base = Cost::new(1, b.message_hash()) + fors_verify + auth;
        let mut verify_step = Cost::default();
        let mut verify_worst_extra = Cost::default();
        if p.scheme.wots_c() {
            // the digits sum to S_wn, so the remaining chain steps are fixed at
            // (w-1)*l - S_wn, and the counter is hashed once per layer
            verify_base = verify_base + Cost::new(2, b.chain_step_with_counter() + b.compress(l)) * d;
            verify_step = Cost::new(1, b.chain_step()) * d;
        } else {
            let avg = (p.w - 1) * l / 2;
            verify_base = verify_base + Cost::new(avg + 1, avg * b.chain_step() + b.compress(l)) * d;
            let worst = p.wots_tw_worst_steps();
            verify_worst_extra = Cost::new(worst - avg, (worst - avg) * b.chain_step()) * d;
        }

        Some(Self {
            params: p,
            l,
            chain_bits: enc.chain_bits,
            pinned_bits: if p.scheme.wots_c() { enc.pinned_bits } else { 0 },
            max_swn: (p.w - 1) * l,
            default_swn: if p.scheme.wots_c() { enc.default_swn() } else { 0 },
            sig_bytes,
            fors_c_grinding: if p.scheme.fors_c() { fors_grind } else { Cost::default() },
            fors_part: fors_build + fors_grind,
            grind_step: Cost::new(1, b.chain_step_with_counter()),
            verify_base,
            verify_step,
            verify_worst_extra,
        })
    }

    /// Expected signing cost, with the top tree's half top in state, when each
    /// layer grinds `trials` counters.
    pub fn sign(&self, lay: &Layers, trials: u64) -> Cost {
        lay.trees_cached + self.fors_part + self.grinding(trials)
    }

    /// The same for a signer holding no state at all, which has to rebuild the
    /// top tree along with the rest.
    pub fn sign_cold(&self, lay: &Layers, trials: u64) -> Cost {
        lay.trees + self.fors_part + self.grinding(trials)
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
            sign_cold: self.sign_cold(lay, trials),
            verify: self.verify(swn),
            verify_worst: self.verify_worst(swn),
            wots_c_grinding: self.grinding(trials),
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
    /// Signing with the top tree's half top in state, the cost a signer that
    /// keeps `cache_bytes` of it actually pays.
    pub sign: Cost,
    /// Signing with no state at all, every tree rebuilt from the seed. Not
    /// reported: a signer pays it once, after restoring a backup. It is the
    /// projection the upstream sage scripts compute, which have no cache
    /// notion, so `tests/goldens` checks their fixtures against it.
    pub sign_cold: Cost,
    pub verify: Cost,
    pub verify_worst: Cost,
    /// Searching for admissible WOTS+C counters, across every layer.
    pub wots_c_grinding: Cost,
    /// Grinding the digest so FORS+C's last tree opens leaf zero.
    pub fors_c_grinding: Cost,
    pub cache_depth: u64,
    pub cache_bytes: u64,
}

impl Costs {
    /// Everything the signer spends on grinding rather than on trees.
    pub fn grinding(&self) -> Cost {
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

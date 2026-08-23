//! One parameter set, and the costs it implies.
//!
//! A parameter set is a [`Params`] (the FORS side and the hash size) plus a
//! [`Hypertree`], which carries every layer's Merkle height and the WOTS
//! parameters signing into it. Nothing forces those to agree across layers, and
//! [`Layer`] documents what varying them buys.

use crate::cost::{Blocks, COUNTER_BYTES, Cost, Encoding, NuCache, NuTable, Scheme};

/// The most hypertree layers a [`Hypertree`] can hold.
pub const MAX_LAYERS: usize = 32;

/// `Layer::swn` when the target sum is the mean, where grinding is cheapest.
const SWN_MEAN: u32 = u32::MAX;

/// One hypertree layer: its Merkle height, and the WOTS instance whose keys sit
/// at its leaves and sign the layer below (the FORS root, at the bottom).
///
/// The layers need not agree. What that buys is narrow but real. Verification,
/// signature size and per-leaf signing work all move together with `w`: a
/// smaller `w` means more chains, so a bigger signature, but fewer chain steps
/// to walk and fewer to build. Size charges every layer the same `l * n`, and
/// verification charges every layer its own walk, so on those two the exchange
/// rate is identical everywhere and a uniform `w` is what a size budget wants:
/// the walk `(2^(8n/l) - 1) * l` is convex in `l`, so at a fixed total `l` an
/// equal split is cheapest.
///
/// Signing is where the layers differ, because a layer's tree costs
/// `2^height` leaves. A tall tree wants cheap leaves, so a small `w`, and a
/// short one can afford a large `w` to give its size back. So per-layer WOTS
/// pays exactly when the signing budget binds and the heights are uneven, which
/// is what a tight key generation budget produces.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Layer {
    height: u8,
    chain_bits: u8,
    dropped: u8,
    swn: u32,
}

impl Layer {
    /// `None` unless the height is countable, `w` is a power of two, and the
    /// target sum is reachable.
    pub fn new(height: u64, w: u64, dropped_chains: u64, swn: Option<u64>) -> Option<Self> {
        if !(1..=63).contains(&height) || w < 2 || !w.is_power_of_two() || dropped_chains > 255 {
            return None;
        }
        let swn = match swn {
            None => SWN_MEAN,
            Some(s) => u32::try_from(s).ok().filter(|&s| s != SWN_MEAN)?,
        };
        Some(Self {
            height: height as u8,
            chain_bits: w.trailing_zeros() as u8,
            dropped: dropped_chains as u8,
            swn,
        })
    }

    pub fn height(&self) -> u64 {
        self.height as u64
    }
    pub fn w(&self) -> u64 {
        1 << self.chain_bits
    }
    pub fn chain_bits(&self) -> u64 {
        self.chain_bits as u64
    }
    pub fn dropped_chains(&self) -> u64 {
        self.dropped as u64
    }
    /// The target digit sum, or `None` for the mean.
    pub fn swn(&self) -> Option<u64> {
        (self.swn != SWN_MEAN).then_some(self.swn as u64)
    }

    pub fn with_height(&self, height: u64) -> Option<Self> {
        Self::new(height, self.w(), self.dropped_chains(), self.swn())
    }
    pub fn with_swn(&self, swn: Option<u64>) -> Option<Self> {
        Self::new(self.height(), self.w(), self.dropped_chains(), swn)
    }

    pub fn encoding(&self, n: u64) -> Option<Encoding> {
        Encoding::new(self.w(), n, self.dropped_chains())
    }

    /// Chains actually signed: `l1 + l2` for WOTS-TW, the encoding's for WOTS+C.
    pub fn chains(&self, n: u64, scheme: Scheme) -> Option<u64> {
        let enc = self.encoding(n)?;
        if scheme.wots_c() {
            return Some(enc.chains);
        }
        // WOTS-TW pads the digest to whole digits and appends a checksum
        // (FIPS 205): l1 = ceil(8n / log2 w), l2 = floor(log_w(l1*(w-1))) + 1.
        let l1 = (8 * n).div_ceil(enc.chain_bits);
        Some(l1 + self.wots_tw_len2(l1, n))
    }

    fn wots_tw_len2(&self, l1: u64, n: u64) -> u64 {
        let _ = n;
        (l1 * (self.w() - 1)).ilog2() as u64 / self.chain_bits() + 1
    }

    /// Verifier chain steps for WOTS-TW when every message digit is zero.
    fn wots_tw_worst_steps(&self, n: u64) -> u64 {
        let bits = self.chain_bits();
        let l1 = (8 * n).div_ceil(bits);
        let l2 = self.wots_tw_len2(l1, n);
        let (w, c) = (self.w(), l1 * (self.w() - 1));
        let digit_sum = {
            let (mut rem, mut sum) = (c, 0);
            while rem > 0 {
                sum += rem % w;
                rem /= w;
            }
            sum
        };
        l1 * (w - 1) + l2 * (w - 1) - digit_sum
    }
}

/// Every layer of the hypertree, top first.
///
/// Any heights and any WOTS parameters are expressible. A search need not try
/// them all: see [`Hypertree::two_group`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Hypertree {
    layers: [Layer; MAX_LAYERS],
    len: u8,
}

impl Hypertree {
    pub fn new(layers: &[Layer]) -> Option<Self> {
        if layers.is_empty() || layers.len() > MAX_LAYERS {
            return None;
        }
        let mut out = Self {
            layers: [layers[0]; MAX_LAYERS],
            len: layers.len() as u8,
        };
        out.layers[..layers.len()].copy_from_slice(layers);
        Some(out)
    }

    /// One WOTS instance for every layer, the top tree at `h_top` and the rest
    /// dividing `h - h_top` as evenly as it goes. `None` for `h_top` is the
    /// classic `h/d` split.
    pub fn uniform(h: u64, d: u64, h_top: Option<u64>, w: u64, dropped: u64, swn: Option<u64>) -> Option<Self> {
        let top = Layer::new(h_top.unwrap_or(h / d).max(1), w, dropped, swn)?;
        Self::two_group(h, d, top, top)
    }

    /// The top layer as given, every other layer sharing `low`'s WOTS
    /// parameters and dividing what is left of `h` as evenly as it goes.
    ///
    /// This is the only shape a search has to try. Any Lagrangian relaxation of
    /// the layer choice, `min sum_i [verify_i + L*size_i + M*sign_i]`, is
    /// separable and so returns each layer's own argmin; but every layer below
    /// the top has an identical cost function, since only the top tree is the
    /// cached one and only it is what keygen pays for. So at most two distinct
    /// choices come back, ties aside, and the ties are between neighbouring
    /// heights, which the split here already spans. `two_group_attains_the_optimum`
    /// in `tests/goldens` checks that against every per-layer assignment of
    /// small hypertrees.
    pub fn two_group(h: u64, d: u64, top: Layer, low: Layer) -> Option<Self> {
        if d == 0 || d as usize > MAX_LAYERS {
            return None;
        }
        let lower_total = h.checked_sub(top.height())?;
        let m = d - 1;
        if m == 0 {
            return (lower_total == 0).then(|| Self::new(&[top]))?;
        }
        if lower_total < m {
            return None; // every layer needs at least one level
        }
        let (q, r) = (lower_total / m, lower_total % m);
        let mut layers = vec![top];
        for i in 0..m {
            layers.push(low.with_height(if i < r { q + 1 } else { q })?);
        }
        Self::new(&layers)
    }

    pub fn layers(&self) -> impl Iterator<Item = Layer> + '_ {
        self.layers[..self.len as usize].iter().copied()
    }

    /// The one layer that is the same for every signature, and so the only one
    /// worth caching.
    pub fn top(&self) -> Layer {
        self.layers[0]
    }

    /// Total height, which is what the authentication path carries.
    pub fn height(&self) -> u64 {
        self.layers().map(|x| x.height()).sum()
    }

    pub fn depth(&self) -> u64 {
        self.len as u64
    }

    /// Do all layers share their WOTS parameters?
    pub fn one_wots(&self) -> bool {
        let top = self.top();
        self.layers()
            .all(|x| (x.w(), x.dropped_chains(), x.swn()) == (top.w(), top.dropped_chains(), top.swn()))
    }

    pub fn with_swn(&self, swn: Option<u64>) -> Option<Self> {
        let layers: Option<Vec<Layer>> = self.layers().map(|x| x.with_swn(swn)).collect();
        Self::new(&layers?)
    }

    /// Heights only: `12 + 7 + 7`.
    pub fn heights(&self) -> String {
        let listed: Vec<String> = self.layers().map(|x| x.height().to_string()).collect();
        listed.join(" + ")
    }
}

impl std::fmt::Display for Hypertree {
    /// The heights, and the WOTS parameters wherever the layers disagree.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.one_wots() {
            return write!(f, "{}", self.heights());
        }
        let listed: Vec<String> = self
            .layers()
            .map(|x| match (x.dropped_chains(), x.swn()) {
                (0, None) => format!("{}(w={})", x.height(), x.w()),
                (0, Some(s)) => format!("{}(w={},S={s})", x.height(), x.w()),
                (dr, None) => format!("{}(w={},-{dr})", x.height(), x.w()),
                (dr, Some(s)) => format!("{}(w={},S={s},-{dr})", x.height(), x.w()),
            })
            .collect();
        write!(f, "{}", listed.join(" + "))
    }
}

/// The FORS side of a parameter set, and the hash size. The hypertree is
/// separate: see [`Hypertree`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Params {
    pub scheme: Scheme,
    /// FORS trees have `2^a` leaves.
    pub a: u64,
    /// Number of FORS trees.
    pub k: u64,
    /// Hash output in bytes.
    pub n: u64,
    /// Height above the leaves of the cached top-tree level; `None` is half of it.
    pub cache_height: Option<u64>,
    /// Cache one level rather than it and everything above.
    pub cache_level_only: bool,
}

impl Params {
    pub fn blocks(&self) -> Blocks {
        Blocks::new(self.n)
    }

    /// FORS trees actually built and authenticated: FORS+C grinds the last away.
    pub fn trees(&self) -> u64 {
        self.scheme.trees(self.k)
    }
}

/// What one layer costs. Every field is additive across layers except the
/// cached tree and the cache itself, which only the top layer has.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct LayerCost {
    pub l: u64,
    /// The target sum in force, the mean resolved.
    pub swn: u64,
    /// Counter values tried per signature at this layer.
    pub trials: u64,
    /// The authentication path and the WOTS signature this layer contributes.
    pub sig_bytes: u64,
    /// Walking this layer's chains and its authentication path.
    pub verify: Cost,
    /// The extra a WOTS-TW verifier walks when every message digit is zero.
    pub verify_worst_extra: Cost,
    /// Growing this layer's tree from the seed.
    pub tree: Cost,
    /// The same with its half top already in state, which is worth doing only
    /// for the top layer.
    pub tree_cached: Cost,
    pub cache_bytes: u64,
    pub cache_depth: u64,
}

/// One layer's costs. `nu` has to be the table for this layer's `(l, w)`.
pub fn layer_cost(layer: Layer, p: &Params, nu: Option<&NuTable>) -> Option<LayerCost> {
    let (n, b, w) = (p.n, p.blocks(), layer.w());
    let l = layer.chains(n, p.scheme)?;
    let enc = layer.encoding(n)?;
    let leaves = 1u64 << layer.height();

    // One WOTS key pair, plus the compression of its l chain ends into a leaf.
    let leaf = Cost::new(
        l + l * (w - 1) + 1,
        l * b.prf() + l * (w - 1) * b.chain_step() + b.compress(l),
    );
    let tree = |height: u64| {
        let count = 1u64 << height;
        leaf * count + Cost::new(count - 1, (count - 1) * b.merkle_node())
    };

    // Only the top tree is worth caching: it is the same for every signature,
    // while the trees below it are picked by the (pseudorandom) index. Its auth
    // path splits at the cached level: below, rebuild the 2^c-leaf subtree the
    // signing leaf sits in; above, the nodes are already in state. Rebuilt
    // leaves are charged a full WOTS public key, as everywhere else here.
    //
    // A BDS-style traversal would amortize a tree to h' leaves per signature
    // with O(h') state, but it only works walking the leaves in order.
    // SPHINCS+ picks its index by hashing the message, so consecutive
    // signatures land on unrelated leaves and nothing amortizes; an
    // index-independent cache like this one is what is left, hence sqrt rather
    // than h'.
    let c = p.cache_height.unwrap_or(layer.height() / 2);
    if c > layer.height() {
        return None;
    }
    let stored_level = 1u64 << (layer.height() - c);
    let mut cached = tree(c);
    let cache_bytes;
    if p.cache_level_only {
        cached = cached + Cost::new(stored_level - 1, (stored_level - 1) * b.merkle_node());
        cache_bytes = stored_level * n;
    } else {
        cache_bytes = (2 * stored_level - 1) * n;
    }

    let counter = if p.scheme.wots_c() { COUNTER_BYTES } else { 0 };
    let auth = Cost::new(layer.height(), layer.height() * b.merkle_node());
    let (swn, trials, verify, verify_worst_extra) = if p.scheme.wots_c() {
        let swn = layer.swn().unwrap_or(enc.default_swn());
        let table = nu?;
        // the digits sum to S_wn, so the remaining chain steps are fixed at
        // (w-1)*l - S_wn, and the counter is hashed in once per layer
        let steps = (w - 1) * l.checked_sub(0)?;
        let steps = steps.checked_sub(swn.min(steps))?;
        let walk = Cost::new(
            steps + 2,
            steps * b.chain_step() + b.chain_step_with_counter() + b.compress(l),
        );
        (swn, table.trials(swn), walk + auth, Cost::default())
    } else {
        let avg = (w - 1) * l / 2;
        let worst = layer.wots_tw_worst_steps(n);
        let walk = Cost::new(avg + 1, avg * b.chain_step() + b.compress(l));
        let extra = Cost::new(worst - avg, (worst - avg) * b.chain_step());
        (0, 0, walk + auth, extra)
    };

    Some(LayerCost {
        l,
        swn,
        trials,
        sig_bytes: layer.height() * n + l * n + counter,
        verify,
        verify_worst_extra,
        tree: tree(layer.height()),
        tree_cached: cached,
        cache_bytes,
        cache_depth: layer.height() - c,
        // `leaves` is only here to keep the shift above honest
    })
    .filter(|_| leaves > 0)
}

/// The FORS side, which no layer sees.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fors {
    pub sig_bytes: u64,
    /// Growing the trees, and any grinding FORS+C does.
    pub sign: Cost,
    pub grinding: Cost,
    /// Opening the leaves, plus the message hash.
    pub verify: Cost,
}

impl Fors {
    pub fn new(p: &Params) -> Option<Self> {
        if p.k < 1 || p.a < 1 || p.a > 63 || (p.scheme.fors_c() && p.k < 2) {
            return None;
        }
        let (n, b, trees, t) = (p.n, p.blocks(), p.trees(), 1u64 << p.a);
        let msg_hash = Cost::new(2, b.message_hash() + b.message_prf());
        let build = Cost::new(
            trees * t + trees * t + trees * (t - 1) + 1,
            trees * t * b.prf() + trees * t * b.chain_step() + trees * (t - 1) * b.merkle_node() + b.compress(trees),
        );
        // FORS+C grinds the digest until its last a bits vanish, so the last
        // FORS tree always opens leaf 0 and needs no authentication path.
        let grinding = if p.scheme.fors_c() { msg_hash * t } else { msg_hash };
        let verify = Cost::new(
            trees + trees * p.a + 1,
            trees * b.chain_step() + trees * p.a * b.merkle_node() + b.compress(trees),
        );
        Some(Self {
            sig_bytes: n + trees * n + trees * p.a * n,
            sign: build + grinding,
            grinding: if p.scheme.fors_c() { grinding } else { Cost::default() },
            verify: verify + Cost::new(1, b.message_hash()),
        })
    }
}

/// Every cost of one parameter set.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Costs {
    pub hypertree: Hypertree,
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

/// A hypertree's costs, added up. Independent of the FORS side, so a search
/// that varies `(a, k)` builds this once and adds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HyperCost {
    pub hypertree: Hypertree,
    pub sig_bytes: u64,
    pub verify: Cost,
    pub verify_worst_extra: Cost,
    /// Growing every layer's tree from the seed.
    pub trees: Cost,
    /// The same with the top tree's half top already in state.
    pub trees_cached: Cost,
    /// Growing the top tree, which is all key generation does.
    pub keygen: Cost,
    /// Counter values tried per signature, across every layer.
    pub trials: u64,
    pub cache_bytes: u64,
    pub cache_depth: u64,
}

/// Add up one hypertree, layer by layer.
pub fn hyper_cost(p: &Params, ht: &Hypertree, nu: &mut NuCache) -> Option<HyperCost> {
    let mut out = HyperCost {
        hypertree: *ht,
        sig_bytes: 0,
        verify: Cost::default(),
        verify_worst_extra: Cost::default(),
        trees: Cost::default(),
        trees_cached: Cost::default(),
        keygen: Cost::default(),
        trials: 0,
        cache_bytes: 0,
        cache_depth: 0,
    };
    for (i, layer) in ht.layers().enumerate() {
        let l = layer.chains(p.n, p.scheme)?;
        let table = p.scheme.wots_c().then(|| nu.table(l, layer.w()));
        let c = layer_cost(layer, p, table)?;
        out.sig_bytes += c.sig_bytes;
        out.verify = out.verify + c.verify;
        out.verify_worst_extra = out.verify_worst_extra + c.verify_worst_extra;
        out.trees = out.trees + c.tree;
        out.trials += c.trials;
        if i == 0 {
            out.keygen = c.tree;
            out.trees_cached = out.trees_cached + c.tree_cached;
            out.cache_bytes = c.cache_bytes;
            out.cache_depth = c.cache_depth;
        } else {
            out.trees_cached = out.trees_cached + c.tree;
        }
    }
    Some(out)
}

/// Add a hypertree and a FORS side together. Pure arithmetic: no tables.
pub fn assemble(p: &Params, hyper: &HyperCost, fors: &Fors) -> Costs {
    let grind = Cost::new(1, p.blocks().chain_step_with_counter()) * hyper.trials;
    Costs {
        hypertree: hyper.hypertree,
        sig_bytes: fors.sig_bytes + hyper.sig_bytes,
        keygen: hyper.keygen,
        sign: hyper.trees_cached + fors.sign + grind,
        sign_cold: hyper.trees + fors.sign + grind,
        verify: fors.verify + hyper.verify,
        verify_worst: fors.verify + hyper.verify + hyper.verify_worst_extra,
        wots_c_grinding: grind,
        fors_c_grinding: fors.grinding,
        cache_depth: hyper.cache_depth,
        cache_bytes: hyper.cache_bytes,
    }
}

/// Costs of one parameter set, building whatever digit-sum tables it needs.
///
/// Convenient for a single evaluation; a search should hold a [`NuCache`] and
/// call [`assemble`] itself.
pub fn costs(p: Params, ht: &Hypertree) -> Option<Costs> {
    let fors = Fors::new(&p)?;
    let mut nu = NuCache::new(p.n);
    Some(assemble(&p, &hyper_cost(&p, ht, &mut nu)?, &fors))
}

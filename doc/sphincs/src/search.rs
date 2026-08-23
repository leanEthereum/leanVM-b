//! Exhaustive search for the parameter set with the cheapest verification.
//!
//! Every `(scheme, h, d | h, chain_bits, dropped_chains, a, k, S_wn)` point that
//! meets the budgets is costed and compared. Nothing is chosen by an optimality
//! argument, and nothing is skipped by a monotonicity one: the three tests that
//! run before the `S_wn` scan reject only points that no `S_wn` could rescue,
//! because size and keygen do not depend on `S_wn` at all, and the least
//! grinding any `S_wn` can ask for is read off the digit-sum table rather than
//! assumed to sit anywhere in particular.
//!
//! What is assumed is the searched range of each parameter, hardcoded below.
//! When a result comes out at the top of one of those ranges the range itself
//! may be what is limiting it, so [`edges`] reports that and names the constant
//! to raise. Ranges the budgets or the structure already close (`d` over the
//! divisors of `h`, `S_wn` over the digit sums a code of `l` chains can reach)
//! need no such warning and get none.

use std::time::Instant;

use crate::cost::{Cost, NuTable, SCHEMES, Scheme};
use crate::params::{Costs, Params, Skeleton};
use crate::security::SecurityTable;

/// Hardcoded search ranges, wide enough that the budgets are normally what
/// binds: SLH-DSA level 1 lives at `h = 63..64`, `a = 6..14`, `k = 14..35`,
/// `chain_bits = 4`, and the report's candidates at `h = 20..44`, `a = 14..16`,
/// `k = 8..11`, so every range here has room above anything yet proposed.
/// Raising one costs only runtime.
pub const H_MAX: u64 = 96;
/// log2 of the leaves in one FORS tree.
pub const A_MAX: u64 = 32;
/// Number of FORS trees.
pub const K_MAX: u64 = 64;
/// log2(w), so w up to 4096.
pub const CHAIN_BITS_MAX: u64 = 12;
/// WOTS+C chains dropped beyond the minimal bit pinning.
pub const DROPPED_MAX: u64 = 16;

/// NIST level 1, matching SLH-DSA's level 1 parameter sets.
pub const LEVEL1_BITS: f64 = 128.0;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Unit {
    Hashes,
    Compressions,
}

impl Unit {
    pub fn of(self, c: Cost) -> u64 {
        match self {
            Unit::Hashes => c.hashes,
            Unit::Compressions => c.compressions,
        }
    }
    pub fn label(self) -> &'static str {
        match self {
            Unit::Hashes => "hashes",
            Unit::Compressions => "compressions",
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Budgets {
    /// log2 of the signatures allowed under one public key.
    pub lifetime: u32,
    pub max_keygen: u64,
    pub max_sign: u64,
    pub max_sign_cached: u64,
    pub max_size: u64,
    /// Classical security floor in bits.
    pub security: f64,
    /// Unit of every budget above, and of the objective.
    pub unit: Unit,
}

impl Budgets {
    fn of(&self, c: Cost) -> u64 {
        self.unit.of(c)
    }

    fn fits(&self, c: &Costs) -> bool {
        c.sig_bytes <= self.max_size
            && self.of(c.keygen) <= self.max_keygen
            && self.of(c.sign) <= self.max_sign
            && self.of(c.sign_cached) <= self.max_sign_cached
    }
}

#[derive(Clone, Debug)]
pub struct Grid {
    pub schemes: Vec<Scheme>,
    pub n: u64,
    pub h_min: u64,
    pub h_max: u64,
    pub a_min: u64,
    pub a_max: u64,
    pub k_max: u64,
    pub chain_bits: Vec<u64>,
    pub max_dropped: u64,
    pub cache_level_only: bool,
}

impl Default for Grid {
    fn default() -> Self {
        Self {
            schemes: SCHEMES.to_vec(),
            n: 16,
            h_min: 1,
            h_max: H_MAX,
            a_min: 1,
            a_max: A_MAX,
            k_max: K_MAX,
            chain_bits: (1..=CHAIN_BITS_MAX).collect(),
            max_dropped: DROPPED_MAX,
            cache_level_only: false,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Candidate {
    pub params: Params,
    pub costs: Costs,
}

impl Candidate {
    pub fn key(&self) -> Key {
        let p = self.params;
        (p.scheme, p.h, p.d, p.a, p.k, p.w, p.dropped_chains)
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct Stats {
    /// `(scheme, h, d, chain_bits, dropped)` tuples reached.
    pub grid: u64,
    pub keygen_pruned: u64,
    /// `(a, k)` pairs rejected by the security floor.
    pub insecure: u64,
    /// `(a, k)` pairs whose signature is too big, whatever the target sum.
    pub size_pruned: u64,
    /// `(a, k)` pairs too slow to sign at the least grinding any target sum asks.
    pub sign_pruned: u64,
    /// `(a, k)` pairs whose whole target-sum range was scanned.
    pub swept: u64,
    /// Points meeting every budget.
    pub feasible: u64,
    pub skeletons: u64,
    pub seconds: f64,
}

impl std::fmt::Display for Stats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "grid {} (scheme, h, d, chain_bits, dropped) tuples, {} over keygen; \
             then {} (a, k) pairs insecure, {} over size, {} over signing; \
             {} target-sum ranges swept, {} points feasible ({} parameter sets costed) in {:.1}s",
            self.grid,
            self.keygen_pruned,
            self.insecure,
            self.size_pruned,
            self.sign_pruned,
            self.swept,
            self.feasible,
            self.skeletons,
            self.seconds
        )
    }
}

/// Identifies one parameter tuple, everything but the target sum.
pub type Key = (Scheme, u64, u64, u64, u64, u64, u64);

fn divisors(h: u64) -> Vec<u64> {
    (1..=h).filter(|d| h.is_multiple_of(*d)).collect()
}

fn params(g: &Grid, scheme: Scheme, h: u64, d: u64, a: u64, k: u64, w: u64, dropped: u64) -> Params {
    Params {
        scheme,
        h,
        d,
        a,
        k,
        w,
        n: g.n,
        dropped_chains: dropped,
        cache_height: None,
        cache_level_only: g.cache_level_only,
        convention: Default::default(),
    }
}

/// Every feasible parameter set, ordered by verification cost.
///
/// One row per `(scheme, h, d, a, k, w, dropped_chains)`, carrying the best
/// target sum for that tuple. Rows are what gets printed; the comparison behind
/// each one saw every target sum.
pub fn search(b: &Budgets, g: &Grid, st: &mut Stats) -> Vec<Candidate> {
    let started = Instant::now();
    let digest_bits = (8 * g.n) as u32;
    let mut sec = SecurityTable::new(b.lifetime, b.security, g.n, g.h_max as u32, g.k_max, g.a_max);
    let mut best: Vec<Candidate> = Vec::new();
    let mut index: std::collections::HashMap<Key, usize> = Default::default();
    let all_divisors: Vec<Vec<u64>> = (0..=g.h_max).map(divisors).collect();

    for &scheme in &g.schemes {
        for &bits in &g.chain_bits {
            let w = 1u64 << bits;
            // WOTS-TW has no counter to grind, so it cannot drop chains, and
            // WOTS+C has to keep at least one.
            let max_dropped = if scheme.wots_c() {
                g.max_dropped.min((8 * g.n / bits).saturating_sub(1))
            } else {
                0
            };
            for dropped in 0..=max_dropped {
                let probe = params(
                    g,
                    scheme,
                    g.h_max.max(1),
                    1,
                    g.a_min,
                    if scheme.fors_c() { 2 } else { 1 },
                    w,
                    dropped,
                );
                let Some(l) = probe.chains() else { continue };
                let table = scheme.wots_c().then(|| NuTable::new(l, w, digest_bits));
                let min_trials = table.as_ref().map_or(0, |t| t.min_trials());
                for h in g.h_min..=g.h_max {
                    for &d in &all_divisors[h as usize] {
                        st.grid += 1;
                        // keygen is one top tree: no a, k or target sum in it
                        let kg = params(
                            g,
                            scheme,
                            h,
                            d,
                            g.a_min,
                            if scheme.fors_c() { 2 } else { 1 },
                            w,
                            dropped,
                        );
                        let Some(kg) = Skeleton::new(kg) else { continue };
                        st.skeletons += 1;
                        if b.of(kg.keygen) > b.max_keygen {
                            st.keygen_pruned += 1;
                            continue;
                        }
                        for a in g.a_min..=g.a_max {
                            for k in 1..=g.k_max {
                                if !sec.is_secure(h as u32, k, a) {
                                    st.insecure += 1;
                                    continue;
                                }
                                let p = params(g, scheme, h, d, a, k, w, dropped);
                                let Some(sk) = Skeleton::new(p) else { continue };
                                st.skeletons += 1;
                                // size and keygen do not depend on the target
                                // sum, and no target sum grinds less than the
                                // table's cheapest, so these three reject only
                                // points that no target sum could rescue
                                if sk.sig_bytes > b.max_size {
                                    st.size_pruned += 1;
                                    continue;
                                }
                                if b.of(sk.sign(min_trials)) > b.max_sign
                                    || b.of(sk.sign_cached(min_trials)) > b.max_sign_cached
                                {
                                    st.sign_pruned += 1;
                                    continue;
                                }
                                let Some(table) = table.as_ref() else {
                                    // WOTS-TW: no target sum to choose
                                    let c = sk.finish(0, 0);
                                    if b.fits(&c) {
                                        st.feasible += 1;
                                        record(&mut best, &mut index, Candidate { params: p, costs: c }, b);
                                    }
                                    continue;
                                };
                                st.swept += 1;
                                let mut winner: Option<(u64, u64)> = None;
                                for swn in 0..=sk.max_swn {
                                    let trials = table.trials(swn);
                                    if b.of(sk.sign(trials)) > b.max_sign
                                        || b.of(sk.sign_cached(trials)) > b.max_sign_cached
                                    {
                                        continue;
                                    }
                                    st.feasible += 1;
                                    let v = b.of(sk.verify(swn));
                                    if winner.is_none_or(|(_, best_v)| v < best_v) {
                                        winner = Some((swn, v));
                                    }
                                }
                                if let Some((swn, _)) = winner {
                                    let c = sk.finish(swn, table.trials(swn));
                                    record(&mut best, &mut index, Candidate { params: p, costs: c }, b);
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    st.seconds = started.elapsed().as_secs_f64();
    best.sort_by_key(|c| (b.of(c.costs.verify), c.costs.sig_bytes, b.of(c.costs.sign)));
    best
}

fn record(best: &mut Vec<Candidate>, index: &mut std::collections::HashMap<Key, usize>, cand: Candidate, b: &Budgets) {
    match index.get(&cand.key()) {
        Some(&i) if b.of(best[i].costs.verify) <= b.of(cand.costs.verify) => {}
        Some(&i) => best[i] = cand,
        None => {
            index.insert(cand.key(), best.len());
            best.push(cand);
        }
    }
}

/// Axes where a result sits at the top of a hardcoded range.
///
/// Such a result may be limited by the range rather than by the budgets, so it
/// is worth raising the range and rerunning before believing it.
pub fn edges(g: &Grid, c: &Candidate) -> Vec<String> {
    let bits_max = g.chain_bits.iter().copied().max().unwrap_or(0);
    let at = [
        ("h", c.params.h, g.h_max, "H_MAX / --h-max"),
        ("a", c.params.a, g.a_max, "A_MAX / --a-max"),
        ("k", c.params.k, g.k_max, "K_MAX / --k-max"),
        (
            "chain_bits",
            c.costs.chain_bits,
            bits_max,
            "CHAIN_BITS_MAX / --chain-bits",
        ),
        (
            "dropped_chains",
            c.params.dropped_chains,
            g.max_dropped,
            "DROPPED_MAX / --max-dropped",
        ),
    ];
    at.iter()
        .filter(|(_, v, limit, _)| *v + 1 >= *limit)
        .map(|(axis, v, limit, what)| {
            let where_ = if v >= limit { "at" } else { "one step below" };
            format!("{axis} = {v} is {where_} the top of the searched range ({limit}): raise {what} and rerun")
        })
        .collect()
}

/// The same search with nothing skipped: every `(a, k, S_wn)` point costed in
/// full and checked against every budget.
///
/// Only usable on a tiny grid, which is the point: it is the oracle the real
/// search is diffed against in `tests/goldens`.
pub fn naive_search(b: &Budgets, g: &Grid) -> Vec<Candidate> {
    let digest_bits = (8 * g.n) as u32;
    let mut out: Vec<Candidate> = Vec::new();
    for &scheme in &g.schemes {
        for &bits in &g.chain_bits {
            let w = 1u64 << bits;
            let max_dropped = if scheme.wots_c() { g.max_dropped } else { 0 };
            for dropped in 0..=max_dropped {
                for h in g.h_min..=g.h_max {
                    for d in divisors(h) {
                        for a in g.a_min..=g.a_max {
                            for k in 1..=g.k_max {
                                let p = params(g, scheme, h, d, a, k, w, dropped);
                                let Some(sk) = Skeleton::new(p) else { continue };
                                if crate::security::security_bits(b.lifetime, h as u32, k, a, g.n) < b.security {
                                    continue;
                                }
                                let table = scheme.wots_c().then(|| NuTable::new(sk.l, w, digest_bits));
                                let sums: Vec<u64> = match &table {
                                    Some(_) => (0..=sk.max_swn).collect(),
                                    None => vec![0],
                                };
                                for swn in sums {
                                    let trials = table.as_ref().map_or(0, |t| t.trials(swn));
                                    let c = sk.finish(swn, trials);
                                    if b.fits(&c) {
                                        out.push(Candidate { params: p, costs: c });
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    out.sort_by_key(|c| (b.of(c.costs.verify), c.costs.sig_bytes, b.of(c.costs.sign)));
    out
}

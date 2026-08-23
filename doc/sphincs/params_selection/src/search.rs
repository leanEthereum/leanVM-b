//! Exhaustive search for the parameter set with the cheapest verification.
//!
//! Every `(scheme, h, d, h_top, chain_bits, dropped_chains, a, k, S_wn)` point
//! that meets the budgets is costed and compared. Nothing is chosen by an
//! optimality argument, and nothing is skipped by a monotonicity one: the three
//! tests that run before the `S_wn` scan reject only points that no `S_wn` could
//! rescue, because size and keygen do not depend on `S_wn` at all, and the least
//! grinding any `S_wn` can ask for is read off the digit-sum table rather than
//! assumed to sit anywhere in particular.
//!
//! Any axis can be pinned to a single value instead of searched, which is how
//! one parameter set gets costed: pin them all. Budgets are optional, and an
//! unset one is no limit.
//!
//! The layer heights are `(h, d, h_top)`: the top tree gets `h_top`, the rest
//! divide what is left as evenly as it goes. [`crate::params::Profile`] argues
//! why that shape covers the cost-optimal representative of every profile, so
//! `d` no longer has to divide `h`. Which `h_top` is best does not depend on
//! `(a, k)` or on the target sum, because size and verification do not depend on
//! `h_top` at all and both signing budgets take the `(a, k)` part as the same
//! additive offset; so the profiles are ranked once per `(h, d)`, by how much
//! grinding they leave room for, and that ranking then holds for every `(a, k)`.
//!
//! What is assumed is the searched range of each parameter, hardcoded below.
//! When a result comes out at the top of one of those ranges the range itself
//! may be what is limiting it, so [`edges`] reports that and names the constant
//! to raise. Ranges the structure already closes (`d` over layer heights that do
//! not add up to `h`, `S_wn` over the digit sums a code of `l` chains can reach)
//! need no such warning and get none, and neither does an axis pinned by hand.

use std::ops::RangeInclusive;
use std::time::Instant;

use crate::cost::{Cost, NuTable, SCHEMES, Scheme};
use crate::params::{Costs, Layers, Params, Skeleton};
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
/// Hypertree layers.
pub const D_MAX: u64 = 32;
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

/// The values of one parameter to try. Pinned when `lo == hi`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Span {
    pub lo: u64,
    pub hi: u64,
}

impl Span {
    pub const fn new(lo: u64, hi: u64) -> Self {
        Self { lo, hi }
    }
    pub const fn pin(v: u64) -> Self {
        Self { lo: v, hi: v }
    }
    pub const fn pinned(&self) -> bool {
        self.lo >= self.hi
    }
    pub const fn iter(&self) -> RangeInclusive<u64> {
        self.lo..=self.hi
    }
    /// The span, further limited by something the parameters imply.
    pub fn within(&self, hi: u64) -> RangeInclusive<u64> {
        self.lo..=self.hi.min(hi)
    }
}

/// Which target sums to consider.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Sums {
    /// Only this one.
    Pinned(u64),
    /// Only the mean, where grinding is cheapest. What to use when nothing
    /// bounds the signer, since then there is no reason to grind harder, and
    /// what the report's own parameter sets do.
    Mean,
    /// All of them, keeping the best the budgets allow.
    Sweep,
}

#[derive(Clone, Copy, Debug)]
pub struct Budgets {
    /// log2 of the signatures allowed under one public key.
    pub lifetime: u32,
    /// An unset budget is no limit.
    pub keygen: Option<u64>,
    pub sign: Option<u64>,
    pub sign_cached: Option<u64>,
    pub size: Option<u64>,
    /// Classical security floor in bits.
    pub security: f64,
    /// Unit of every budget above, and of the objective.
    pub unit: Unit,
}

impl Budgets {
    pub fn max_keygen(&self) -> u64 {
        self.keygen.unwrap_or(u64::MAX)
    }
    pub fn max_sign(&self) -> u64 {
        self.sign.unwrap_or(u64::MAX)
    }
    pub fn max_sign_cached(&self) -> u64 {
        self.sign_cached.unwrap_or(u64::MAX)
    }
    pub fn max_size(&self) -> u64 {
        self.size.unwrap_or(u64::MAX)
    }
    pub fn any_signing_limit(&self) -> bool {
        self.sign.is_some() || self.sign_cached.is_some()
    }

    pub fn of(&self, c: Cost) -> u64 {
        self.unit.of(c)
    }

    pub fn fits(&self, c: &Costs) -> bool {
        c.sig_bytes <= self.max_size()
            && self.of(c.keygen) <= self.max_keygen()
            && self.of(c.sign) <= self.max_sign()
            && self.of(c.sign_cached) <= self.max_sign_cached()
    }
}

#[derive(Clone, Debug)]
pub struct Grid {
    pub schemes: Vec<Scheme>,
    pub n: u64,
    pub h: Span,
    pub d: Span,
    /// `None` searches nothing: the classic split, `h/d` on every layer.
    pub h_top: Option<Span>,
    pub a: Span,
    pub k: Span,
    pub dropped: Span,
    pub chain_bits: Vec<u64>,
    pub sums: Sums,
    pub cache_level_only: bool,
}

impl Default for Grid {
    fn default() -> Self {
        Self {
            schemes: SCHEMES.to_vec(),
            n: 16,
            h: Span::new(1, H_MAX),
            d: Span::new(1, D_MAX),
            h_top: Some(Span::new(1, H_MAX)),
            a: Span::new(1, A_MAX),
            k: Span::new(1, K_MAX),
            dropped: Span::new(0, DROPPED_MAX),
            chain_bits: (1..=CHAIN_BITS_MAX).collect(),
            sums: Sums::Sweep,
            cache_level_only: false,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Candidate {
    pub params: Params,
    pub costs: Costs,
}

/// Identifies one parameter tuple: everything but the layer profile and the
/// target sum, neither of which changes what it verifies at.
pub type Key = (Scheme, u64, u64, u64, u64, u64, u64);

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
    /// `(a, k)` pairs whose target sums were scanned.
    pub swept: u64,
    /// Points meeting every budget.
    pub feasible: u64,
    pub skeletons: u64,
    /// Layer profiles kept after the keygen budget.
    pub profiles: u64,
    /// Parameter tuples that came out feasible, one row each.
    pub rows: u64,
    /// Rows dropped as worse than everything kept.
    pub rows_dropped: u64,
    pub seconds: f64,
}

impl std::fmt::Display for Stats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "grid {} (scheme, h, d, chain_bits, dropped) tuples, {} over keygen; \
             then {} (a, k) pairs insecure, {} over size, {} over signing; \
             {} target-sum ranges swept, {} points feasible over {} rows ({} dropped as worse than everything kept); \
             {} layer profiles and {} parameter sets costed in {:.1}s",
            self.grid,
            self.keygen_pruned,
            self.insecure,
            self.size_pruned,
            self.sign_pruned,
            self.swept,
            self.feasible,
            self.rows,
            self.rows_dropped,
            self.profiles,
            self.skeletons,
            self.seconds
        )
    }
}

fn params(g: &Grid, scheme: Scheme, h: u64, d: u64, a: u64, k: u64, w: u64, dropped: u64) -> Params {
    Params {
        scheme,
        h,
        d,
        h_top: None,
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

/// The layer profiles worth trying for one `(h, d)`, and how much grinding the
/// best of them leaves room for.
///
/// `slack` is `max over profiles of min(max_sign - trees, max_sign_cached -
/// trees_cached)`, in the budget's unit. Both signing costs take the `(a, k)`
/// part of signing as the same additive offset, so subtracting that offset from
/// `slack` gives the grinding budget of the best profile for any `(a, k)`,
/// without re-ranking the profiles per candidate.
struct Room {
    profiles: Vec<Layers>,
    slack: u64,
}

fn room(b: &Budgets, g: &Grid, p: &Params) -> Option<Room> {
    let mut profiles = Vec::new();
    let mut slack = 0;
    let mut consider = |h_top: Option<u64>| {
        let Some(lay) = Layers::new(&Params { h_top, ..*p }) else {
            return;
        };
        if b.of(lay.keygen) > b.max_keygen() {
            return;
        }
        let room = b
            .max_sign()
            .saturating_sub(b.of(lay.trees))
            .min(b.max_sign_cached().saturating_sub(b.of(lay.trees_cached)));
        slack = slack.max(room);
        profiles.push(lay);
    };
    match g.h_top {
        None => consider(None),
        Some(span) => {
            // The top tree has 2^h_top leaves and every leaf costs at least one
            // hash, so a top height past the keygen budget's log is out for any
            // (a, k).
            let ceiling = 64 - b.max_keygen().max(1).leading_zeros() as u64;
            for h_top in span.within((p.h + 1).saturating_sub(p.d).min(ceiling)) {
                consider(Some(h_top));
            }
        }
    }
    (!profiles.is_empty()).then_some(Room { profiles, slack })
}

/// Every feasible parameter set, ordered by verification cost.
///
/// One row per `(scheme, h, d, a, k, w, dropped_chains)`, carrying the best
/// target sum for that tuple and the layer profile that admitted it. Rows are
/// what gets printed; the comparison behind each one saw every target sum.
pub fn search(b: &Budgets, g: &Grid, st: &mut Stats) -> Vec<Candidate> {
    let started = Instant::now();
    let digest_bits = (8 * g.n) as u32;
    let mut sec = SecurityTable::new(b.lifetime, b.security, g.n, g.h.hi as u32, g.k.hi, g.a.hi);
    // Every (scheme, h, d, a, k, w, dropped) key is reached exactly once, so
    // rows need no deduplication, only a bound: budgets loose enough to admit
    // millions of them would otherwise be held in memory to print a dozen.
    let mut best: Vec<Candidate> = Vec::new();

    for &scheme in &g.schemes {
        for &bits in &g.chain_bits {
            let w = 1u64 << bits;
            // WOTS-TW has no counter to grind, so it cannot drop chains, and
            // WOTS+C has to keep at least one.
            let dropped_range = if scheme.wots_c() {
                g.dropped.within((8 * g.n / bits).saturating_sub(1))
            } else {
                0..=0
            };
            for dropped in dropped_range {
                let probe = params(
                    g,
                    scheme,
                    g.h.hi.max(1),
                    1,
                    g.a.lo,
                    if scheme.fors_c() { 2 } else { 1 },
                    w,
                    dropped,
                );
                let Some(l) = probe.chains() else { continue };
                let table = scheme.wots_c().then(|| NuTable::new(l, w, digest_bits));
                let min_trials = table.as_ref().map_or(0, |t| t.min_trials());
                for h in g.h.iter() {
                    for d in g.d.within(h) {
                        st.grid += 1;
                        // Layer profiles first: they need no a or k, and the
                        // keygen budget alone usually settles the question.
                        let Some(room) = room(b, g, &params(g, scheme, h, d, g.a.lo, 1, w, dropped)) else {
                            st.keygen_pruned += 1;
                            continue;
                        };
                        st.profiles += room.profiles.len() as u64;
                        for a in g.a.iter() {
                            for k in g.k.iter() {
                                if !sec.is_secure(h as u32, k, a) {
                                    st.insecure += 1;
                                    continue;
                                }
                                let p = params(g, scheme, h, d, a, k, w, dropped);
                                let Some(sk) = Skeleton::new(p) else { continue };
                                st.skeletons += 1;
                                // The signature grows with k, so once it is too
                                // big it stays too big.
                                if sk.sig_bytes > b.max_size() {
                                    st.size_pruned += 1;
                                    break;
                                }
                                // What the best profile can still afford to
                                // grind, once this (a, k) has taken its share.
                                let per_trial = b.of(sk.grind_step) * d;
                                let max_trials = room.slack.saturating_sub(b.of(sk.fors_part)) / per_trial.max(1);
                                let Some(table) = table.as_ref() else {
                                    // WOTS-TW: no counter, no target sum
                                    if room.slack >= b.of(sk.fors_part) {
                                        st.feasible += 1;
                                        record(&mut best, st, b, &sk, &room, 0, 0);
                                    }
                                    continue;
                                };
                                if max_trials < min_trials {
                                    st.sign_pruned += 1;
                                    continue;
                                }
                                let sums = match g.sums {
                                    Sums::Sweep => 0..=sk.max_swn,
                                    Sums::Mean => sk.default_swn..=sk.default_swn,
                                    Sums::Pinned(s) => s..=s,
                                };
                                st.swept += 1;
                                let mut winner: Option<(u64, u64)> = None;
                                for swn in sums {
                                    if table.trials(swn) > max_trials {
                                        continue;
                                    }
                                    st.feasible += 1;
                                    let v = b.of(sk.verify(swn));
                                    if winner.is_none_or(|(_, best_v)| v < best_v) {
                                        winner = Some((swn, v));
                                    }
                                }
                                if let Some((swn, _)) = winner {
                                    record(&mut best, st, b, &sk, &room, swn, table.trials(swn));
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    st.seconds = started.elapsed().as_secs_f64();
    sort_rows(&mut best, b);
    best
}

/// Rows kept before the list is trimmed back to `ROWS_KEPT`. The optimum is
/// unaffected: what gets dropped is worse than everything retained.
const ROWS_CAP: usize = 1 << 18;
const ROWS_KEPT: usize = 1 << 17;

fn sort_rows(rows: &mut [Candidate], b: &Budgets) {
    rows.sort_by_key(|c| (b.of(c.costs.verify), c.costs.sig_bytes, b.of(c.costs.sign)));
}

/// Record this parameter tuple on the cheapest layer profile that fits: they
/// all verify the same, so the tie goes to cached signing.
fn record(rows: &mut Vec<Candidate>, st: &mut Stats, b: &Budgets, sk: &Skeleton, room: &Room, swn: u64, trials: u64) {
    let Some(lay) = room
        .profiles
        .iter()
        .filter(|lay| {
            b.of(sk.sign(lay, trials)) <= b.max_sign() && b.of(sk.sign_cached(lay, trials)) <= b.max_sign_cached()
        })
        .min_by_key(|lay| (b.of(sk.sign_cached(lay, trials)), b.of(sk.sign(lay, trials))))
    else {
        return;
    };
    st.rows += 1;
    rows.push(Candidate {
        params: Params {
            h_top: Some(lay.profile.h_top),
            ..sk.params
        },
        costs: sk.finish(lay, swn, trials),
    });
    if rows.len() >= ROWS_CAP {
        sort_rows(rows, b);
        rows.truncate(ROWS_KEPT);
        st.rows_dropped += (ROWS_CAP - ROWS_KEPT) as u64;
    }
}

/// Axes where a result sits at the top of a searched range.
///
/// Such a result may be limited by the range rather than by the budgets, so it
/// is worth raising the range and rerunning before believing it. An axis pinned
/// to one value was pinned deliberately and says nothing.
pub fn edges(g: &Grid, c: &Candidate) -> Vec<String> {
    let bits = Span::new(
        g.chain_bits.iter().copied().min().unwrap_or(0),
        g.chain_bits.iter().copied().max().unwrap_or(0),
    );
    let at = [
        ("h", c.params.h, g.h, "H_MAX / --height"),
        ("d", c.params.d, g.d, "D_MAX / --layers"),
        ("a", c.params.a, g.a, "A_MAX / -a"),
        ("k", c.params.k, g.k, "K_MAX / -k"),
        ("chain_bits", c.costs.chain_bits, bits, "CHAIN_BITS_MAX / --chain-bits"),
        (
            "dropped_chains",
            c.params.dropped_chains,
            g.dropped,
            "DROPPED_MAX / --drop-chains",
        ),
    ];
    at.iter()
        .filter(|(_, v, span, _)| !span.pinned() && *v + 1 >= span.hi)
        .map(|(axis, v, span, what)| {
            let where_ = if *v >= span.hi { "at" } else { "one step below" };
            format!(
                "{axis} = {v} is {where_} the top of the searched range ({}): raise {what} and rerun",
                span.hi
            )
        })
        .collect()
}

/// The same search with nothing skipped: every `(a, k, h_top, S_wn)` point
/// costed in full and checked against every budget.
///
/// Only usable on a tiny grid, which is the point: it is the oracle the real
/// search is diffed against in `tests/goldens`.
pub fn naive_search(b: &Budgets, g: &Grid) -> Vec<Candidate> {
    let digest_bits = (8 * g.n) as u32;
    let mut out: Vec<Candidate> = Vec::new();
    for &scheme in &g.schemes {
        for &bits in &g.chain_bits {
            let w = 1u64 << bits;
            let dropped_range = if scheme.wots_c() { g.dropped.iter() } else { 0..=0 };
            for dropped in dropped_range {
                for h in g.h.iter() {
                    for d in g.d.within(h) {
                        for h_top in 1..=h {
                            for a in g.a.iter() {
                                for k in g.k.iter() {
                                    let p = Params {
                                        h_top: Some(h_top),
                                        ..params(g, scheme, h, d, a, k, w, dropped)
                                    };
                                    let Some(sk) = Skeleton::new(p) else { continue };
                                    let Some(lay) = Layers::new(&p) else { continue };
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
                                        let c = sk.finish(&lay, swn, trials);
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
    }
    out.sort_by_key(|c| (b.of(c.costs.verify), c.costs.sig_bytes, b.of(c.costs.sign)));
    out
}

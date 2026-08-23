//! Exhaustive search for the parameter set with the cheapest verification.
//!
//! Every `(scheme, a, k, h, d, h_top, and a WOTS instance for the top layer and
//! one for the rest)` point that meets the budgets is costed and compared.
//! Nothing is chosen by an optimality argument, and nothing is skipped by a
//! monotonicity one: the tests that run before the target-sum scan reject only
//! points that no target sum could rescue, because size and keygen do not
//! depend on the target sums at all, and the least grinding any of them can ask
//! for is read off the digit-sum table rather than assumed to sit anywhere in
//! particular.
//!
//! Two WOTS instances rather than `d` of them is not a restriction:
//! [`Hypertree::two_group`] gives the argument, and a test checks it against
//! every per-layer assignment of small hypertrees. Any axis can also be pinned
//! to a single value instead of searched, which is how one parameter set gets
//! costed: pin them all. Budgets are optional, and an unset one is no limit.
//!
//! What is assumed is the searched range of each parameter, hardcoded below.
//! When a result comes out at the top of one of those ranges the range itself
//! may be what is limiting it, so [`edges`] reports that and names the constant
//! to raise. Ranges the structure already closes need no such warning and get
//! none, and neither does an axis pinned by hand.

use std::ops::RangeInclusive;
use std::time::Instant;

use crate::cost::{Cost, NuCache, SCHEMES, Scheme};
use crate::params::{Costs, Fors, Hypertree, Layer, Params, assemble};
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
    /// Only this one, on every layer.
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
    /// Signatures allowed under one public key. Need not be a power of two.
    pub q_s: f64,
    /// An unset budget is no limit.
    pub keygen: Option<u64>,
    /// Signing with the top tree's half top in state: see [`Costs::sign`].
    pub sign: Option<u64>,
    pub size: Option<u64>,
    /// Classical security floor in bits.
    pub security: f64,
}

impl Budgets {
    pub fn max_keygen(&self) -> u64 {
        self.keygen.unwrap_or(u64::MAX)
    }
    pub fn max_sign(&self) -> u64 {
        self.sign.unwrap_or(u64::MAX)
    }
    pub fn max_size(&self) -> u64 {
        self.size.unwrap_or(u64::MAX)
    }

    /// Everything is counted in compression calls: see [`crate::cost::Blocks`].
    pub fn of(&self, c: Cost) -> u64 {
        c.compressions
    }

    pub fn fits(&self, c: &Costs) -> bool {
        c.sig_bytes <= self.max_size() && self.of(c.keygen) <= self.max_keygen() && self.of(c.sign) <= self.max_sign()
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
    /// Search a separate WOTS instance for the top layer, rather than one for
    /// the whole hypertree.
    pub split_wots: bool,
    /// A hypertree given outright, which pins every axis it covers.
    pub hypertree: Option<Hypertree>,
    pub cache_height: Option<u64>,
    pub cache_level_only: bool,
}

impl Grid {
    /// Is every axis pinned to one value, so that a run costs one parameter set
    /// rather than searching for one? Distinct from a search that happens to
    /// leave one survivor, which still deserves its count and its table.
    pub fn fully_pinned(&self) -> bool {
        if self.hypertree.is_some() {
            return self.schemes.len() == 1 && self.a.pinned() && self.k.pinned();
        }
        let h_top_pinned = match self.h_top {
            None => true, // the classic split is one profile
            Some(span) => span.pinned(),
        };
        self.schemes.len() == 1
            && self.chain_bits.len() == 1
            && self.h.pinned()
            && self.d.pinned()
            && self.a.pinned()
            && self.k.pinned()
            && self.dropped.pinned()
            && h_top_pinned
            && !self.split_wots
            && !matches!(self.sums, Sums::Sweep)
    }
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
            split_wots: false,
            hypertree: None,
            cache_height: None,
            cache_level_only: false,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Candidate {
    pub params: Params,
    pub costs: Costs,
}

/// Identifies one parameter tuple: everything but the target sums, which do not
/// change what it verifies at.
pub type Key = (Scheme, u64, u64, u64, u64, u64, u64, u64, u64);

impl Candidate {
    pub fn key(&self) -> Key {
        let (p, ht) = (self.params, self.costs.hypertree);
        let low = ht.layers().last().unwrap_or(ht.top());
        (
            p.scheme,
            ht.height(),
            ht.depth(),
            p.a,
            p.k,
            ht.top().w(),
            ht.top().dropped_chains(),
            low.w(),
            low.dropped_chains(),
        )
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct Stats {
    /// `(scheme, h, d, top WOTS, lower WOTS)` tuples reached.
    pub grid: u64,
    pub keygen_pruned: u64,
    /// `(a, k)` pairs rejected by the security floor.
    pub insecure: u64,
    /// `(a, k)` pairs whose signature is too big, whatever the target sums.
    pub size_pruned: u64,
    /// `(a, k)` pairs too slow to sign at the least grinding any target sum asks.
    pub sign_pruned: u64,
    /// `(a, k)` pairs whose target sums were scanned.
    pub swept: u64,
    /// Points meeting every budget.
    pub feasible: u64,
    pub costed: u64,
    /// Parameter tuples that came out feasible, one row each.
    pub rows: u64,
    /// Rows dropped as worse than everything kept.
    pub rows_dropped: u64,
    pub seconds: f64,
}

impl Stats {
    fn add(&mut self, o: &Self) {
        self.grid += o.grid;
        self.keygen_pruned += o.keygen_pruned;
        self.insecure += o.insecure;
        self.size_pruned += o.size_pruned;
        self.sign_pruned += o.sign_pruned;
        self.swept += o.swept;
        self.feasible += o.feasible;
        self.costed += o.costed;
        self.rows += o.rows;
        self.rows_dropped += o.rows_dropped;
    }
}

impl std::fmt::Display for Stats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "grid {} (scheme, h, d, top WOTS, lower WOTS) tuples, {} over keygen; \
             then {} (a, k) pairs insecure, {} over size, {} over signing; \
             {} target-sum ranges swept, {} points feasible over {} parameter tuples ({} dropped as worse than \
             everything kept); {} parameter sets costed in {:.1}s",
            self.grid,
            self.keygen_pruned,
            self.insecure,
            self.size_pruned,
            self.sign_pruned,
            self.swept,
            self.feasible,
            self.rows,
            self.rows_dropped,
            self.costed,
            self.seconds
        )
    }
}

fn params(g: &Grid, scheme: Scheme, a: u64, k: u64) -> Params {
    Params {
        scheme,
        a,
        k,
        n: g.n,
        cache_height: g.cache_height,
        cache_level_only: g.cache_level_only,
    }
}

/// How much verification a grinding budget buys, for one hypertree.
///
/// Every unit of target sum removes exactly one chain step from verification,
/// whatever layer it is on, and costs that layer's grinding. So the best
/// allocation maximises `swn_top + (d-1) * swn_lower` against the trials the
/// signing budget leaves. Both layer groups have a convex increasing cost in
/// their own sum, since the digit-sum count is log-concave, so the frontier of
/// the pair is the greedy merge of their marginal costs, walked here once per
/// hypertree rather than once per `(a, k)`.
struct Grinding {
    /// `(trials, gain, top sum, lower sum)`, by increasing trials.
    frontier: Vec<(u64, u64, u64, u64)>,
}

/// Frontier points kept. The grinding rises fast enough that a budget runs out
/// long before this, so it is a bound on the allocation rather than a cap on
/// the answer.
const FRONTIER_MAX: usize = 4096;

impl Grinding {
    fn build(p: &Params, ht: &Hypertree, nu: &mut NuCache, cap: u64) -> Option<Self> {
        let (top, low) = (ht.top(), ht.layers().last()?);
        let m = ht.depth() - 1;
        let (top_l, low_l) = (top.chains(p.n, p.scheme)?, low.chains(p.n, p.scheme)?);
        let (top_tab, low_tab) = nu.pair((top_l, top.w()), (low_l, low.w()));
        let (top_max, low_max) = (top_tab.max_swn(), low_tab.max_swn());
        let (mut ts, mut ls) = (top_max / 2, low_max / 2);
        let cost = |ts: u64, ls: u64| top_tab.trials(ts).saturating_add(low_tab.trials(ls).saturating_mul(m));
        let mut frontier = vec![(cost(ts, ls), ts + m * ls, ts, ls)];
        while frontier.last()?.0 <= cap && frontier.len() < FRONTIER_MAX && (ts < top_max || (m > 0 && ls < low_max)) {
            // whichever next step buys its gain most cheaply
            let up_top = (ts < top_max).then(|| cost(ts + 1, ls));
            let up_low = (m > 0 && ls < low_max).then(|| cost(ts, ls + 1));
            let take_top = match (up_top, up_low) {
                (Some(t), Some(l)) => (t - frontier.last()?.0) <= (l - frontier.last()?.0) / m.max(1),
                (Some(_), None) => true,
                (None, Some(_)) => false,
                (None, None) => break,
            };
            if take_top {
                ts += 1;
            } else {
                ls += 1;
            }
            frontier.push((cost(ts, ls), ts + m * ls, ts, ls));
        }
        Some(Self { frontier })
    }

    /// The cheapest-verifying allocation that grinds at most `trials`.
    ///
    /// The frontier rises in both cost and gain, so this is the last entry
    /// within budget.
    fn best(&self, trials: u64) -> (u64, u64, u64) {
        let i = self.frontier.partition_point(|&(cost, ..)| cost <= trials);
        match i.checked_sub(1).and_then(|i| self.frontier.get(i)) {
            Some(&(_, gain, ts, ls)) => (gain, ts, ls),
            None => (0, 0, 0),
        }
    }
}

/// One hypertree candidate, costed and with its grinding frontier.
struct Tree {
    hyper: crate::params::HyperCost,
    grinding: Option<Grinding>,
}

/// Every feasible parameter set, ordered by verification cost.
///
/// One row per parameter tuple, carrying the target sums that verified cheapest
/// for it. Rows are what gets printed; the comparison behind each one saw every
/// target sum.
pub fn search(b: &Budgets, g: &Grid, st: &mut Stats) -> Vec<Candidate> {
    use rayon::prelude::*;
    let started = Instant::now();
    let sec = SecurityTable::filled(b.q_s, b.security, g.n, g.h.hi as u32, g.k.hi, g.a.hi);
    // The (scheme, WOTS instance) tasks are independent, and there are hundreds
    // of them once the top layer's instance is searched separately.
    let tasks: Vec<(Scheme, (Wots, Wots))> = g
        .schemes
        .iter()
        .flat_map(|&scheme| wots_instances(g, scheme).into_iter().map(move |w| (scheme, w)))
        .collect();
    let (rows, stats) = tasks
        .par_iter()
        .map(|&(scheme, wots)| {
            let mut st = Stats::default();
            let rows = one_task(b, g, &sec, scheme, wots, &mut st);
            (rows, st)
        })
        .reduce(
            || (Vec::new(), Stats::default()),
            |(mut rows, mut acc), (more, st)| {
                rows.extend(more);
                acc.add(&st);
                if rows.len() >= ROWS_CAP {
                    sort_rows(&mut rows, b);
                    rows.truncate(ROWS_KEPT);
                    acc.rows_dropped += (ROWS_CAP - ROWS_KEPT) as u64;
                }
                (rows, acc)
            },
        );
    let mut rows = rows;
    *st = stats;
    st.seconds = started.elapsed().as_secs_f64();
    sort_rows(&mut rows, b);
    rows
}

/// One `(scheme, WOTS instances)` task: everything else enumerated under it.
fn one_task(
    b: &Budgets,
    g: &Grid,
    sec: &SecurityTable,
    scheme: Scheme,
    wots: (Wots, Wots),
    st: &mut Stats,
) -> Vec<Candidate> {
    let mut nu = NuCache::new(g.n);
    let mut rows: Vec<Candidate> = Vec::new();
    // The FORS side depends on (scheme, a, k) alone, and every hypertree asks
    // for the same ones.
    let mut fors_of: std::collections::HashMap<(u64, u64), Option<Fors>> = Default::default();

    for h in g.h.iter() {
        for d in g.d.within(h) {
            st.grid += 1;
            let tops: Vec<u64> = match (g.hypertree, g.h_top) {
                (Some(ht), _) => vec![ht.top().height()],
                (None, None) => vec![h / d.max(1)],
                (None, Some(span)) => span.within((h + 1).saturating_sub(d)).collect(),
            };
            // Cost the hypertrees once: they need no a or k, and the keygen
            // budget alone usually settles the question.
            let probe = params(g, scheme, g.a.lo, if scheme.fors_c() { 2 } else { 1 });
            let mut trees = Vec::new();
            for h_top in tops {
                let Some(ht) = build(g, wots, h, d, h_top) else {
                    continue;
                };
                let Some(hyper) = crate::params::hyper_cost(&probe, &ht, &mut nu) else {
                    continue;
                };
                st.costed += 1;
                if b.of(hyper.keygen) > b.max_keygen() || hyper.sig_bytes > b.max_size() {
                    continue;
                }
                let grinding = (scheme.wots_c() && matches!(g.sums, Sums::Sweep))
                    .then(|| Grinding::build(&probe, &ht, &mut nu, b.max_sign()))
                    .flatten();
                trees.push(Tree { hyper, grinding });
            }
            if trees.is_empty() {
                st.keygen_pruned += 1;
                continue;
            }
            let smallest = trees.iter().map(|t| t.hyper.sig_bytes).min().unwrap_or(u64::MAX);
            for a in g.a.iter() {
                for k in g.k.iter() {
                    if !sec.is_secure(h as u32, k, a) {
                        st.insecure += 1;
                        continue;
                    }
                    let p = params(g, scheme, a, k);
                    let fors = *fors_of.entry((a, k)).or_insert_with(|| Fors::new(&p));
                    let Some(fors) = fors else { continue };
                    // the signature grows with k, so once it overruns there is
                    // no larger k
                    if fors.sig_bytes + smallest > b.max_size() {
                        st.size_pruned += 1;
                        break;
                    }
                    let mut best: Option<Costs> = None;
                    for tree in &trees {
                        let Some(c) = fit(b, &p, tree, &fors, &mut nu, st) else {
                            continue;
                        };
                        if best.is_none_or(|old| b.of(c.verify) < b.of(old.verify)) {
                            best = Some(c);
                        }
                    }
                    if let Some(costs) = best {
                        st.rows += 1;
                        rows.push(Candidate { params: p, costs });
                        if rows.len() >= ROWS_CAP {
                            sort_rows(&mut rows, b);
                            rows.truncate(ROWS_KEPT);
                            st.rows_dropped += (ROWS_CAP - ROWS_KEPT) as u64;
                        }
                    }
                }
            }
        }
    }
    rows
}

/// This hypertree with this FORS side, at the target sums that verify cheapest
/// within the budgets, or `None` if nothing fits.
fn fit(b: &Budgets, p: &Params, tree: &Tree, fors: &Fors, nu: &mut NuCache, st: &mut Stats) -> Option<Costs> {
    let at_mean = assemble(p, &tree.hyper, fors);
    if at_mean.sig_bytes > b.max_size() {
        st.size_pruned += 1;
        return None;
    }
    // the mean grinds least, so it settles whether any sums fit at all
    if !b.fits(&at_mean) {
        st.sign_pruned += 1;
        return None;
    }
    st.feasible += 1;
    let Some(grinding) = tree.grinding.as_ref() else {
        return Some(at_mean);
    };
    st.swept += 1;
    // What the signing budget leaves for grinding, in counter trials.
    let per_trial = b.of(Cost::new(1, p.blocks().chain_step_with_counter())).max(1);
    let fixed = b.of(at_mean.sign) - b.of(at_mean.wots_c_grinding);
    let (gain, top_swn, low_swn) = grinding.best(b.max_sign().saturating_sub(fixed) / per_trial);
    if gain == 0 {
        return Some(at_mean);
    }
    let ht = tree.hyper.hypertree;
    let layers: Option<Vec<Layer>> = ht
        .layers()
        .enumerate()
        .map(|(i, x)| x.with_swn(Some(if i == 0 { top_swn } else { low_swn })))
        .collect();
    let chosen = Hypertree::new(&layers?)?;
    // the frontier says what it costs; the model says what it is
    let hyper = crate::params::hyper_cost(p, &chosen, nu)?;
    let costs = assemble(p, &hyper, fors);
    st.costed += 1;
    if b.fits(&costs) && b.of(costs.verify) < b.of(at_mean.verify) {
        st.feasible += 1;
        return Some(costs);
    }
    Some(at_mean)
}

/// One WOTS instance's searched parameters: `(w, dropped_chains)`.
pub type Wots = (u64, u64);

/// The `(top WOTS, lower WOTS)` pairs to try: one pair unless `split_wots`.
fn wots_instances(g: &Grid, scheme: Scheme) -> Vec<(Wots, Wots)> {
    if g.hypertree.is_some() {
        return vec![((0, 0), (0, 0))]; // ignored: `build` returns the given tree
    }
    let mut single = Vec::new();
    for &bits in &g.chain_bits {
        let w = 1u64 << bits;
        let range = if scheme.wots_c() {
            g.dropped.within((8 * g.n / bits).saturating_sub(1))
        } else {
            0..=0
        };
        for dropped in range {
            single.push((w, dropped));
        }
    }
    if !g.split_wots {
        return single.iter().map(|&x| (x, x)).collect();
    }
    single
        .iter()
        .flat_map(|&t| single.iter().map(move |&l| (t, l)))
        .collect()
}

fn build(g: &Grid, wots: (Wots, Wots), h: u64, d: u64, h_top: u64) -> Option<Hypertree> {
    if let Some(ht) = g.hypertree {
        return (ht.height() == h && ht.depth() == d).then_some(ht);
    }
    let ((tw, td), (lw, ld)) = wots;
    let sums = match g.sums {
        Sums::Pinned(s) => Some(s),
        _ => None,
    };
    Hypertree::two_group(h, d, Layer::new(h_top, tw, td, sums)?, Layer::new(1, lw, ld, sums)?)
}

/// Rows kept before the list is trimmed back to `ROWS_KEPT`. The optimum is
/// unaffected: what gets dropped is worse than everything retained.
const ROWS_CAP: usize = 1 << 16;
const ROWS_KEPT: usize = 1 << 15;

fn sort_rows(rows: &mut [Candidate], b: &Budgets) {
    rows.sort_by_key(|c| (b.of(c.costs.verify), c.costs.sig_bytes, b.of(c.costs.sign)));
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
    let ht = c.costs.hypertree;
    let low = ht.layers().last().unwrap_or(ht.top());
    let at = [
        ("h", ht.height(), g.h.lo, g.h.hi, "H_MAX"),
        ("d", ht.depth(), g.d.lo, g.d.hi, "D_MAX"),
        ("a", c.params.a, g.a.lo, g.a.hi, "A_MAX"),
        ("k", c.params.k, g.k.lo, g.k.hi, "K_MAX"),
        ("chain_bits", ht.top().chain_bits(), bits.lo, bits.hi, "CHAIN_BITS_MAX"),
        ("chain_bits", low.chain_bits(), bits.lo, bits.hi, "CHAIN_BITS_MAX"),
        (
            "dropped_chains",
            ht.top().dropped_chains(),
            0,
            g.dropped.hi,
            "DROPPED_MAX",
        ),
        ("dropped_chains", low.dropped_chains(), 0, g.dropped.hi, "DROPPED_MAX"),
    ];
    let mut out: Vec<String> = at
        .iter()
        .filter(|(_, v, floor, limit, _)| limit > floor && *v + 1 >= *limit)
        .map(|(axis, v, _, limit, what)| {
            let where_ = if v >= limit { "at" } else { "one step below" };
            format!("{axis} = {v} is {where_} the top of the searched range ({limit}): raise {what} in src/search.rs and rerun")
        })
        .collect();
    out.dedup();
    out
}

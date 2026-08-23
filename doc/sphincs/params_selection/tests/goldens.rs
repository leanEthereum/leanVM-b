//! Everything this crate computes, pinned against something outside it.
//!
//! Sources, in descending order of authority:
//!
//!   * `tests/fixtures.json` of BlockstreamResearch/SPHINCS-Parameters, frozen
//!     there from real `sage costs.sage` runs, under both hash conventions;
//!   * Tables 1 and 2 of the report itself, for the columns it publishes;
//!   * `security.sage`, whose 100-digit decimal sum the log2-space f64 port here
//!     has to reproduce;
//!   * `doc/xmss/main.tex`, for the digest-cut geometry;
//!   * for the search, a naive oracle in this crate that skips nothing.

use sphincs_params::cost::{Blocks, Encoding, NuTable, Scheme};
use sphincs_params::params::{Fors, Hypertree, Layer, Params, assemble, costs, hyper_cost};
use sphincs_params::search::{Budgets, Grid, LEVEL1_BITS, Span, Stats, search};
use sphincs_params::security::{forgery_exponent, security_bits};

fn params(scheme: Scheme, a: u64, k: u64) -> Params {
    Params {
        scheme,
        a,
        k,
        n: 16,
        cache_height: None,
        cache_level_only: false,
    }
}

/// One parameter set the way the report writes them: one WOTS instance for the
/// whole hypertree, the height split evenly.
fn uniform(scheme: Scheme, h: u64, d: u64, a: u64, k: u64, w: u64, swn: Option<u64>) -> (Params, Hypertree) {
    (
        params(scheme, a, k),
        Hypertree::uniform(h, d, None, w, 0, swn).expect("consistent"),
    )
}

/// `(scheme, h, d, k, a, w, S_wn)` and the `(size, keygen, sign, verify,
/// verify_worst)` it must produce, sizes in bytes and costs in compressions.
type Fixture = (Scheme, u64, u64, u64, u64, u64, Option<u64>, [u64; 5]);

/// From fixtures.json under the cached convention.
const FIXTURES_CACHED: [Fixture; 7] = [
    (
        Scheme::Spx,
        63,
        7,
        14,
        12,
        16,
        None,
        [7856, 292351, 2218483, 2155, 3891],
    ),
    (
        Scheme::Wc,
        44,
        4,
        8,
        16,
        16,
        Some(240),
        [4960, 1069055, 5849347, 1185, 1185],
    ),
    (
        Scheme::Wc,
        40,
        5,
        11,
        14,
        256,
        Some(2040),
        [4596, 1050111, 5794969, 10441, 10441],
    ),
    (
        Scheme::Wc,
        40,
        5,
        11,
        14,
        256,
        Some(2840),
        [4596, 1050111, 5941944, 6441, 6441],
    ),
    (
        Scheme::WcFc,
        44,
        4,
        8,
        16,
        16,
        Some(240),
        [4688, 1069055, 5914880, 1168, 1168],
    ),
    (
        Scheme::WcFc,
        40,
        5,
        11,
        14,
        256,
        Some(2040),
        [4356, 1050111, 5811349, 10425, 10425],
    ),
    (
        Scheme::WcFc,
        20,
        2,
        10,
        15,
        256,
        Some(2040),
        [3160, 4200447, 9418194, 4261, 4261],
    ),
];

#[test]
fn matches_the_sage_fixtures() {
    for &(scheme, h, d, k, a, w, swn, want) in &FIXTURES_CACHED {
        let (p, ht) = uniform(scheme, h, d, a, k, w, swn);
        let c = costs(p, &ht).expect("consistent parameters");
        let got = [
            c.sig_bytes,
            c.keygen.compressions,
            c.sign_cold.compressions,
            c.verify.compressions,
            c.verify_worst.compressions,
        ];
        assert_eq!(got, want, "{} h={h} d={d} k={k} a={a} w={w}", scheme.label());
    }
}

/// The compression rule: one call per 64 bytes of hash input, the input being
/// the n-byte public parameter, the n-byte tweak, and the payload.
#[test]
fn one_compression_per_64_bytes() {
    let b = Blocks::new(16);
    assert_eq!(b.merkle_node(), 1, "two 16-byte children fill one block exactly");
    assert_eq!(b.chain_step(), 1);
    assert_eq!(b.chain_step_with_counter(), 1);
    assert_eq!(b.prf(), 1);
    // doc/xmss's IncEnc: 32 B of prefix, a 32 B message, 24 B of randomness
    // and 8 B of padding
    assert_eq!(b.message_hash(), 2);
    assert_eq!(b.message_prf(), 2);
    for m in 1..200 {
        assert_eq!(b.compress(m), (32 + 16 * m).div_ceil(64), "compressing {m} hash values");
    }
    // And it is the same function as the report's SHA-2 layout with the PK.seed
    // midstate cached, ceil((22*8 + 128m + 65) / 512), which is why its
    // published compression counts still pin this model.
    for m in 1..4000u64 {
        assert_eq!(
            b.compress(m),
            (22 * 8 + 128 * m + 65).div_ceil(512),
            "against the report's layout at m={m}"
        );
    }
}

/// Tables 1 and 2 of the report, WOTS/FORS rows only: `(scheme, h, d, a, k, w,
/// S_wn)` then `(SigVer, SigTime/1e4 to three figures, Exp. Search)` in hashes. The tables' Sig (B) column is 16
/// bytes above what the current scripts compute (7856 for SLH-DSA-128s is the
/// FIPS 205 value, against the table's 7872); the fixtures above are the
/// authority there, and the tables predate them.
type ReportRow = (Scheme, u64, u64, u64, u64, u64, Option<u64>, u64, f64, Option<u64>);

const REPORT_TABLE: [ReportRow; 18] = [
    (Scheme::Spx, 63, 7, 12, 14, 16, None, 2088, 219.0, Some(0)),
    (Scheme::Wc, 44, 4, 16, 8, 16, Some(240), 1150, 578.0, Some(264)),
    (Scheme::Wc, 44, 4, 16, 8, 16, Some(304), 894, 579.0, Some(5344)),
    (Scheme::Wc, 44, 4, 16, 8, 256, Some(2040), 8350, 3515.0, Some(2996)),
    (Scheme::Wc, 40, 5, 14, 11, 256, Some(2040), 10417, 579.0, Some(3745)),
    (Scheme::Wc, 40, 5, 14, 11, 256, Some(2840), 6417, 594.0, None),
    (Scheme::WcFc, 44, 4, 16, 8, 16, Some(240), 1133, 572.0, None),
    (Scheme::WcFc, 40, 5, 14, 11, 256, Some(2040), 10402, 577.0, Some(36513)),
    (Scheme::Wc, 36, 3, 14, 9, 16, Some(240), 899, 676.0, Some(198)),
    (Scheme::Wc, 33, 3, 15, 9, 16, Some(304), 713, 405.0, Some(4008)),
    (Scheme::Wc, 32, 4, 14, 10, 256, Some(2840), 5152, 481.0, None),
    (Scheme::WcFc, 33, 3, 15, 9, 16, Some(240), 889, 401.0, Some(65734)),
    (Scheme::WcFc, 32, 4, 14, 10, 256, Some(2040), 8337, 467.0, Some(35764)),
    (Scheme::Wc, 24, 2, 16, 8, 16, Some(240), 646, 578.0, None),
    (Scheme::Wc, 24, 2, 16, 8, 256, Some(2040), 4246, 3515.0, None),
    (Scheme::WcFc, 24, 2, 16, 8, 16, Some(240), 629, 572.0, None),
    (Scheme::Wc, 20, 2, 15, 10, 256, Some(2040), 4266, 938.0, None),
    (Scheme::WcFc, 20, 2, 15, 10, 256, Some(2040), 4250, 934.0, None),
];

#[test]
fn matches_the_report_tables() {
    for (scheme, h, d, a, k, w, swn, sigver, sigtime_e4, search) in REPORT_TABLE {
        let (p, ht) = uniform(scheme, h, d, a, k, w, swn);
        let c = costs(p, &ht).expect("consistent parameters");
        let tag = format!("{} h={h} d={d} a={a} k={k} w={w} S={swn:?}", scheme.label());
        assert_eq!(c.verify.hashes, sigver, "SigVer {tag}");
        let got = c.sign_cold.hashes as f64 / 1e4;
        assert!(
            (got - sigtime_e4).abs() < 0.55,
            "SigTime {tag}: got {got:.2}e4, want {sigtime_e4}e4"
        );
        if let Some(want) = search {
            assert_eq!(c.grinding().hashes, want, "Exp. Search {tag}");
        }
    }
}

/// `(w, n, dropped)` -> `(chain_bits, pinned_bits, chains, mean S_wn)`.
/// `(8, 16, 0)` is the `doc/xmss/main.tex` instance: 2 of 128 bits pinned,
/// v = 42 chains. For the w the report uses, chain_bits divides 128 and nothing
/// is pinned.
const ENCODINGS: [(u64, u64, u64, [u64; 4]); 10] = [
    (8, 16, 0, [3, 2, 42, 147]),
    (8, 16, 1, [3, 5, 41, 143]),
    (8, 16, 2, [3, 8, 40, 140]),
    (16, 16, 0, [4, 0, 32, 240]),
    (16, 16, 1, [4, 4, 31, 232]),
    (32, 16, 0, [5, 3, 25, 387]),
    (256, 16, 0, [8, 0, 16, 2040]),
    (4096, 16, 0, [12, 8, 10, 20475]),
    (2, 16, 0, [1, 0, 128, 64]),
    (8, 32, 0, [3, 1, 85, 297]),
];

#[test]
fn digest_cut_follows_doc_xmss() {
    for (w, n, dropped, want) in ENCODINGS {
        let e = Encoding::new(w, n, dropped).expect("a chain is left");
        let got = [e.chain_bits, e.pinned_bits, e.chains, e.default_swn()];
        assert_eq!(got, want, "encoding w={w} n={n} dropped={dropped}");
    }
    assert!(
        Encoding::new(8, 16, 42).is_none(),
        "dropping every chain leaves nothing to sign"
    );
    assert!(Encoding::new(24, 16, 0).is_none(), "w must be a power of two");
}

/// `(l, w, swn)` -> `(nu, trials)`, from the python port's exact bignum values.
#[test]
fn digit_sum_counts_are_exact() {
    let cases: [(u64, u64, u64, u128, u64); 4] = [
        (42, 8, 195, 11539185377238682781344003244544752, 29490),
        (42, 8, 147, 2277086601665419901777619378707106160, 150),
        (16, 256, 2040, 454918678781617793203528879683071744, 749),
        (128, 2, 64, 23951146041928082866135587776380551750, 15),
    ];
    for (l, w, swn, nu, trials) in cases {
        let t = NuTable::new(l, w, 128);
        assert_eq!(t.nu(swn), nu, "nu(l={l}, w={w}, swn={swn})");
        assert_eq!(t.trials(swn), trials, "trials(l={l}, w={w}, swn={swn})");
    }
    // The count is symmetric and the totals check out: nothing is lost off
    // either end of the table.
    let t = NuTable::new(32, 16, 128);
    for s in 0..=240 {
        assert_eq!(t.nu(s), t.nu(480 - s), "the digit-sum count is symmetric at s={s}");
    }
    assert_eq!(t.min_trials(), t.trials(240), "the cheapest grinding is at the mean");
    assert_eq!(t.nu(240), 5181241160064611531897369560287267312);
}

/// `(lifetime, h, k, a)` -> forgery exponent, from `security.sage` via the
/// python port's 100-digit decimal sum. The f64 log-space version here has to
/// land within a thousandth of a bit.
const SECURITY: [(i32, u32, u64, u64, f64); 13] = [
    (64, 63, 14, 12, 133.749299297),
    (40, 44, 8, 16, 128.283950447),
    (40, 40, 11, 14, 134.630384667),
    (30, 32, 10, 14, 131.514752565),
    (20, 24, 8, 16, 128.283952741),
    (30, 33, 9, 15, 131.399050971),
    (20, 20, 10, 15, 133.177627134),
    (40, 42, 9, 15, 128.338475839),
    (30, 30, 9, 16, 129.632278830),
    (20, 18, 19, 10, 129.282431578),
    (64, 63, 35, 6, 104.414518339),
    (40, 45, 8, 16, 130.423562374),
    (30, 36, 9, 14, 129.476084807),
];

#[test]
fn security_matches_the_decimal_sum() {
    for (log2_q_s, h, k, a, want) in SECURITY {
        let q_s = 2f64.powi(log2_q_s);
        let got = forgery_exponent(q_s, h, k, a).expect("converges");
        assert!(
            (got - want).abs() < 1e-3,
            "forgery exponent at q_s=2^{log2_q_s} h={h} k={k} a={a}: got {got:.9}, want {want:.9}"
        );
    }
    // The preimage bound caps the reported level, and 128 bits is what every
    // parameter set in the report reaches.
    assert_eq!(security_bits(2f64.powi(64), 63, 14, 12, 16), 128.0);
    assert_eq!(security_bits(2f64.powi(30), 32, 10, 14, 16), 128.0);
    // n = 32 lifts the cap, so the forgery term shows through.
    assert!((security_bits(2f64.powi(30), 32, 10, 14, 32) - 131.514752565).abs() < 1e-3);
    // A lifetime far past the hypertree has nothing left to quantify.
    assert!(forgery_exponent(2f64.powi(40), 20, 10, 15).is_none());
    assert_eq!(security_bits(2f64.powi(40), 20, 10, 15, 16), 0.0);
}

#[test]
fn secure_k_form_an_up_set() {
    // Relied on nowhere in the search, which tests every k, but it is the
    // property that makes "the smallest secure k" a meaningful phrase at all.
    for (h, a) in [(20u32, 10u64), (24, 12), (30, 14)] {
        let flags: Vec<bool> = (1..=32)
            .map(|k| security_bits(2f64.powi(20), h, k, a, 16) >= LEVEL1_BITS)
            .collect();
        let mut sorted = flags.clone();
        sorted.sort_unstable();
        assert_eq!(flags, sorted, "secure k are an up-set at h={h} a={a}");
    }
}

#[test]
fn half_top_cache_is_a_saving_and_reduces_to_the_full_tree() {
    let (p, ht) = uniform(Scheme::WcFc, 40, 5, 14, 11, 256, None);
    let c = costs(p, &ht).unwrap();
    assert!(c.sign.hashes < c.sign_cold.hashes);
    // caching at the leaves is caching the whole tree: nothing left to rebuild
    let whole = Params {
        cache_height: Some(0),
        ..p
    };
    assert!(costs(whole, &ht).unwrap().sign.hashes < c.sign.hashes);
    // caching only the root is caching nothing, so signing goes cold
    let none = Params {
        cache_height: Some(ht.top().height()),
        ..p
    };
    assert_eq!(costs(none, &ht).unwrap().sign.hashes, c.sign_cold.hashes);
}

#[test]
fn a_taller_top_layer_is_free_on_size_and_verification() {
    // The whole point of per-layer heights: the signature carries h
    // authentication nodes and the verifier walks them however the layers
    // divide h, so only the signer's costs move.
    let p = params(Scheme::WcFc, 14, 11);
    let flat = Hypertree::uniform(40, 5, Some(8), 256, 0, None).unwrap();
    let tall = Hypertree::uniform(40, 5, Some(15), 256, 0, None).unwrap();
    let (u, t) = (costs(p, &flat).unwrap(), costs(p, &tall).unwrap());
    assert_eq!(flat.height(), 40);
    assert_eq!(tall.height(), 40);
    assert_eq!(
        (t.sig_bytes, t.verify),
        (u.sig_bytes, u.verify),
        "size and verification do not move"
    );
    assert!(
        t.keygen.hashes > u.keygen.hashes,
        "a taller top tree costs more to generate"
    );
    assert!(t.sign_cold.hashes > u.sign_cold.hashes, "and more to sign cold");
    assert!(
        t.sign.hashes < u.sign.hashes,
        "but less with the cache, which is the point"
    );
    // the lower layers come out as equal as they go
    let lower: Vec<u64> = tall.layers().skip(1).map(|x| x.height()).collect();
    assert!(
        lower.iter().max().unwrap() - lower.iter().min().unwrap() <= 1,
        "{lower:?}"
    );
}

/// Every way of splitting `h` over `d` layers, top first.
fn compositions(h: u64, d: u64) -> Vec<Vec<u64>> {
    if d == 1 {
        return vec![vec![h]];
    }
    (1..=h.saturating_sub(d - 1))
        .flat_map(|first| {
            compositions(h - first, d - 1).into_iter().map(move |rest| {
                let mut out = vec![first];
                out.extend(rest);
                out
            })
        })
        .collect()
}

#[test]
fn any_hypertree_can_be_costed() {
    let p = params(Scheme::WcFc, 14, 11);
    // heights and WOTS parameters both varying, layer by layer
    let mixed = Hypertree::new(&[
        Layer::new(11, 256, 0, Some(2040)).unwrap(),
        Layer::new(5, 16, 1, None).unwrap(),
        Layer::new(7, 4, 0, None).unwrap(),
        Layer::new(3, 2, 0, None).unwrap(),
    ])
    .unwrap();
    assert_eq!(mixed.height(), 26);
    assert_eq!(mixed.depth(), 4);
    assert!(!mixed.one_wots());
    assert_eq!(mixed.heights(), "11 + 5 + 7 + 3");
    let c = costs(p, &mixed).unwrap();
    // the signature carries one WOTS signature per layer, at that layer's l
    let chains: u64 = mixed.layers().map(|x| x.chains(16, Scheme::WcFc).unwrap()).sum();
    let fors = Fors::new(&p).unwrap();
    assert_eq!(c.sig_bytes, fors.sig_bytes + 26 * 16 + chains * 16 + 4 * 4);
    // a hypertree of one layer is an ordinary XMSS tree
    let single = Hypertree::new(&[Layer::new(20, 16, 0, None).unwrap()]).unwrap();
    assert_eq!(single.depth(), 1);
    assert!(costs(p, &single).is_some());
    assert!(Hypertree::new(&[]).is_none());
    assert!(Layer::new(0, 16, 0, None).is_none(), "every layer needs a level");
    assert!(Layer::new(64, 16, 0, None).is_none(), "2^height has to be countable");
    assert!(Layer::new(8, 24, 0, None).is_none(), "w is a power of two");
}

/// The search tries two WOTS instances, one for the top layer and one for the
/// rest, and this is what that costs against giving every layer its own.
#[test]
fn two_groups_against_every_per_layer_assignment() {
    let p = params(Scheme::WcFc, 10, 12);
    let fors = Fors::new(&p).unwrap();
    let mut nu = sphincs_params::cost::NuCache::new(16);
    let configs: Vec<(u64, u64)> = [2, 4, 16].iter().flat_map(|&w| [0, 1].map(move |dr| (w, dr))).collect();
    let mut worst_gap = 0.0f64;
    for (h, d) in [(8, 2), (11, 2), (9, 3), (12, 3)] {
        // the budgets have to bind, or every assignment is feasible and the
        // comparison says nothing
        let (max_size, max_sign) = (5_000, 4_000_000);
        let mut best_any = u64::MAX;
        let mut best_two_group = u64::MAX;
        for heights in compositions(h, d) {
            for assignment in 0..configs.len().pow(d as u32) {
                let layers: Option<Vec<Layer>> = heights
                    .iter()
                    .enumerate()
                    .map(|(i, &height)| {
                        let (w, dr) = configs[assignment / configs.len().pow(i as u32) % configs.len()];
                        Layer::new(height, w, dr, None)
                    })
                    .collect();
                let Some(layers) = layers else { continue };
                let Some(ht) = Hypertree::new(&layers) else { continue };
                let Some(hyper) = hyper_cost(&p, &ht, &mut nu) else {
                    continue;
                };
                let c = assemble(&p, &hyper, &fors);
                if c.sig_bytes > max_size || c.sign.compressions > max_sign {
                    continue;
                }
                best_any = best_any.min(c.verify.compressions);
                // is this assignment inside the two-group family?
                let top = layers[0];
                let low = layers[layers.len() - 1];
                let even = Hypertree::two_group(h, d, top, low);
                if even == Some(ht) {
                    best_two_group = best_two_group.min(c.verify.compressions);
                }
            }
        }
        assert!(best_any < u64::MAX, "nothing feasible at h={h} d={d}");
        assert!(best_two_group >= best_any, "the family cannot beat the whole space");
        let gap = best_two_group as f64 / best_any as f64 - 1.0;
        worst_gap = worst_gap.max(gap);
        println!(
            "h={h} d={d}: two groups {best_two_group}, every assignment {best_any} ({:.1}% gap)",
            100.0 * gap
        );
    }
    // What the two-group restriction costs. Raise this only with a note saying
    // which case moved and why.
    assert!(
        worst_gap <= 0.0,
        "the two-group family lost {:.1}% somewhere",
        100.0 * worst_gap
    );
}

fn budgets(log2_q_s: i32, keygen: u64, sign: u64, size: u64) -> Budgets {
    Budgets {
        q_s: 2f64.powi(log2_q_s),
        keygen: Some(keygen),
        sign: Some(sign),
        size: Some(size),
        security: LEVEL1_BITS,
    }
}

#[test]
fn search_finds_and_improves_on_the_reports_bold_row() {
    // Budgets near the report's 2^40 numbers, on its grid (w in {16, 256}, no
    // chain dropping). Its own choice has to come out feasible, and the search
    // has to do at least as well: it spends what is left of the signing budget
    // raising the target sums, which the report's row does not.
    let b = budgets(40, 1_100_000, 6_000_000, 4_400);
    let g = Grid {
        chain_bits: vec![4, 8],
        dropped: Span::pin(0),
        ..Default::default()
    };
    let mut st = Stats::default();
    let found = search(&b, &g, &mut st);
    let row = found
        .iter()
        .find(|c| {
            let ht = c.costs.hypertree;
            (c.params.a, c.params.k, ht.height(), ht.depth(), ht.top().w()) == (14, 11, 40, 5, 256)
        })
        .expect("the report's bold row is feasible under its own budgets");
    let swn = row.costs.hypertree.top().swn().unwrap();
    assert!(swn > 2040, "the report's row grinds less than the budget allows");
    assert!(
        row.costs.verify.hashes < 10402,
        "so it can verify faster than the table's 10402 hashes"
    );
    assert!(
        found[0].costs.verify.compressions <= row.costs.verify.compressions,
        "and the winner is at least as cheap"
    );
}

#[test]
fn rejects_what_it_cannot_count_or_assemble() {
    let p = params(Scheme::WcFc, 14, 11);
    // 2^h has to be countable: without this the shift masks and a 2^64-leaf
    // tree reports the cost of a one-leaf tree
    assert!(Layer::new(64, 256, 0, None).is_none());
    assert!(Hypertree::uniform(64, 1, None, 256, 0, None).is_none());
    assert!(Hypertree::uniform(63, 1, None, 256, 0, None).is_some());
    // and the cost really does scale with the tree, so nothing wraps below that
    let small = costs(p, &Hypertree::uniform(40, 8, None, 256, 0, None).unwrap()).unwrap();
    let large = costs(p, &Hypertree::uniform(48, 8, None, 256, 0, None).unwrap()).unwrap();
    // twice the leaves in the top tree is twice the work plus the node joining
    // the two halves
    assert_eq!(large.keygen.hashes, small.keygen.hashes * 2 + 1);
    assert!(large.sign_cold.hashes > small.sign_cold.hashes);
    // FORS+C signs k-1 trees, so it needs two
    assert!(Fors::new(&Params { k: 1, ..p }).is_none());
    // every layer needs a level, and the heights have to add up
    assert!(Hypertree::uniform(2, 3, None, 256, 0, None).is_none());
    assert!(Hypertree::uniform(40, 5, Some(40), 256, 0, None).is_none());
    assert!(Hypertree::uniform(40, 5, Some(36), 256, 0, None).is_some());
    // the cache sits inside the top tree
    let deep = Params {
        cache_height: Some(99),
        ..p
    };
    assert!(costs(deep, &Hypertree::uniform(40, 5, None, 256, 0, None).unwrap()).is_none());
}

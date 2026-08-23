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
use sphincs_params::params::{Layers, Params, Profile, Skeleton, costs};
use sphincs_params::search::{Budgets, Grid, LEVEL1_BITS, Span, Stats, naive_search, search};
use sphincs_params::security::{forgery_exponent, security_bits};

fn params(scheme: Scheme, h: u64, d: u64, a: u64, k: u64, w: u64) -> Params {
    Params {
        scheme,
        h,
        d,
        h_top: None,
        a,
        k,
        w,
        n: 16,
        dropped_chains: 0,
        cache_height: None,
        cache_level_only: false,
    }
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
        let p = params(scheme, h, d, a, k, w);
        let c = costs(p, swn).expect("consistent parameters");
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
        let p = params(scheme, h, d, a, k, w);
        let c = costs(p, swn).expect("consistent parameters");
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
    let p = params(Scheme::WcFc, 40, 5, 14, 11, 256);
    let c = costs(p, None).unwrap();
    assert!(c.sign.hashes < c.sign_cold.hashes);
    // caching at the leaves is caching the whole tree: nothing left to rebuild
    let whole = Params {
        cache_height: Some(0),
        ..p
    };
    assert!(costs(whole, None).unwrap().sign.hashes < c.sign.hashes);
    // caching only the root is caching nothing, so signing goes cold
    let none = Params {
        cache_height: Some(p.profile().unwrap().h_top()),
        ..p
    };
    assert_eq!(costs(none, None).unwrap().sign.hashes, c.sign_cold.hashes);
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
fn search_agrees_with_a_naive_oracle() {
    // A grid small enough to sweep with nothing skipped at all.
    let b = budgets(20, 3_000_000, 10_000_000, 4_000);
    let g = Grid {
        schemes: vec![Scheme::Wc, Scheme::WcFc],
        h: Span::pin(20),
        a: Span::new(14, 16),
        k: Span::new(1, 14),
        chain_bits: vec![4],
        dropped: Span::new(0, 1),
        h_top: Some(Span::new(1, 20)),
        ..Default::default()
    };
    let mut st = Stats::default();
    let found = search(&b, &g, &mut st);
    let oracle = naive_search(&b, &g);
    assert!(!found.is_empty() && !oracle.is_empty());
    assert_eq!(
        found[0].costs.verify.hashes, oracle[0].costs.verify.hashes,
        "the oracle finds the same optimum"
    );
    assert_eq!(found[0].key(), oracle[0].key(), "and the same winner");
    // Every parameter tuple the oracle found feasible is in the search's output,
    // with the same best verification cost for that tuple.
    let mut want: std::collections::HashMap<_, u64> = Default::default();
    for c in &oracle {
        let e = want.entry(c.key()).or_insert(u64::MAX);
        *e = (*e).min(c.costs.verify.hashes);
    }
    let got: std::collections::HashMap<_, u64> = found.iter().map(|c| (c.key(), c.costs.verify.hashes)).collect();
    assert_eq!(got, want, "the search and the oracle agree tuple by tuple");
}

#[test]
fn search_finds_and_improves_on_the_reports_bold_row() {
    // Budgets near the report's 2^40 numbers, on its grid (w in {16, 256}, no
    // chain dropping). Its own choice has to come out feasible, and the search
    // has to do at least as well: it spends what is left of the signing budget
    // raising the target sum, which the report's row does not.
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
        .find(|c| c.key() == (Scheme::WcFc, 40, 5, 14, 11, 256, 0))
        .expect("the report's bold row is feasible under its own budgets");
    assert!(
        row.costs.swn.unwrap() > 2040,
        "the report's row grinds less than the budget allows"
    );
    assert!(
        row.costs.verify.hashes < 10402,
        "so it can verify faster than the table's 10402 hashes"
    );
    assert!(
        found[0].costs.verify.hashes <= row.costs.verify.hashes,
        "and the winner is at least as cheap"
    );
}

#[test]
fn a_taller_top_layer_is_free_on_size_and_verification() {
    // The whole point of per-layer heights: the signature carries h
    // authentication nodes and the verifier walks them however the layers
    // divide h, so only the signer's costs move.
    let uniform = Params {
        h_top: Some(8),
        ..params(Scheme::WcFc, 40, 5, 14, 11, 256)
    };
    let tall = Params {
        h_top: Some(15),
        ..uniform
    };
    let (u, t) = (costs(uniform, None).unwrap(), costs(tall, None).unwrap());
    assert_eq!(u.profile.total(), 40);
    assert_eq!(t.profile.total(), 40);
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
    assert!(t.sign.hashes < u.sign.hashes, "but less with it, which is the point");
    // the lower layers come out as equal as they go, never differing by more
    // than one level
    let p = t.profile;
    let lower: Vec<u64> = p.heights().skip(1).collect();
    let (lo, hi) = (lower.iter().min().unwrap(), lower.iter().max().unwrap());
    assert!(
        hi - lo <= 1,
        "the lower layers never differ by more than a level: {lower:?}"
    );
    assert_eq!(Profile::canonical(41, 5, Some(9)).unwrap().total(), 41);
    assert_eq!(Layers::new(&tall).unwrap().profile, t.profile);
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

/// The search only ever builds `Profile::canonical`, and this is why that is
/// not a restriction: for the same `(h, d, h_top)`, no other profile costs less
/// on anything.
#[test]
fn profile_shape_is_never_beaten() {
    let mut checked = 0;
    for (h, d) in [(12, 3), (14, 4), (9, 2), (16, 5), (20, 4)] {
        let p = Params {
            h,
            d,
            ..params(Scheme::WcFc, h, d, 10, 12, 16)
        };
        let sk = Skeleton::new(p).expect("consistent");
        for heights in compositions(h, d) {
            let Some(profile) = Profile::new(&heights) else {
                continue;
            };
            let Some(any) = Layers::from_profile(&p, profile) else {
                continue;
            };
            let canon = Layers::new(&Params {
                h_top: Some(heights[0]),
                ..p
            })
            .expect("same top height");
            let tag = format!("h={h} d={d} heights={heights:?}");
            // size and verification do not see the profile at all
            let (a, c) = (sk.finish(&any, 0, 0), sk.finish(&canon, 0, 0));
            assert_eq!(
                (a.sig_bytes, a.verify),
                (c.sig_bytes, c.verify),
                "size or verification moved: {tag}"
            );
            // keygen is the top tree, which they share
            assert_eq!(any.keygen, canon.keygen, "keygen moved: {tag}");
            // and the canonical split is the cheapest to sign, cached or cold
            assert!(
                canon.trees_cached.compressions <= any.trees_cached.compressions,
                "beaten on signing: {tag}"
            );
            assert!(
                canon.trees.compressions <= any.trees.compressions,
                "beaten on cold signing: {tag}"
            );
            checked += 1;
        }
    }
    assert!(checked > 2000, "only {checked} profiles checked");
}

/// A profile is expressible however uneven, and reads back as given.
#[test]
fn any_profile_can_be_costed() {
    let p = params(Scheme::WcFc, 26, 4, 14, 11, 256);
    let lopsided = Profile::new(&[11, 5, 7, 3]).expect("26 over 4 layers");
    assert_eq!(lopsided.total(), 26);
    assert_eq!(lopsided.h_top(), 11);
    assert_eq!(format!("{lopsided}"), "11 + 5 + 7 + 3");
    let lay = Layers::from_profile(&p, lopsided).expect("adds up to h over d layers");
    assert_eq!(lay.profile, lopsided);
    // and the canonical one with the same top is at least as cheap to sign
    let canon = Layers::new(&Params { h_top: Some(11), ..p }).unwrap();
    assert_eq!(format!("{}", canon.profile), "11 + 3 x 5");
    assert!(canon.trees_cached.compressions <= lay.trees_cached.compressions);
    // heights have to add up over the layers there are
    assert!(Layers::from_profile(&p, Profile::new(&[11, 5, 7, 4]).unwrap()).is_none());
    assert!(Layers::from_profile(&p, Profile::new(&[13, 13]).unwrap()).is_none());
    assert!(Profile::new(&[11, 0, 15]).is_none(), "every layer needs a level");
    assert!(Profile::new(&[64]).is_none(), "2^height has to be countable");
}

#[test]
fn skeleton_rejects_trees_that_do_not_fit_a_u64() {
    // 2^h' leaves has to be countable: without this the shift masks and a
    // 2^64-leaf tree reports the cost of a one-leaf tree.
    let p = params(Scheme::WcFc, 64, 1, 14, 11, 256);
    assert!(Skeleton::new(p).is_none());
    assert!(Skeleton::new(Params { h: 63, ..p }).is_some());
    assert!(Skeleton::new(Params { a: 64, ..p }).is_none());
    // and the cost really does scale with the tree, so nothing wraps below that
    let small = costs(Params { h: 40, d: 8, ..p }, None).unwrap();
    let large = costs(Params { h: 48, d: 8, ..p }, None).unwrap();
    // twice the leaves is twice the work plus the node joining the two halves
    assert_eq!(large.keygen.hashes, small.keygen.hashes * 2 + 1);
}

#[test]
fn skeleton_rejects_inconsistent_parameters() {
    let ok = params(Scheme::WcFc, 40, 5, 14, 11, 256);
    assert!(Skeleton::new(ok).is_some());
    // d need not divide h: the layers just come out within one of each other
    let uneven = Skeleton::new(Params { d: 3, ..ok }).expect("d need not divide h");
    assert_eq!(uneven.params.profile().unwrap().total(), 40);
    assert!(
        Skeleton::new(Params { h: 2, d: 3, ..ok }).is_none(),
        "every layer needs a level"
    );
    assert!(
        Skeleton::new(Params { h_top: Some(40), ..ok }).is_none(),
        "the lower layers need levels too"
    );
    assert!(
        Skeleton::new(Params { h_top: Some(36), ..ok }).is_some(),
        "but only one each"
    );
    assert!(
        Skeleton::new(Params { w: 24, ..ok }).is_none(),
        "w must be a power of two"
    );
    assert!(Skeleton::new(Params { k: 1, ..ok }).is_none(), "FORS+C signs k-1 trees");
    assert!(
        Skeleton::new(Params {
            scheme: Scheme::Spx,
            dropped_chains: 1,
            ..ok
        })
        .is_none(),
        "WOTS-TW has no counter"
    );
    assert!(
        Layers::new(&Params {
            cache_height: Some(99),
            ..ok
        })
        .is_none(),
        "the cache sits inside the top tree"
    );
}

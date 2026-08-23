//! Human-readable output.

use crate::cost::Cost;
use crate::params::{Costs, Layer, Params};
use crate::search::{Budgets, Candidate};
use crate::security::forgery_exponent;

/// A signature count, as a power of two when it is one.
pub fn signatures(q_s: f64) -> String {
    let log2 = q_s.log2();
    if (log2 - log2.round()).abs() < 1e-9 {
        return format!("2^{}", log2.round() as i64);
    }
    for (unit, div) in [
        ("E", 1e18),
        ("P", 1e15),
        ("T", 1e12),
        ("G", 1e9),
        ("M", 1e6),
        ("K", 1e3),
    ] {
        if q_s >= div {
            return format!("{:.3}{unit} (2^{log2:.1})", q_s / div);
        }
    }
    format!("{q_s:.0}")
}

pub fn si(x: u64) -> String {
    let f = x as f64;
    for (unit, div) in [("G", 1e9), ("M", 1e6), ("K", 1e3)] {
        if f >= div {
            return format!("{:.2}{unit}", f / div);
        }
    }
    x.to_string()
}

/// One layer's WOTS instance: how its digest is cut into chain positions.
fn wots_line(p: &Params, layer: Layer) -> String {
    let l = layer.chains(p.n, p.scheme).unwrap_or(0);
    let enc = layer.encoding(p.n);
    if !p.scheme.wots_c() {
        let l1 = (8 * p.n).div_ceil(layer.chain_bits());
        return format!("WOTS-TW, {l} chains: {l1} for the digest + {} checksum", l - l1);
    }
    let pinned = enc.map_or(0, |e| e.pinned_bits);
    let swn = layer.swn().unwrap_or_else(|| enc.map_or(0, |e| e.default_swn()));
    let dropped = if layer.dropped_chains() > 0 {
        format!(", {} chain(s) dropped", layer.dropped_chains())
    } else {
        String::new()
    };
    format!(
        "w = {}, {l} chains of {} bits, {pinned} of {} digest bits pinned{dropped}, S_wn = {swn} of {}",
        layer.w(),
        layer.chain_bits(),
        8 * p.n,
        l * (layer.w() - 1)
    )
}

/// The full picture of one parameter set.
pub fn report(p: &Params, c: &Costs, q_s: f64) -> String {
    let forgery = forgery_exponent(q_s, c.hypertree.height() as u32, p.k, p.a);
    let cap = 8.0 * p.n as f64;
    let security = forgery.map_or(0.0, |f| f.min(cap));
    let ht = c.hypertree;
    let row = |label: &str, x: Cost, note: String| format!("{label:<24}{:>12}{note}", si(x.compressions));

    let mut lines = vec![
        format!(
            "scheme          {}   q_s = {}   n = {} bits",
            p.scheme.label(),
            signatures(q_s),
            8 * p.n
        ),
        format!(
            "(h, d)          ({}, {})   layer heights {}",
            ht.height(),
            ht.depth(),
            ht.heights()
        ),
        format!(
            "(a, k)          ({}, {}){}",
            p.a,
            p.k,
            if p.scheme.fors_c() {
                format!("   [FORS+C signs {} trees]", p.k - 1)
            } else {
                String::new()
            }
        ),
    ];
    // one line per distinct WOTS instance, which is one line unless the layers
    // disagree
    if ht.one_wots() {
        lines.push(format!("every layer     {}", wots_line(p, ht.top())));
    } else {
        // one line per run of layers sharing their WOTS parameters
        let mut runs: Vec<(Layer, u64, u64)> = Vec::new();
        for (i, layer) in ht.layers().enumerate() {
            let same =
                |a: Layer, b: Layer| (a.w(), a.dropped_chains(), a.swn()) == (b.w(), b.dropped_chains(), b.swn());
            match runs.last_mut() {
                Some((prev, _, last)) if same(*prev, layer) => *last = i as u64,
                _ => runs.push((layer, i as u64, i as u64)),
            }
        }
        for (layer, first, last) in runs {
            let which = match (first, last) {
                (0, 0) => "top layer".to_string(),
                (f, l) if f == l => format!("layer {f}"),
                (f, l) if l + 1 == ht.depth() => format!("layers {f}..{l}"),
                (f, l) => format!("layers {f}..{l}"),
            };
            lines.push(format!("{which:<16}{}", wots_line(p, layer)));
        }
    }
    lines.push(String::new());
    lines.push(match forgery {
        Some(f) => format!(
            "security        {security:.1} bits classical   (FORS forgery {f:.1}, preimage {})",
            cap as u64
        ),
        None => format!(
            "security        none: q_s = {} reuses every FORS instance ~{:.0} times",
            signatures(q_s),
            q_s / 2f64.powi(ht.height() as i32)
        ),
    });
    lines.push(format!("signature       {} bytes", c.sig_bytes));
    lines.push(String::new());
    lines.push(format!("{:<24}{:>12}", "", "compressions"));
    lines.push(row("keygen", c.keygen, String::new()));
    lines.push(row(
        "sign",
        c.sign,
        format!("   ({} B of state at depth {})", c.cache_bytes, c.cache_depth),
    ));
    lines.push(row("verify", c.verify, String::new()));
    if c.verify_worst != c.verify {
        lines.push(row("verify (worst)", c.verify_worst, String::new()));
    }
    lines.push(String::new());
    lines.push(format!(
        "of signing, grinding accounts for {}: {} searching for WOTS+C counters, {} on the FORS+C digest",
        si(c.grinding().compressions),
        si(c.wots_c_grinding.compressions),
        si(c.fors_c_grinding.compressions)
    ));
    lines.join("\n")
}

const COLUMNS: [(&str, usize); 15] = [
    ("verify", 9),
    ("scheme", 9),
    ("h", 4),
    ("d", 3),
    ("heights", 18),
    ("a", 3),
    ("k", 3),
    ("w", 9),
    ("drop", 5),
    ("l", 7),
    ("S_wn", 11),
    ("size", 6),
    ("keygen", 8),
    ("sign", 8),
    ("cache B", 7),
];

/// `top/low` when the layers disagree, one value when they do not.
fn per_group(top: String, low: String) -> String {
    if top == low { top } else { format!("{top}/{low}") }
}

fn cells(c: &Candidate) -> Vec<String> {
    let (p, x) = (&c.params, &c.costs);
    let ht = x.hypertree;
    let (top, low) = (ht.top(), ht.layers().last().unwrap_or(ht.top()));
    let chains = |layer: Layer| layer.chains(p.n, p.scheme).unwrap_or(0);
    let sum = |layer: Layer| {
        layer
            .swn()
            .or_else(|| layer.encoding(p.n).map(|e| e.default_swn()))
            .map_or("-".to_string(), |s| s.to_string())
    };
    vec![
        si(x.verify.compressions),
        p.scheme.label().to_string(),
        ht.height().to_string(),
        ht.depth().to_string(),
        ht.heights(),
        p.a.to_string(),
        p.k.to_string(),
        per_group(top.w().to_string(), low.w().to_string()),
        per_group(top.dropped_chains().to_string(), low.dropped_chains().to_string()),
        per_group(chains(top).to_string(), chains(low).to_string()),
        if p.scheme.wots_c() {
            per_group(sum(top), sum(low))
        } else {
            "-".to_string()
        },
        x.sig_bytes.to_string(),
        si(x.keygen.compressions),
        si(x.sign.compressions),
        x.cache_bytes.to_string(),
    ]
}

/// What the abbreviated columns mean, since several of them are this project's
/// own and not the report's.
pub fn legend() -> String {
    "every cost in compression calls, one per 64 bytes of hash input; sign = signing with the top tree's half top \
     in state, cache B of it\nheights = every layer's height, top first, and the only one worth caching is that top \
     one; w, drop, l and S_wn are written top/lower where the layers differ, and are the Winternitz parameter, the \
     chains dropped beyond the pinned digest bits, the chains signed, and the target digit sum"
        .to_string()
}

pub fn table(cands: &[Candidate]) -> String {
    let head: Vec<String> = COLUMNS.iter().map(|(name, w)| format!("{name:>w$}")).collect();
    let head = head.join(" ");
    let mut lines = vec![head.clone(), "-".repeat(head.len())];
    for c in cands {
        let row: Vec<String> = cells(c)
            .iter()
            .zip(COLUMNS)
            .map(|(cell, (_, w))| format!("{cell:>w$}", w = w))
            .collect();
        lines.push(row.join(" "));
    }
    lines.join("\n")
}

/// How much of each budget the candidate uses. Unset budgets say nothing.
pub fn utilization(b: &Budgets, c: &Candidate) -> String {
    let used = [
        ("keygen", c.costs.keygen.compressions, b.keygen),
        ("sign", c.costs.sign.compressions, b.sign),
        ("size", c.costs.sig_bytes, b.size),
    ];
    used.iter()
        .filter_map(|(name, v, limit)| limit.map(|l| (name, v, l)))
        .map(|(name, v, limit)| format!("{name} {:.0}%", 100.0 * *v as f64 / limit as f64))
        .collect::<Vec<_>>()
        .join(", ")
}

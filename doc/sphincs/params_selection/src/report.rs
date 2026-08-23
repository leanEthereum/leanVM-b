//! Human-readable output.

use crate::params::{Costs, Params};
use crate::search::{Budgets, Candidate};
use crate::security::forgery_exponent;

pub fn si(x: u64) -> String {
    let f = x as f64;
    for (unit, div) in [("G", 1e9), ("M", 1e6), ("K", 1e3)] {
        if f >= div {
            return format!("{:.2}{unit}", f / div);
        }
    }
    x.to_string()
}

/// One line spelling out the WOTS+C digest-to-chains cut.
pub fn encoding_line(p: &Params, c: &Costs) -> String {
    let Some(swn) = c.swn else {
        let l1 = (8 * p.n).div_ceil(c.chain_bits);
        return format!(
            "encoding        WOTS-TW: {} chains, {l1} for the digest + {} checksum",
            c.l,
            c.l - l1
        );
    };
    let dropped = if c.dropped_chains > 0 {
        format!(", {} chain(s) dropped", c.dropped_chains)
    } else {
        String::new()
    };
    format!(
        "encoding        {} bits/chain, {} of {} digest bits pinned to zero{dropped}, S_wn = {swn} of {}",
        c.chain_bits,
        c.pinned_bits,
        8 * p.n,
        c.l * (p.w - 1)
    )
}

/// The full picture of one parameter set.
pub fn report(p: &Params, c: &Costs, lifetime: u32) -> String {
    let forgery = forgery_exponent(lifetime, p.h as u32, p.k, p.a);
    let cap = 8.0 * p.n as f64;
    let security = forgery.map_or(0.0, |f| f.min(cap));
    let speedup = c.sign.hashes as f64 / c.sign_cached.hashes.max(1) as f64;
    let row = |label: &str, x: crate::cost::Cost, note: String| format!("{label:<24}{:>12}{note}", si(x.compressions));

    let mut lines = vec![
        format!(
            "scheme          {}   q_s = 2^{lifetime}   n = {} bits",
            p.scheme.label(),
            8 * p.n
        ),
        format!("(h, d)          ({}, {})   layer heights {}", p.h, p.d, c.profile),
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
        format!("(w, l)          ({}, {})", p.w, c.l),
        encoding_line(p, c),
        String::new(),
        match forgery {
            Some(f) => format!(
                "security        {security:.1} bits classical   (FORS forgery {f:.1}, preimage {})",
                cap as u64
            ),
            None => format!(
                "security        none: q_s = 2^{lifetime} reuses every FORS instance ~2^{} times",
                lifetime as i64 - p.h as i64
            ),
        },
        format!("signature       {} bytes", c.sig_bytes),
        String::new(),
        format!("{:<24}{:>12}", "", "compressions"),
        row("keygen", c.keygen, String::new()),
        row("sign (avg)", c.sign, String::new()),
        row(
            "sign (half-top cached)",
            c.sign_cached,
            format!(
                "   ({speedup:.2}x, {} B of state at depth {})",
                c.cache_bytes, c.cache_depth
            ),
        ),
        row("verify", c.verify, String::new()),
    ];
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

const COLUMNS: [(&str, usize); 16] = [
    ("verify", 9),
    ("scheme", 9),
    ("h", 4),
    ("d", 3),
    ("ht", 4),
    ("a", 3),
    ("k", 3),
    ("cb", 3),
    ("drop", 5),
    ("l", 4),
    ("S_wn", 6),
    ("size", 6),
    ("keygen", 8),
    ("sign", 8),
    ("sign-cached", 11),
    ("cache B", 7),
];

fn cells(c: &Candidate) -> Vec<String> {
    let (p, x) = (&c.params, &c.costs);
    vec![
        si(x.verify.compressions),
        p.scheme.label().to_string(),
        p.h.to_string(),
        p.d.to_string(),
        x.profile.h_top.to_string(),
        p.a.to_string(),
        p.k.to_string(),
        x.chain_bits.to_string(),
        p.dropped_chains.to_string(),
        x.l.to_string(),
        x.swn.map_or("-".to_string(), |s| s.to_string()),
        x.sig_bytes.to_string(),
        si(x.keygen.compressions),
        si(x.sign.compressions),
        si(x.sign_cached.compressions),
        x.cache_bytes.to_string(),
    ]
}

/// What the abbreviated columns mean, since several of them are this project's
/// own and not the report's.
pub fn legend() -> String {
    "every cost in compression calls, one per 64 bytes of hash input; sign / sign-cached = signing without and \
     with the top tree's half top in state, cache B of it\nht = top layer height, cb = log2(w), drop = chains \
     dropped beyond the pinned digest bits, l = chains signed, S_wn = target digit sum"
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
        ("sign-cached", c.costs.sign_cached.compressions, b.sign_cached),
        ("size", c.costs.sig_bytes, b.size),
    ];
    used.iter()
        .filter_map(|(name, v, limit)| limit.map(|l| (name, v, l)))
        .map(|(name, v, limit)| format!("{name} {:.0}%", 100.0 * *v as f64 / limit as f64))
        .collect::<Vec<_>>()
        .join(", ")
}

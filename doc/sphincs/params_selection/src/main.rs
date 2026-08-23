//! One command: pin the parameters you know, budget the costs you care about,
//! and everything left over gets searched.

use sphincs_params::cost::{SCHEMES, Scheme};
use sphincs_params::params::{Hypertree, Layer};
use sphincs_params::report::{legend, report, si, signatures, table, utilization};
use sphincs_params::search::{
    A_MAX, Budgets, CHAIN_BITS_MAX, D_MAX, DROPPED_MAX, Grid, H_MAX, K_MAX, LEVEL1_BITS, Span, Stats, Sums, edges,
    search,
};

const USAGE: &str = "\
SPHINCS+ parameter selection: what verifies cheapest, or what one set costs.

usage: sphincs_params --lifetime Q [parameters] [budgets] [output]

Give a parameter to pin it, leave it out to search it. Pin them all and the run
just costs that one set. Numbers may be written as 2e6 or 100,000 or 100_000.

parameters
  --lifetime Q      signatures allowed per public key, e.g. 16e6 (required)
  --scheme S        SPX | W+C | W+C_F+C, repeatable       [all three]
  --height h        total hypertree height                [1..96]
  --layers d        hypertree layers                      [1..32]
  --top-height ht   height of the top XMSS tree, the rest
                    of h splitting evenly below it        [1..h-d+1, or h/d]
  --heights H,...   every layer height outright, top first, pinning h and d
  --layer SPEC      one layer outright, repeated top first, e.g.
                    --layer 12,w=16,swn=240 --layer 12,w=8,drop=1
                    Fields: the bare number is the height, then w=, swn=,
                    drop=. Pins h, d and every layer's WOTS instance.
  --split-wots      search a separate WOTS instance for the top layer rather
                    than one for the whole hypertree. Two instances is all a
                    search needs (see Hypertree::two_group), but it multiplies
                    the grid by the number of instances, so expect minutes.
  -a A              log2 of the leaves in a FORS tree     [1..32]
  -k K              FORS trees                            [1..64]
  --chain-bits B    log2(w), repeatable                   [1..12]
  -w W              Winternitz parameter, instead of --chain-bits
  --drop-chains C   WOTS+C chains dropped beyond the
                    minimal digest-bit pinning            [0..16, or 0]
  --swn S           WOTS+C target digit sum               [the most the signing
                                                           budget allows, or the
                                                           mean]
  -n N              hash output in bytes                  [16]

Three of those buy something only by spending something else, so left unpinned
they are searched against the budget that bounds what they spend, and take the
value the report's own parameter sets use when it is unset (the second default
above). --swn and --drop-chains buy cheaper verification with grinding, bounded
by --max-sign; --top-height buys cheaper signing with key generation, bounded by
--max-keygen.

budgets, all optional: an unset one is no limit. Every cost is counted in
compression calls, one per 64 bytes of hash input.
  --max-keygen N        compressions at key generation
  --max-sign N          compressions at signing, counting the top XMSS tree's
                        half top as already in state: the steady-state cost of
                        a signer that keeps the cache the `cache B` column
                        sizes. A signer holding nothing pays the `cold` column
                        instead, which nothing here budgets.
  --max-size B          signature bytes
  --security BITS       classical security floor          [128, NIST level 1]

other
  --cache-height C      cached top-tree level, above the leaves  [half of h_top]
  --cache-level-only    cache one level, not it and everything above
  --top N               rows of the table to print        [15]
  --stats               report how much of the space was visited

examples
  sphincs_params --lifetime 1e9 --max-keygen 2e6 --max-sign 4e6 --max-size 4000
  sphincs_params --lifetime 1e12 --height 40 --layers 5 -a 14 -k 11 -w 256 --swn 2040
";

fn main() -> std::process::ExitCode {
    let argv: Vec<String> = std::env::args().skip(1).collect();
    if argv.is_empty() || argv.iter().any(|a| a == "-h" || a == "--help") {
        print!("{USAGE}");
        return std::process::ExitCode::SUCCESS;
    }
    match run(&argv) {
        Ok(true) => std::process::ExitCode::SUCCESS,
        Ok(false) => std::process::ExitCode::FAILURE,
        Err(e) => {
            eprintln!("error: {e}");
            std::process::ExitCode::from(2)
        }
    }
}

/// Flags and their values, repeatable flags kept in order.
struct Args(Vec<(String, Option<String>)>);

const NO_VALUE: [&str; 5] = ["--cache-level-only", "--stats", "--help", "-h", "--split-wots"];

const FLAGS: [&str; 24] = [
    "--lifetime",
    "--scheme",
    "--height",
    "--layers",
    "--top-height",
    "--heights",
    "--layer",
    "--split-wots",
    "-a",
    "-k",
    "--chain-bits",
    "-w",
    "--drop-chains",
    "--swn",
    "-n",
    "--max-keygen",
    "--max-sign",
    "--max-size",
    "--security",
    "--cache-height",
    "--cache-level-only",
    "--top",
    "--stats",
    "--help",
];

/// Flags that used to exist, and what to reach for instead.
const GONE: [(&str, &str); 8] = [
    (
        "--max-sign-cached",
        "--max-sign, which now counts exactly that: signing with the half top in state",
    ),
    ("--unit", "nothing: every cost is compression calls"),
    ("--uncached", "nothing: every cost is compression calls"),
    ("--max-dropped", "--drop-chains"),
    (
        "--h-max",
        "--height, which pins it; widening the range means raising H_MAX in src/search.rs",
    ),
    ("--d-max", "--layers, or D_MAX in src/search.rs"),
    ("--a-max", "-a, or A_MAX in src/search.rs"),
    ("--k-max", "-k, or K_MAX in src/search.rs"),
];

impl Args {
    fn parse(argv: &[String]) -> Result<Self, String> {
        let mut out = Vec::new();
        let mut i = 0;
        while i < argv.len() {
            let flag = &argv[i];
            if !flag.starts_with('-') {
                return Err(format!("unexpected argument {flag}"));
            }
            if let Some((_, instead)) = GONE.iter().find(|(gone, _)| gone == flag) {
                return Err(format!("{flag} is gone: use {instead}"));
            }
            if !FLAGS.contains(&flag.as_str()) {
                return Err(format!("unknown flag {flag}; run with no arguments for the list"));
            }
            if NO_VALUE.contains(&flag.as_str()) {
                out.push((flag.clone(), None));
                i += 1;
            } else {
                let v = argv.get(i + 1).ok_or_else(|| format!("{flag} needs a value"))?;
                out.push((flag.clone(), Some(v.clone())));
                i += 2;
            }
        }
        Ok(Args(out))
    }

    fn flag(&self, name: &str) -> bool {
        self.0.iter().any(|(f, _)| f == name)
    }

    fn all(&self, name: &str) -> Vec<&str> {
        self.0
            .iter()
            .filter(|(f, _)| f == name)
            .filter_map(|(_, v)| v.as_deref())
            .collect()
    }

    fn get(&self, name: &str) -> Option<&str> {
        self.all(name).last().copied()
    }

    /// Accepts 2e6 and 100,000 and 100_000 as well as 100000.
    fn float(&self, name: &str) -> Result<Option<f64>, String> {
        match self.get(name) {
            None => Ok(None),
            Some(s) => s
                .replace([',', '_', ' '], "")
                .parse::<f64>()
                .map(Some)
                .map_err(|_| format!("{name}: expected a number, got {s}")),
        }
    }

    fn num(&self, name: &str) -> Result<Option<u64>, String> {
        Ok(self.float(name)?.map(|f| f as u64))
    }

    fn u64_or(&self, name: &str, default: u64) -> Result<u64, String> {
        Ok(self.num(name)?.unwrap_or(default))
    }

    /// A pin if the flag was given, the whole range otherwise.
    fn span(&self, name: &str, whole: Span) -> Result<Span, String> {
        Ok(self.num(name)?.map_or(whole, Span::pin))
    }

    fn schemes(&self) -> Result<Vec<Scheme>, String> {
        let named = self.all("--scheme");
        if named.is_empty() {
            return Ok(SCHEMES.to_vec());
        }
        named
            .iter()
            .map(|s| Scheme::parse(s).ok_or_else(|| format!("unknown scheme {s}")))
            .collect()
    }

    fn chain_bits(&self) -> Result<Vec<u64>, String> {
        let mut bits: Vec<u64> = self
            .all("--chain-bits")
            .iter()
            .map(|s| {
                s.parse::<u64>()
                    .map_err(|_| format!("--chain-bits: expected a number, got {s}"))
            })
            .collect::<Result<_, _>>()?;
        if let Some(w) = self.num("-w")? {
            if w < 2 || !w.is_power_of_two() {
                return Err(format!("-w: expected a power of two, got {w}"));
            }
            bits.push(w.trailing_zeros() as u64);
        }
        if bits.is_empty() {
            bits = (1..=CHAIN_BITS_MAX).collect();
        }
        bits.sort_unstable();
        bits.dedup();
        Ok(bits)
    }
}

/// `--heights 12,7,7`, or `--layer 12,w=16,swn=240 --layer 7,w=8` repeated once
/// per layer, top first. Both give the hypertree outright.
fn layers_from(args: &Args) -> Result<Option<Hypertree>, String> {
    let specs = args.all("--layer");
    if !specs.is_empty() {
        let layers: Vec<Layer> = specs
            .iter()
            .map(|spec| {
                let mut height = None;
                let (mut w, mut dropped, mut swn) = (16, 0, None);
                for field in spec.split(',') {
                    let field = field.trim();
                    let (key, value) = field.split_once('=').unwrap_or(("height", field));
                    let value: u64 = value
                        .replace([',', '_'], "")
                        .parse()
                        .map_err(|_| format!("--layer {spec}: {value} is not a number"))?;
                    match key {
                        "height" | "h" => height = Some(value),
                        "w" => w = value,
                        "drop" | "dropped" => dropped = value,
                        "swn" | "S" => swn = Some(value),
                        other => return Err(format!("--layer {spec}: unknown field {other}")),
                    }
                }
                let height = height.ok_or_else(|| format!("--layer {spec}: no height"))?;
                Layer::new(height, w, dropped, swn)
                    .ok_or_else(|| format!("--layer {spec}: height 1..=63 and w a power of two are needed"))
            })
            .collect::<Result<_, _>>()?;
        return Ok(Some(
            Hypertree::new(&layers).ok_or("--layer: 1 to 32 layers, top first")?,
        ));
    }
    let Some(list) = args.get("--heights") else {
        return Ok(None);
    };
    let heights: Vec<u64> = list
        .split(',')
        .map(|x| {
            x.trim()
                .parse::<u64>()
                .map_err(|_| format!("--heights: expected numbers, got {list}"))
        })
        .collect::<Result<_, _>>()?;
    let w = args.num("-w")?.unwrap_or(16);
    let dropped = args.num("--drop-chains")?.unwrap_or(0);
    let swn = args.num("--swn")?;
    let layers: Option<Vec<Layer>> = heights.iter().map(|&h| Layer::new(h, w, dropped, swn)).collect();
    Ok(Some(
        Hypertree::new(&layers.ok_or("--heights: heights are 1..=63")?)
            .ok_or("--heights: 1 to 32 heights, top first")?,
    ))
}

fn run(argv: &[String]) -> Result<bool, String> {
    let args = Args::parse(argv)?;
    let q_s = args.float("--lifetime")?.ok_or("--lifetime is required")?;
    let b = Budgets {
        q_s,
        keygen: args.num("--max-keygen")?,
        sign: args.num("--max-sign")?,
        size: args.num("--max-size")?,
        security: args.get("--security").map_or(Ok(LEVEL1_BITS), |s| {
            s.parse().map_err(|_| format!("--security: expected a number, got {s}"))
        })?,
    };
    // Three axes buy something only by spending something that may be
    // unbudgeted, and then their answer is useless: the target sum and the
    // dropped chains buy cheaper verification with grinding, and a taller top
    // tree buys cheaper signing with key generation and with cold signing.
    // Unpinned, each is searched only when the budget that bounds it is set,
    // and otherwise takes the value the report's own parameter sets use.
    let signing_bounded = b.sign.is_some();
    let sums = match (args.num("--swn")?, signing_bounded) {
        (Some(s), _) => Sums::Pinned(s),
        (None, true) => Sums::Sweep,
        (None, false) => Sums::Mean,
    };
    let dropped = match (args.num("--drop-chains")?, signing_bounded) {
        (Some(c), _) => Span::pin(c),
        (None, true) => Span::new(0, DROPPED_MAX),
        (None, false) => Span::pin(0),
    };
    let h_top = match (args.num("--top-height")?, b.keygen.is_some()) {
        (Some(ht), _) => Some(Span::pin(ht)),
        (None, true) => Some(Span::new(1, H_MAX)),
        (None, false) => None,
    };
    let hypertree = layers_from(&args)?;
    let g = Grid {
        schemes: args.schemes()?,
        n: args.u64_or("-n", 16)?,
        h: match hypertree {
            Some(ht) => Span::pin(ht.height()),
            None => args.span("--height", Span::new(1, H_MAX))?,
        },
        d: match hypertree {
            Some(ht) => Span::pin(ht.depth()),
            None => args.span("--layers", Span::new(1, D_MAX))?,
        },
        h_top,
        a: args.span("-a", Span::new(1, A_MAX))?,
        k: args.span("-k", Span::new(1, K_MAX))?,
        dropped,
        chain_bits: args.chain_bits()?,
        sums,
        split_wots: args.flag("--split-wots"),
        hypertree,
        cache_height: args.num("--cache-height")?,
        cache_level_only: args.flag("--cache-level-only"),
    };

    let mut stats = Stats::default();
    let found = search(&b, &g, &mut stats);
    if args.flag("--stats") {
        println!("{stats}\n");
    }
    if found.is_empty() {
        println!(
            "nothing meets these constraints at {:.0}-bit security and q_s = {}",
            b.security,
            signatures(q_s)
        );
        println!(
            "rejected: {} layer sets over --max-keygen, {} parameter sets over --max-size, {} over --max-sign; \
             and {} (a, k) pairs never reached the security floor",
            si(stats.keygen_pruned),
            si(stats.size_pruned),
            si(stats.sign_pruned),
            si(stats.insecure)
        );
        return Ok(false);
    }

    if !g.fully_pinned() {
        let top = args.u64_or("--top", 15)? as usize;
        let shown = top.min(found.len());
        let kept = match (found.len(), stats.rows_dropped) {
            (1, _) => "1 feasible set".to_string(),
            (n, 0) => format!("{n} feasible sets, best {shown} by verification cost"),
            (n, _) => format!(
                "{} feasible sets, {n} kept, best {shown} by verification cost",
                stats.rows
            ),
        };
        println!("{kept}:\n");
        println!("{}\n", table(&found[..shown]));
        println!("{}\n", legend());
    }

    let best = &found[0];
    let use_ = utilization(&b, best);
    if !use_.is_empty() {
        println!("budget use: {use_}");
    }
    for w in edges(&g, best) {
        println!("warning: {w}");
    }
    if !use_.is_empty() || !edges(&g, best).is_empty() {
        println!();
    }
    println!("{}", report(&best.params, &best.costs, b.q_s));
    Ok(true)
}

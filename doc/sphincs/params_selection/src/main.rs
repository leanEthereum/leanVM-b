//! One command: pin the parameters you know, budget the costs you care about,
//! and everything left over gets searched.

use sphincs_params::cost::{Convention, SCHEMES, Scheme};
use sphincs_params::report::{legend, report, table, utilization};
use sphincs_params::search::{
    A_MAX, Budgets, CHAIN_BITS_MAX, D_MAX, DROPPED_MAX, Grid, H_MAX, K_MAX, LEVEL1_BITS, Span, Stats, Sums, Unit,
    edges, search,
};

const USAGE: &str = "\
SPHINCS+ parameter selection: what verifies cheapest, or what one set costs.

usage: sphincs_params --lifetime L [parameters] [budgets] [output]

Give a parameter to pin it, leave it out to search it. Pin them all and the run
just costs that one set. Numbers may be written as 2e6.

parameters
  --lifetime L      log2 of the signatures allowed per public key (required)
  --scheme S        SPX | W+C | W+C_F+C, repeatable       [all three]
  --height h        total hypertree height                [1..96]
  --layers d        hypertree layers                      [1..32]
  --top-height ht   height of the top XMSS tree, the rest
                    of h splitting evenly below it        [1..h-d+1, or h/d]
  -a A              log2 of the leaves in a FORS tree     [1..32]
  -k K              FORS trees                            [1..64]
  --chain-bits B    log2(w), repeatable                   [1..12]
  -w W              Winternitz parameter, instead of --chain-bits
  --drop-chains C   WOTS+C chains dropped beyond the
                    minimal digest-bit pinning            [0..16, or 0]
  --swn S           WOTS+C target digit sum               [the most the signing
                                                           budget allows, or the
                                                           mean]

The last three trade signer work for cheaper verification, so unpinned they are
searched only against a budget that bounds it; with none they take the value the
report's own parameter sets use, shown above after the comma.
  -n N              hash output in bytes                  [16]

budgets, all optional: an unset one is no limit
  --max-keygen N        hashes at key generation
  --max-sign N          hashes at signing
  --max-sign-cached N   hashes at signing with the top tree's half top cached
  --max-size B          signature bytes
  --security BITS       classical security floor          [128, NIST level 1]
  --unit U              hashes | compressions, for the budgets and the
                        objective alike                   [hashes]

other
  --cache-height C      cached top-tree level, above the leaves  [half of h_top]
  --cache-level-only    cache one level, not it and everything above
  --uncached            charge every hash for its full input, rather than
                        caching the PK.seed midstate
  --top N               rows of the table to print        [15]
  --stats               report how much of the space was visited

examples
  sphincs_params --lifetime 30 --max-keygen 2e6 --max-sign 6e6 \\
                 --max-sign-cached 4e6 --max-size 4000
  sphincs_params --lifetime 40 --height 40 --layers 5 -a 14 -k 11 -w 256 --swn 2040
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

const NO_VALUE: [&str; 4] = ["--uncached", "--cache-level-only", "--stats", "--help"];

impl Args {
    fn parse(argv: &[String]) -> Result<Self, String> {
        let mut out = Vec::new();
        let mut i = 0;
        while i < argv.len() {
            let flag = &argv[i];
            if !flag.starts_with('-') {
                return Err(format!("unexpected argument {flag}"));
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

    /// Accepts 2e6 as well as 2000000.
    fn num(&self, name: &str) -> Result<Option<u64>, String> {
        match self.get(name) {
            None => Ok(None),
            Some(s) => s
                .parse::<f64>()
                .map(|f| Some(f as u64))
                .map_err(|_| format!("{name}: expected a number, got {s}")),
        }
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

fn run(argv: &[String]) -> Result<bool, String> {
    let args = Args::parse(argv)?;
    let lifetime = args.num("--lifetime")?.ok_or("--lifetime is required")?;
    let unit = match args.get("--unit").unwrap_or("hashes") {
        "hashes" => Unit::Hashes,
        "compressions" => Unit::Compressions,
        other => return Err(format!("--unit: expected hashes or compressions, got {other}")),
    };
    let b = Budgets {
        lifetime: lifetime as u32,
        keygen: args.num("--max-keygen")?,
        sign: args.num("--max-sign")?,
        sign_cached: args.num("--max-sign-cached")?,
        size: args.num("--max-size")?,
        security: args.get("--security").map_or(Ok(LEVEL1_BITS), |s| {
            s.parse().map_err(|_| format!("--security: expected a number, got {s}"))
        })?,
        unit,
    };
    // A higher target sum, dropped chains and a taller top tree all buy cheaper
    // verification with signer work, so with nothing bounding the signer they
    // are unbounded and their answer is useless. Unpinned and unbudgeted, they
    // take their classic value instead: the mean target sum, no dropped chains,
    // and h/d on every layer.
    let signing_bounded = b.any_signing_limit();
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
    let h_top = match (args.num("--top-height")?, signing_bounded || b.keygen.is_some()) {
        (Some(ht), _) => Some(Span::pin(ht)),
        (None, true) => Some(Span::new(1, H_MAX)),
        (None, false) => None,
    };
    let g = Grid {
        schemes: args.schemes()?,
        n: args.u64_or("-n", 16)?,
        h: args.span("--height", Span::new(1, H_MAX))?,
        d: args.span("--layers", Span::new(1, D_MAX))?,
        h_top,
        a: args.span("-a", Span::new(1, A_MAX))?,
        k: args.span("-k", Span::new(1, K_MAX))?,
        dropped,
        chain_bits: args.chain_bits()?,
        sums,
        cache_level_only: args.flag("--cache-level-only"),
    };

    let mut stats = Stats::default();
    let found = search(&b, &g, &mut stats);
    if args.flag("--stats") {
        println!("{stats}\n");
    }
    if found.is_empty() {
        println!(
            "nothing meets these constraints at {:.0}-bit security and q_s = 2^{lifetime}",
            b.security
        );
        println!("--stats says where the space went; the binding budget is usually size or keygen");
        return Ok(false);
    }

    if found.len() > 1 {
        let top = args.u64_or("--top", 15)? as usize;
        let kept = if stats.rows_dropped > 0 {
            format!("{} feasible sets, {} kept", stats.rows, found.len())
        } else {
            format!("{} feasible sets", found.len())
        };
        println!(
            "{kept}, best {} by verification {}:\n",
            top.min(found.len()),
            unit.label()
        );
        println!("{}\n", table(&b, &found[..top.min(found.len())]));
        println!("{}\n", legend(&b));
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
    // The convention and the cache split are not searched, so they ride here
    // rather than in the grid.
    let shown = sphincs_params::params::Params {
        cache_height: args.num("--cache-height")?,
        convention: Convention {
            cached_midstate: !args.flag("--uncached"),
        },
        ..best.params
    };
    let costs = sphincs_params::params::costs(shown, best.costs.swn).ok_or("inconsistent parameters")?;
    println!("{}", report(&shown, &costs, b.lifetime));
    Ok(true)
}

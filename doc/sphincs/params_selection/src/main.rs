//! `params`: cost one parameter set. `search`: find the cheapest to verify.

use sphincs_params::cost::{Convention, SCHEMES, Scheme};
use sphincs_params::params::{Params, costs};
use sphincs_params::report::{report, table, utilization};
use sphincs_params::search::{
    A_MAX, Budgets, CHAIN_BITS_MAX, Candidate, D_MAX, DROPPED_MAX, Grid, H_MAX, K_MAX, LEVEL1_BITS, Stats, Unit, edges,
    search,
};

const USAGE: &str = "\
usage: sphincs_params params [options]      cost one parameter set
       sphincs_params search [options]      search for the cheapest verification

params options (defaults are the report's bold 2^40 row):
  --scheme S        SPX | W+C | W+C_F+C            [W+C_F+C]
  --lifetime L      log2 of signatures per key     [40]
  --height h        hypertree height               [40]
  --layers d        hypertree layers               [5]
  --top-height H    height of the top XMSS tree     [h/d, so every layer equal]
  -a A              log2 leaves per FORS tree      [14]
  -k K              FORS trees                     [11]
  -w W              Winternitz parameter           [256]
  --chain-bits B    log2(w), instead of -w
  --swn S           WOTS+C target digit sum        [the mean, l*(w-1)/2]
  --drop-chains C   chains dropped beyond the minimal bit pinning  [0]
  -n N              hash output in bytes           [16]
  --cache-height C  cached top-tree level, above the leaves        [h'/2]
  --cache-level-only  cache one level, not it and everything above
  --uncached        charge every hash for its full input

search options (all five budgets required):
  --lifetime L          log2 of signatures per key
  --max-keygen N        budget for keygen
  --max-sign N          budget for average signing
  --max-sign-cached N   budget for average signing, half top cached
  --max-size B          budget for the signature, in bytes
  --security BITS       classical security floor   [128, NIST level 1]
  --unit U              hashes | compressions, for the budgets and objective [hashes]
  --scheme S            restrict the schemes searched (repeatable)
  --chain-bits B        restrict log2(w) searched (repeatable)
  --top N               rows to print              [15]
  --h-max / --d-max / --a-max / --k-max / --max-dropped   widen or narrow a range
  --stats               report how much of the space was visited
  -n N                  hash output in bytes       [16]
";

fn main() -> std::process::ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("params") => run(cmd_params(&args[1..])),
        Some("search") => run(cmd_search(&args[1..])),
        _ => {
            print!("{USAGE}");
            std::process::ExitCode::from(2)
        }
    }
}

fn run(r: Result<bool, String>) -> std::process::ExitCode {
    match r {
        Ok(true) => std::process::ExitCode::SUCCESS,
        Ok(false) => std::process::ExitCode::FAILURE,
        Err(e) => {
            eprintln!("error: {e}");
            std::process::ExitCode::from(2)
        }
    }
}

/// Flags and their values, with repeatable flags kept in order.
struct Args(Vec<(String, Option<String>)>);

impl Args {
    fn parse(argv: &[String]) -> Result<Self, String> {
        let mut out = Vec::new();
        let mut i = 0;
        while i < argv.len() {
            let flag = &argv[i];
            if !flag.starts_with('-') {
                return Err(format!("unexpected argument {flag}"));
            }
            let takes_value = !matches!(flag.as_str(), "--uncached" | "--cache-level-only" | "--stats");
            if takes_value {
                let v = argv.get(i + 1).ok_or_else(|| format!("{flag} needs a value"))?;
                out.push((flag.clone(), Some(v.clone())));
                i += 2;
            } else {
                out.push((flag.clone(), None));
                i += 1;
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

    fn u64(&self, name: &str, default: u64) -> Result<u64, String> {
        match self.get(name) {
            None => Ok(default),
            // accept 2e6 as well as 2000000
            Some(s) => s
                .parse::<f64>()
                .map(|f| f as u64)
                .map_err(|_| format!("{name}: expected a number, got {s}")),
        }
    }

    fn f64(&self, name: &str, default: f64) -> Result<f64, String> {
        match self.get(name) {
            None => Ok(default),
            Some(s) => s.parse().map_err(|_| format!("{name}: expected a number, got {s}")),
        }
    }

    fn required(&self, name: &str) -> Result<u64, String> {
        self.get(name).ok_or_else(|| format!("{name} is required"))?;
        self.u64(name, 0)
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
}

fn cmd_params(argv: &[String]) -> Result<bool, String> {
    let args = Args::parse(argv)?;
    let w = match args.get("--chain-bits") {
        Some(_) => 1u64 << args.u64("--chain-bits", 8)?,
        None => args.u64("-w", 256)?,
    };
    let lifetime = args.u64("--lifetime", 40)? as u32;
    let p = Params {
        scheme: match args.get("--scheme") {
            Some(s) => Scheme::parse(s).ok_or_else(|| format!("unknown scheme {s}"))?,
            None => Scheme::WcFc,
        },
        h: args.u64("--height", 40)?,
        d: args.u64("--layers", 5)?,
        h_top: args
            .get("--top-height")
            .map(|_| args.u64("--top-height", 0))
            .transpose()?,
        a: args.u64("-a", 14)?,
        k: args.u64("-k", 11)?,
        w,
        n: args.u64("-n", 16)?,
        dropped_chains: args.u64("--drop-chains", 0)?,
        cache_height: args
            .get("--cache-height")
            .map(|_| args.u64("--cache-height", 0))
            .transpose()?,
        cache_level_only: args.flag("--cache-level-only"),
        convention: Convention {
            cached_midstate: !args.flag("--uncached"),
        },
    };
    let swn = args.get("--swn").map(|_| args.u64("--swn", 0)).transpose()?;
    let c = costs(p, swn)
        .ok_or("inconsistent parameters: d must divide h, w must be a power of two, FORS+C needs k >= 2")?;
    println!("{}", report(&p, &c, lifetime));
    Ok(true)
}

fn cmd_search(argv: &[String]) -> Result<bool, String> {
    let args = Args::parse(argv)?;
    let bits: Vec<u64> = args
        .all("--chain-bits")
        .iter()
        .map(|s| {
            s.parse::<u64>()
                .map_err(|_| format!("--chain-bits: expected a number, got {s}"))
        })
        .collect::<Result<_, _>>()?;
    let unit = match args.get("--unit").unwrap_or("hashes") {
        "hashes" => Unit::Hashes,
        "compressions" => Unit::Compressions,
        other => return Err(format!("--unit: expected hashes or compressions, got {other}")),
    };
    let b = Budgets {
        lifetime: args.required("--lifetime")? as u32,
        max_keygen: args.required("--max-keygen")?,
        max_sign: args.required("--max-sign")?,
        max_sign_cached: args.required("--max-sign-cached")?,
        max_size: args.required("--max-size")?,
        security: args.f64("--security", LEVEL1_BITS)?,
        unit,
    };
    let g = Grid {
        schemes: args.schemes()?,
        n: args.u64("-n", 16)?,
        h_max: args.u64("--h-max", H_MAX)?,
        a_max: args.u64("--a-max", A_MAX)?,
        k_max: args.u64("--k-max", K_MAX)?,
        d_max: args.u64("--d-max", D_MAX)?,
        chain_bits: if bits.is_empty() {
            (1..=CHAIN_BITS_MAX).collect()
        } else {
            bits
        },
        max_dropped: args.u64("--max-dropped", DROPPED_MAX)?,
        cache_level_only: args.flag("--cache-level-only"),
        ..Default::default()
    };
    let top = args.u64("--top", 15)? as usize;

    let mut stats = Stats::default();
    let found = search(&b, &g, &mut stats);
    if args.flag("--stats") {
        println!("{stats}\n");
    }
    if found.is_empty() {
        println!(
            "no parameter set meets these budgets at {:.0}-bit security and q_s = 2^{}",
            b.security, b.lifetime
        );
        println!("--stats says which budget pruned everything; the binding one is usually size or keygen");
        return Ok(false);
    }
    println!(
        "{} feasible sets, best {} by verification {}:\n",
        found.len(),
        top.min(found.len()),
        unit.label()
    );
    println!("{}\n", table(&b, &found[..top.min(found.len())]));
    let best: &Candidate = &found[0];
    println!("budget use of the best: {}", utilization(&b, best));
    for w in edges(&g, best) {
        println!("warning: {w}");
    }
    println!();
    println!("{}", report(&best.params, &best.costs, b.lifetime));
    Ok(true)
}

//! Repetition-averaged timing for the manual benchmarks.
//!
//! Every benchmark entry point follows the same shape: one **warmup** pass
//! whose timing is discarded, then `repeat` measured passes whose wall-clock
//! samples are averaged. The warmup exists because a cold pass pays one-time
//! costs that steady-state proving does not — thread-pool spawn, first-touch
//! page faults, and setup/twiddle table construction. Reporting those as
//! proving cost understates throughput and makes back-to-back runs
//! incomparable.
//!
//! Samples are summarized as a mean plus a 95% confidence half-width, and each
//! pass is echoed to stderr, so a reported delta can be read against the noise
//! (and the drift) that produced it.
//!
//! # Cooldown
//!
//! On a thermally-limited host, back-to-back passes measure the power budget
//! rather than the prover. Measured on an M4 Max MacBook Pro (16 in, high power
//! mode, on AC) at the 820-signature XMSS workload:
//!
//! | cooldown before each pass | proving |
//! |---------------------------|---------|
//! | none                      |  3.14 s |
//! | 1 s                       |  2.59 s |
//! | 3 s                       |  1.85 s |
//! | 6 s                       |  1.72 s |
//!
//! That is a 1.8x spread with no code change, and it is *stable* within a run,
//! so a confidence interval does not reveal it. [`Plan::cooldown`] inserts idle
//! time before each measured pass; use ~6 s on an Apple laptop and none on a
//! server-class host. A/B comparisons are only meaningful between runs that
//! used the same cooldown.

use std::time::{Duration, Instant};

/// Mean and 95%-confidence half-width of `samples` (half-width `0` for a
/// single sample). Uses the Student-t critical value for `n - 1` degrees of
/// freedom, so small sample counts are not reported as tighter than they are.
#[must_use]
pub fn mean_and_ci(samples: &[f64]) -> (f64, f64) {
    let n = samples.len();
    assert!(n > 0, "mean_and_ci needs at least one sample");
    let mean = samples.iter().sum::<f64>() / n as f64;
    if n < 2 {
        return (mean, 0.0);
    }
    let variance = samples.iter().map(|x| (x - mean).powi(2)).sum::<f64>() / (n - 1) as f64;
    let std_err = (variance / n as f64).sqrt();
    (mean, t_critical_95(n - 1) * std_err)
}

/// Two-sided 95% Student-t critical value, via the standard Cornish-Fisher
/// expansion around the normal quantile (exact to <0.5% for `df >= 3`).
fn t_critical_95(df: usize) -> f64 {
    if df == 0 {
        return f64::INFINITY;
    }
    let z = 1.959_964_f64;
    let df = df as f64;
    z + (z.powi(3) + z) / (4.0 * df) + (5.0 * z.powi(5) + 16.0 * z.powi(3) + 3.0 * z) / (96.0 * df.powi(2))
}

/// Wall-clock samples from one repeated measurement, in seconds.
#[derive(Clone, Debug, Default)]
pub struct Timing {
    samples: Vec<f64>,
}

impl Timing {
    /// Record one measured pass.
    pub fn push(&mut self, secs: f64) {
        self.samples.push(secs);
    }

    #[must_use]
    pub fn samples(&self) -> &[f64] {
        &self.samples
    }

    /// Mean duration in seconds.
    #[must_use]
    pub fn mean(&self) -> f64 {
        mean_and_ci(&self.samples).0
    }

    /// 95%-confidence half-width in seconds (`0` for a single sample).
    #[must_use]
    pub fn ci(&self) -> f64 {
        mean_and_ci(&self.samples).1
    }

    /// `" ± 0.4%"` when there is more than one sample, else empty — the suffix
    /// appended to every reported duration and throughput.
    #[must_use]
    pub fn spread(&self) -> String {
        let (mean, ci) = mean_and_ci(&self.samples);
        if self.samples.len() < 2 || mean == 0.0 {
            String::new()
        } else {
            format!(" ± {:.1}%", 100.0 * ci / mean)
        }
    }

    /// `"   (mean of 3 runs, 1 warmup)"`, or empty for an unrepeated measurement.
    #[must_use]
    pub fn provenance(&self) -> String {
        if self.samples.len() < 2 {
            String::new()
        } else {
            format!("   (mean of {} runs, 1 warmup)", self.samples.len())
        }
    }
}

/// How a benchmark repeats and paces its measured passes.
#[derive(Clone, Copy, Debug)]
pub struct Plan {
    /// Measured passes to average; at least 1.
    pub repeat: usize,
    /// Idle time before each measured pass, to let a thermally-limited host
    /// recover its clocks (see the module docs).
    pub cooldown: Duration,
}

impl Default for Plan {
    fn default() -> Self {
        Self {
            repeat: 1,
            cooldown: Duration::ZERO,
        }
    }
}

impl Plan {
    /// A plan of `repeat` measured passes, each preceded by `cooldown_ms` idle.
    #[must_use]
    pub fn new(repeat: usize, cooldown_ms: u64) -> Self {
        assert!(repeat >= 1, "a benchmark needs at least one measured pass");
        Self {
            repeat,
            cooldown: Duration::from_millis(cooldown_ms),
        }
    }

    /// Read the plan from the environment: `BENCH_REPEAT` and
    /// `BENCH_COOLDOWN_MS`. For the `#[ignore]`d benchmark tests, which have no
    /// command line of their own.
    #[must_use]
    pub fn from_env() -> Self {
        Self::new(env_usize("BENCH_REPEAT", 1), env_usize("BENCH_COOLDOWN_MS", 0) as u64)
    }

    /// Run `f` once untimed to warm up, then `self.repeat` measured passes,
    /// keeping the last result and the samples.
    pub fn warm_then_measure<T>(&self, mut f: impl FnMut() -> T) -> (T, Timing) {
        // Free the warmup's result before the first measured pass allocates, so
        // every measured pass sees the same steady-state footprint.
        drop(f());
        self.measure(f)
    }

    /// Run `f` `self.repeat` times with no warmup pass, for a stage an earlier
    /// stage already warmed (verification after proving, say).
    pub fn measure<T>(&self, f: impl FnMut() -> T) -> (T, Timing) {
        self.run(f, true)
    }

    /// [`measure`](Self::measure) without the per-pass echo, for a stage whose
    /// individual passes are not interesting. Verification takes milliseconds and
    /// nobody tunes it, so echoing every pass would bury the numbers that matter.
    pub fn measure_quiet<T>(&self, f: impl FnMut() -> T) -> (T, Timing) {
        self.run(f, false)
    }

    fn run<T>(&self, mut f: impl FnMut() -> T, echo: bool) -> (T, Timing) {
        let mut timing = Timing::default();
        let mut last = None;
        for pass in 1..=self.repeat {
            drop(last.take()); // free the previous result before the next pass allocates
            if !self.cooldown.is_zero() {
                std::thread::sleep(self.cooldown);
            }
            let t = Instant::now();
            let out = f();
            let secs = t.elapsed().as_secs_f64();
            timing.push(secs);
            if echo && self.repeat > 1 {
                // Echo each pass: a throttling ramp is visible here and invisible
                // in the mean.
                eprintln!("  [pass {pass}/{}] {secs:.3} s", self.repeat);
            }
            last = Some(out);
        }
        (last.expect("repeat >= 1"), timing)
    }
}

/// Peak resident set size of this process, in bytes.
///
/// Worth reporting next to any timing here: the proving arena trades resident
/// memory for the page faults it removes, so a throughput number is only half the
/// picture. Read after a warmup pass, this is the steady-state footprint.
#[must_use]
pub fn peak_rss_bytes() -> u64 {
    // SAFETY: `getrusage` only writes into the `rusage` we hand it, which is
    // zeroed and correctly sized.
    let mut usage: libc::rusage = unsafe { std::mem::zeroed() };
    unsafe { libc::getrusage(libc::RUSAGE_SELF, &raw mut usage) };
    let max = usage.ru_maxrss as u64;
    // `ru_maxrss` is bytes on macOS and KiB on Linux.
    if cfg!(target_os = "macos") { max } else { max * 1024 }
}

/// Read a `usize` benchmark knob from the environment, defaulting when unset.
///
/// # Panics
/// If the variable is set but does not parse.
#[must_use]
pub fn env_usize(key: &str, default: usize) -> usize {
    std::env::var(key)
        .ok()
        .map(|s| s.parse().unwrap_or_else(|_| panic!("{key} must be an integer")))
        .unwrap_or(default)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn single_sample_has_no_spread() {
        let mut t = Timing::default();
        t.push(1.5);
        assert_eq!(t.mean(), 1.5);
        assert_eq!(t.ci(), 0.0);
        assert_eq!(t.spread(), "");
        assert_eq!(t.provenance(), "");
    }

    #[test]
    fn identical_samples_have_zero_width_interval() {
        let mut t = Timing::default();
        for _ in 0..4 {
            t.push(2.0);
        }
        assert_eq!(t.mean(), 2.0);
        assert_eq!(t.ci(), 0.0);
        assert_eq!(t.spread(), " ± 0.0%");
        assert_eq!(t.provenance(), "   (mean of 4 runs, 1 warmup)");
    }

    #[test]
    fn ci_shrinks_as_samples_accumulate() {
        let spread = |n: usize| {
            let mut t = Timing::default();
            for i in 0..n {
                t.push(if i.is_multiple_of(2) { 1.0 } else { 1.2 });
            }
            t.ci()
        };
        assert!(spread(16) < spread(4), "more samples must tighten the interval");
    }

    #[test]
    fn warmup_pass_is_not_measured() {
        let mut calls = 0;
        let (last, timing) = Plan::new(3, 0).warm_then_measure(|| {
            calls += 1;
            calls
        });
        assert_eq!(calls, 4, "one warmup plus three measured passes");
        assert_eq!(last, 4);
        assert_eq!(timing.samples().len(), 3);
    }

    #[test]
    fn measure_skips_the_warmup() {
        let mut calls = 0;
        let (_, timing) = Plan::new(2, 0).measure(|| calls += 1);
        assert_eq!(calls, 2);
        assert_eq!(timing.samples().len(), 2);
    }
}

//! Shared primitives: the GF(2^128)/GF(2^8) field kernels, bit transposes,
//! multilinear helpers, the scratch buffer pool, and small integer utilities.

pub mod bits;
pub mod field;
pub mod multilinear;
pub mod scratch;

pub use field::{F128, F256Unreduced, G, g_pow, g_powers, mul_by_x, x_pow};

fn format_trace_tree(tree: &tracing_forest::tree::Tree) -> Result<String, std::fmt::Error> {
    use tracing_forest::Formatter;

    let rendered = tracing_forest::printer::Pretty.fmt(tree)?;
    let mut percentages = Vec::new();
    collect_parent_percentages(tree, None, &mut percentages);
    Ok(rewrite_trace_percentages(&rendered, &percentages))
}

fn collect_parent_percentages(
    tree: &tracing_forest::tree::Tree,
    parent_duration: Option<std::time::Duration>,
    percentages: &mut Vec<f64>,
) {
    let tracing_forest::tree::Tree::Span(span) = tree else {
        return;
    };

    let percentage = match parent_duration {
        None => 100.0,
        Some(duration) if duration.is_zero() => 0.0,
        Some(duration) => {
            100.0 * span.total_duration().as_nanos() as f64 / duration.as_nanos() as f64
        }
    };
    percentages.push(percentage);

    for node in span.nodes() {
        collect_parent_percentages(node, Some(span.total_duration()), percentages);
    }
}

/// Replace tracing-forest's root-relative percentages (and its optional self
/// percentage) with one percentage relative to the span's direct parent.
fn rewrite_trace_percentages(rendered: &str, percentages: &[f64]) -> String {
    let mut output = String::with_capacity(rendered.len());
    let mut percentages = percentages.iter();

    for segment in rendered.split_inclusive('\n') {
        let (line, newline) = segment.strip_suffix('\n').map_or((segment, ""), |line| (line, "\n"));

        let timing = line.find(" | ").and_then(|separator| {
            let value_start = separator + " | ".len();
            let values = &line[value_start..];
            let percent_end = values.find("% ]")?;
            let displayed = &values[..percent_end];
            let displayed_total = displayed.rsplit("% / ").next()?;

            displayed_total
                .parse::<f64>()
                .ok()
                .map(|_| (value_start, value_start + percent_end))
        });

        if let Some((value_start, percent_end)) = timing {
            let percentage = percentages
                .next()
                .expect("trace formatter found more spans than trace-tree timings");
            output.push_str(&line[..value_start]);
            output.push_str(&format!("{percentage:.2}"));
            output.push_str(&line[percent_end..]);
        } else {
            output.push_str(line);
        }
        output.push_str(newline);
    }

    assert!(
        percentages.next().is_none(),
        "trace formatter found fewer spans than trace-tree timings"
    );
    output
}

/// Install the hierarchical tracing subscriber used by benchmark binaries.
///
/// The default level is `INFO`; `RUST_LOG` can override it. Repeated calls are
/// harmless: if another global subscriber is already installed, this leaves it
/// unchanged.
pub fn init_tracing() {
    use tracing_forest::{ForestLayer, PrettyPrinter, util::LevelFilter};
    use tracing_subscriber::{EnvFilter, Registry, layer::SubscriberExt, util::SubscriberInitExt};

    let env_filter = EnvFilter::builder()
        .with_default_directive(LevelFilter::INFO.into())
        .from_env_lossy();

    let _ = Registry::default()
        .with(env_filter)
        .with(ForestLayer::from(PrettyPrinter::new().formatter(format_trace_tree)))
        .try_init();
}

#[cfg(test)]
mod tracing_tests {
    use super::rewrite_trace_percentages;

    #[test]
    fn trace_output_uses_parent_relative_percentage() {
        let trace = concat!(
            "INFO     Prove [ 3.38s | 73.12% ]\n",
            "INFO     ┕━ PCS open [ 1.14s | 11.35% / 33.74% ]\n",
            "INFO        ┕━ Sumcheck round [ 17.6ms | 0.53% ] round: 0\n",
        );

        assert_eq!(
            rewrite_trace_percentages(trace, &[100.0, 33.727_810, 1.543_860]),
            concat!(
                "INFO     Prove [ 3.38s | 100.00% ]\n",
                "INFO     ┕━ PCS open [ 1.14s | 33.73% ]\n",
                "INFO        ┕━ Sumcheck round [ 17.6ms | 1.54% ] round: 0\n",
            )
        );
    }
}

/// `log2` of a power of two (panics otherwise).
pub fn log2_strict_usize(n: usize) -> usize {
    assert!(n.is_power_of_two(), "not a power of two: {n}");
    n.trailing_zeros() as usize
}

/// `ceil(log2(n))` for `n ≥ 1`.
pub fn log2_ceil_usize(n: usize) -> usize {
    assert!(n >= 1);
    usize::BITS as usize - (n - 1).leading_zeros() as usize
}

/// Allocate a `Vec<T>` of length `n` whose contents are NOT zero-initialized.
/// Caller MUST write every slot before reading it.
///
/// Used to skip the eager zero-init of large ping-pong buffers in hot prover
/// paths (Ligerito codeword + Merkle tree, zerocheck Round-2 fold, NTT
/// scratch, lincheck packing). At m=29 the
/// zero-fill of a fresh 128 MB `vec![T::default(); n]` runs sequentially on
/// the main thread (~22 ms), which caps the parallel speedup of those phases.
///
/// `T: Copy` ensures `T` has no Drop impl, so the leaked uninitialized
/// elements are a no-op on drop.
///
/// # Safety contract
///
/// Reading uninitialized memory is UB per Rust's memory model regardless of
/// whether all bit patterns are valid for `T`. Caller must ensure every slot
/// is written before any read.
// `uninit_vec` flags exactly this pattern; here it is the deliberate purpose of
// the function (the safety contract above is what makes it sound).
#[allow(clippy::uninit_vec)]
pub fn alloc_uninit_vec<T: Copy>(n: usize) -> Vec<T> {
    let mut v: Vec<T> = Vec::with_capacity(n);
    // SAFETY:
    // - capacity == n was just allocated, so set_len(n) is in bounds.
    // - T: Copy implies !Drop, so leaking uninit elements is a no-op.
    // - Caller upholds write-before-read.
    unsafe {
        v.set_len(n);
    }
    v
}

/// Allocate a zero-filled `Vec<T>` through the global allocator's zeroed path.
/// Large allocations can therefore start as demand-zero pages instead of
/// paying an eager single-threaded fill before parallel work begins.
///
/// # Safety
///
/// The all-zero byte pattern must be a valid value of `T`.
pub unsafe fn alloc_zeroed_vec<T: Copy>(n: usize) -> Vec<T> {
    if n == 0 {
        return Vec::new();
    }
    let layout = std::alloc::Layout::array::<T>(n).expect("allocation size overflow");
    // SAFETY: `layout` is non-empty and was constructed for exactly `n`
    // elements of `T`.
    let ptr = unsafe { std::alloc::alloc_zeroed(layout) } as *mut T;
    if ptr.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    // SAFETY: the global allocator returned storage for exactly `n` elements;
    // the caller guarantees that the zero bytes are valid initialized `T`s.
    unsafe { Vec::from_raw_parts(ptr, n, n) }
}

/// Cached [`perf_core_count`]. The uncached version may spawn `sysctl`; this
/// memoizes it so hot paths can cheaply ask "is the current rayon pool the
/// homogeneous P-core pool?" (i.e. `current_num_threads() <= this`).
#[cfg_attr(not(target_arch = "aarch64"), allow(dead_code))] // caller is aarch64-only
pub fn perf_core_count_cached() -> usize {
    use std::sync::OnceLock;
    static N: OnceLock<usize> = OnceLock::new();
    *N.get_or_init(perf_core_count)
}

/// Best-effort count of performance cores. On macOS, queries
/// `hw.perflevel0.physicalcpu` (= P-core count on Apple silicon, =
/// physical CPU count on Intel). Elsewhere, falls back to
/// `std::thread::available_parallelism()`.
fn perf_core_count() -> usize {
    #[cfg(target_os = "macos")]
    {
        if let Ok(out) = std::process::Command::new("sysctl")
            .args(["-n", "hw.perflevel0.physicalcpu"])
            .output()
            && let Ok(s) = std::str::from_utf8(&out.stdout)
            && let Ok(n) = s.trim().parse::<usize>()
            && n > 0
        {
            return n;
        }
    }
    std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1)
}

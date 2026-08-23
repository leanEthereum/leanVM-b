//! Classical security of a FORS-based parameter set.
//!
//! Ported from `security.sage` of BlockstreamResearch/SPHINCS-Parameters. The
//! sage version carries the sum in 100-digit decimals; this carries it in
//! log2-space `f64`, as the report's own site does, which `tests/goldens` pins
//! against the decimal values to better than 0.001 bits.

/// -log2 P(FORS subset forgery) after `q_s = 2^lifetime` signatures.
///
/// An adversary that finds a hypertree leaf reused `r` times, and a message
/// whose `k` FORS indices all point at leaves those `r` signatures already
/// opened, forges without inverting anything:
///
/// ```text
/// P = sum_r  C(q_s, r) p^r (1-p)^(q_s-r) * (1 - (1 - 1/t)^r)^k
/// ```
///
/// with `p = 2^-h` the chance one signature lands on a given leaf and `t = 2^a`.
/// The binomial term is carried by its recurrence rather than built from
/// `C(q_s, r)`, so `q_s = 2^64` costs no more than `q_s = 2^20`.
///
/// `None` when `q_s` so far exceeds the `2^h` leaves that there is no security
/// left to quantify.
pub fn forgery_exponent(lifetime: u32, h: u32, k: u64, a: u64) -> Option<f64> {
    const LOG2_E: f64 = std::f64::consts::LOG2_E;
    // Expected times one FORS instance is reused. Past a few thousand the sum
    // needs more terms than it is worth: the answer is "none", not a number.
    let lam = 2f64.powi(lifetime as i32 - h as i32);
    if lam > 4096.0 {
        return None;
    }
    let q_s = 2f64.powi(lifetime as i32);
    let log2_p = -(h as f64);
    let log2_1mp = (-2f64.powi(-(h as i32))).ln_1p() * LOG2_E;
    let ln_miss = (-1.0 / 2f64.powi(a as i32)).ln_1p(); // ln(1 - 1/t)

    let r_max = (lam + 40.0 * (lam + 1.0).sqrt()).ceil() as u64 + 40;
    let r_max = r_max.max(1000);

    let mut log2_term = q_s * log2_1mp; // C(q_s,0) p^0 (1-p)^q_s
    let mut log2_sigma = f64::NEG_INFINITY;
    for r in 1..=r_max {
        let rf = r as f64;
        log2_term += (q_s - rf + 1.0).log2() - rf.log2() + log2_p - log2_1mp;
        // log2 (1 - (1-1/t)^r)^k, via expm1 so that small r keeps its digits
        let log2_pf = k as f64 * (-(rf * ln_miss).exp_m1()).log2();
        let contribution = log2_term + log2_pf;
        log2_sigma = log2_sum_exp(log2_sigma, contribution);
        // Stop once the tail cannot matter, either absolutely or against what
        // has already accumulated.
        if rf > lam && (contribution < -1250.0 || contribution < log2_sigma - 80.0) {
            break;
        }
    }
    Some(-log2_sigma)
}

/// Classical bit security: the forgery exponent capped by the preimage bound.
///
/// A query aimed at a FORS forgery cannot double as a preimage query for a tree
/// node or a WOTS chain (different tweaks), so the two attacks are independent
/// strategies and the adversary simply takes the better one.
pub fn security_bits(lifetime: u32, h: u32, k: u64, a: u64, n: u64) -> f64 {
    forgery_exponent(lifetime, h, k, a).map_or(0.0, |e| e.min(8.0 * n as f64))
}

fn log2_sum_exp(a: f64, b: f64) -> f64 {
    let (hi, lo) = if a >= b { (a, b) } else { (b, a) };
    if hi == f64::NEG_INFINITY {
        return hi;
    }
    hi + 2f64.powf(lo - hi).ln_1p() * std::f64::consts::LOG2_E
}

/// `is_secure` memoized over `(h, k, a)`, which is all it depends on.
///
/// A search revisits the same triple once per `(scheme, d, chain_bits,
/// dropped_chains)`, so without this the security sum dominates everything.
pub struct SecurityTable {
    lifetime: u32,
    target: f64,
    n: u64,
    h_max: u32,
    k_max: u64,
    a_max: u64,
    /// 0 unknown, 1 secure, 2 insecure
    seen: Vec<u8>,
}

impl SecurityTable {
    pub fn new(lifetime: u32, target: f64, n: u64, h_max: u32, k_max: u64, a_max: u64) -> Self {
        let cells = (h_max as usize + 1) * (k_max as usize + 1) * (a_max as usize + 1);
        Self {
            lifetime,
            target,
            n,
            h_max,
            k_max,
            a_max,
            seen: vec![0; cells],
        }
    }

    pub fn is_secure(&mut self, h: u32, k: u64, a: u64) -> bool {
        if h > self.h_max || k > self.k_max || a > self.a_max {
            return self.compute(h, k, a);
        }
        let i = (h as usize * (self.k_max as usize + 1) + k as usize) * (self.a_max as usize + 1) + a as usize;
        if self.seen[i] == 0 {
            self.seen[i] = if self.compute(h, k, a) { 1 } else { 2 };
        }
        self.seen[i] == 1
    }

    fn compute(&self, h: u32, k: u64, a: u64) -> bool {
        security_bits(self.lifetime, h, k, a, self.n) >= self.target
    }
}

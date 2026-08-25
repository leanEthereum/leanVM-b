import SphincsSecurity.Proof.FewTimePrehitArith

/-!
# A weighted prefix split for the digest race

The cached branch of a digest retry loop wins immediately, a rejected answer continues, and an
ordinary successful answer ends the event. The weighted split below keeps the continuation
probability instead of paying one full copy of its bound at every retry.
-/

namespace SphincsSecurity

open OracleComp ENNReal

theorem probEvent_bind_le_probEvent_add_mul
    {m : Type _ → Type _} [Monad m]
    [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadLiftT m SetM] [EvalDistCompatible m]
    {alpha beta : Type} {mx : m alpha} {my : alpha → m beta}
    {event : beta → Prop} {hit retry : alpha → Prop} {epsilon : ℝ≥0∞}
    (hoff : ∀ x ∈ support mx, ¬ hit x → ¬ retry x →
      Pr[event | my x] = 0)
    (hretry : ∀ x ∈ support mx, retry x → Pr[event | my x] ≤ epsilon) :
    Pr[event | mx >>= my] ≤
      Pr[hit | mx] + Pr[retry | mx] * epsilon := by
  classical
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_indicator,
    probEvent_eq_tsum_indicator]
  calc
    ∑' x, Pr[= x | mx] * Pr[event | my x] ≤
        ∑' x, ({x | hit x}.indicator (fun y => Pr[= y | mx]) x +
          {x | retry x}.indicator (fun y => Pr[= y | mx] * epsilon) x) := by
      apply ENNReal.tsum_le_tsum
      intro x
      by_cases hx : x ∈ support mx
      · by_cases hhit : hit x
        · calc
            Pr[= x | mx] * Pr[event | my x] ≤ Pr[= x | mx] := by
              simpa only [mul_one] using mul_le_mul' le_rfl probEvent_le_one
            _ ≤ {x | hit x}.indicator (fun y => Pr[= y | mx]) x +
                {x | retry x}.indicator (fun y => Pr[= y | mx] * epsilon) x := by
              simp [hhit]
        · by_cases hrx : retry x
          · calc
              Pr[= x | mx] * Pr[event | my x] ≤
                  Pr[= x | mx] * epsilon := mul_le_mul' le_rfl (hretry x hx hrx)
              _ = {x | hit x}.indicator (fun y => Pr[= y | mx]) x +
                  {x | retry x}.indicator (fun y => Pr[= y | mx] * epsilon) x := by
                simp [hhit, hrx]
          · rw [hoff x hx hhit hrx]
            simp [hhit, hrx]
      · rw [probOutput_eq_zero_of_not_mem_support hx]
        simp
    _ = (∑' x, {x | hit x}.indicator (fun y => Pr[= y | mx]) x) +
        ∑' x, {x | retry x}.indicator (fun y => Pr[= y | mx] * epsilon) x :=
      ENNReal.tsum_add
    _ = (∑' x, {x | hit x}.indicator (fun y => Pr[= y | mx]) x) +
        (∑' x, {x | retry x}.indicator (fun y => Pr[= y | mx]) x) * epsilon := by
      rw [← ENNReal.tsum_mul_right]
      congr 1
      apply tsum_congr
      intro x
      by_cases hrx : retry x <;> simp [hrx]

end SphincsSecurity

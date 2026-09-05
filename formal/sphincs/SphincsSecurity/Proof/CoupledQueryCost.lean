import SphincsSecurity.Proof.MarginalCoupling

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

theorem expected_cost_le_of_relTriple {α β : Type}
    {left : ProbComp α} {right : ProbComp β} {relation : α → β → Prop}
    (hrel : RelTriple left right relation) (leftCost : α → ℝ≥0∞)
    (rightCost : β → ℝ≥0∞) (errorCost : α → ℝ≥0∞)
    (hcost : ∀ a b, relation a b → leftCost a ≤ rightCost b + errorCost a) :
    (∑' a, Pr[= a | left] * leftCost a) ≤
      (∑' b, Pr[= b | right] * rightCost b) + ∑' a, Pr[= a | left] * errorCost a := by
  obtain ⟨coupling, hrelation⟩ := (relTriple_iff_relWP).mp hrel
  have hleft (cost : α → ℝ≥0∞) :
      (∑' a, Pr[= a | left] * cost a) =
        ∑' pair, Pr[= pair | coupling.1] * cost pair.1 := by
    change (∑' a, Pr[= a | (evalDist left : SPMF α)] * cost a) = _
    exact (congrArg (fun run : SPMF α => ∑' a, Pr[= a | run] * cost a)
      coupling.2.map_fst.symm).trans (tsum_probOutput_map_mul coupling.1 Prod.fst cost)
  have hright : (∑' b, Pr[= b | right] * rightCost b) =
      ∑' pair, Pr[= pair | coupling.1] * rightCost pair.2 := by
    change (∑' b, Pr[= b | (evalDist right : SPMF β)] * rightCost b) = _
    exact (congrArg (fun run : SPMF β => ∑' b, Pr[= b | run] * rightCost b)
      coupling.2.map_snd.symm).trans (tsum_probOutput_map_mul coupling.1 Prod.snd rightCost)
  rw [hleft leftCost, hleft errorCost, hright, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro pair
  rw [← mul_add]
  by_cases hpair : pair ∈ support coupling.1
  · exact mul_le_mul' le_rfl (hcost pair.1 pair.2 (hrelation pair hpair))
  · rw [probOutput_eq_zero_of_not_mem_support hpair, zero_mul, zero_mul]

end SphincsSecurity

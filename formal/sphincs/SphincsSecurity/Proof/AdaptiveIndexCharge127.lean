import SphincsSecurity.Proof.AdaptiveIndexCharge

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem expectedMacroIndexCharge_full_scaled_le_127 {α : Type} (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (hbound : (simulateQ (expandedAdversaryImpl key) computation).IsQueryBoundP (· matches Sum.inr _) q)
    (cache : QueryCache HashSpec)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q) :
    expectedMacroIndexCharge key q ∅ Finset.univ computation (cache, []) * ((2 ^ 176 : Nat) : ENNReal)⁻¹ ≤
      (q : ENNReal) * ((29 / 64 : ENNReal) * ((2 ^ 127 : Nat) : ENNReal)⁻¹) := by
  have hsigned : SigningDigestsCached key.parameter cache key.root [] := by
    intro entry hentry
    simp only [List.not_mem_nil] at hentry
  have hvalid : TargetShapeValid ∅ Finset.univ := by constructor <;> simp
  have hcharge := expectedMacroIndexCharge_le_queryBudget key q hq ∅ Finset.univ hvalid computation q hbound (cache, []) hsigned hbudget
  have hcache := simulateQ_logTraced_initial_cache_bound key q computation (cache, []) hbudget
  have hpure : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) (pure () : OracleComp (OracleWorld + SigningSpec) Unit)).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q := by
    intro result hresult
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hresult
    subst result
    exact hcache
  have hinitial := expected_adaptive_cappedRawIndex_full_scaled_le_127 key q hq (pure ()) cache hnone hpure
  simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul] at hinitial
  apply (mul_le_mul' hcharge le_rfl).trans
  rw [mul_assoc]
  exact mul_le_mul' le_rfl hinitial

end SphincsSecurity.Concrete

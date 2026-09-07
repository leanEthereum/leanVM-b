import SphincsSecurity.Proof.FewTimeConditionalCoverage
import SphincsSecurity.Proof.JointProbeMessageReserve
import SphincsSecurity.Proof.RomQueryCharge

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def CoveredMessageCache {n : Nat} (parameter : PublicParameter)
    (views : HashInput → Fin n → Option FewTimeView) (cache : QueryCache HashSpec) : Prop :=
  ∃ input output, MessageHashInput parameter input ∧ cache input = some output ∧
    Admissible (truncateMessageDigest output) ∧ CoveredFewTimeView (views input) (hashOutputFewTimeView output)

noncomputable def freshCoverageCharge {n : Nat} (parameter : PublicParameter)
    (views : HashInput → Fin n → Option FewTimeView) (cache : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  if cache input = none ∧ MessageHashInput parameter input then coverageOccupancyMoment (views input) else 0

theorem coveredMessageCache_cacheQuery_of_clean {n : Nat} (parameter : PublicParameter)
    (views : HashInput → Fin n → Option FewTimeView) (cache : QueryCache HashSpec)
    (hclean : ¬ CoveredMessageCache parameter views cache) (input : HashInput) (output : HashOutput)
    (hcover : CoveredMessageCache parameter views (cache.cacheQuery input output)) :
    MessageHashInput parameter input ∧ Admissible (truncateMessageDigest output) ∧
      CoveredFewTimeView (views input) (hashOutputFewTimeView output) := by
  obtain ⟨target, answer, hmessage, hanswer, hadmissible, hview⟩ := hcover
  by_cases heq : target = input
  · subst target
    rw [QueryCache.cacheQuery_self, Option.some.injEq] at hanswer
    rw [hanswer]
    exact ⟨hmessage, hadmissible, hview⟩
  · rw [QueryCache.cacheQuery_of_ne cache output heq] at hanswer
    exact (hclean ⟨target, answer, hmessage, hanswer, hadmissible, hview⟩).elim

theorem probEvent_uniform_coveredMessageCache_le_charge {n : Nat} (parameter : PublicParameter)
    (views : HashInput → Fin n → Option FewTimeView) (cache : QueryCache HashSpec)
    (input : HashInput) (hfresh : cache input = none) :
    Pr[fun output => CoveredMessageCache parameter views (cache.cacheQuery input output) |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      (if CoveredMessageCache parameter views cache then 1 else 0) +
        freshCoverageCharge parameter views cache input * ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
  by_cases hclean : CoveredMessageCache parameter views cache
  · rw [if_pos hclean]
    exact probEvent_le_one.trans le_self_add
  · rw [if_neg hclean, zero_add]
    by_cases hmessage : MessageHashInput parameter input
    · rw [freshCoverageCharge, if_pos ⟨hfresh, hmessage⟩]
      exact (probEvent_mono (fun output _ hcover =>
        (coveredMessageCache_cacheQuery_of_clean parameter views cache hclean input output hcover).2)).trans
          (probEvent_uniformHashOutput_covered_le_occupancy (views input))
    · rw [freshCoverageCharge, if_neg (fun h => hmessage h.2), zero_mul]
      apply le_of_eq
      apply probEvent_eq_zero_iff.mpr
      intro output _ hcover
      exact hmessage (coveredMessageCache_cacheQuery_of_clean parameter views cache hclean input output hcover).1

theorem probEvent_adaptive_coveredMessageCache_le_charge {α : Type} {n : Nat}
    (parameter : PublicParameter) (views : HashInput → Fin n → Option FewTimeView)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    Pr[fun result : α × QueryCache HashSpec => CoveredMessageCache parameter views result.2 |
      (simulateQ romImpl computation).run cache] ≤
      (if CoveredMessageCache parameter views cache then 1 else 0) +
        expectedQueryCharge (freshCoverageCharge parameter views) computation cache * ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
  let potential : QueryCache HashSpec → ENNReal := fun cache => if CoveredMessageCache parameter views cache then 1 else 0
  have hstep (query : OracleWorld.Domain) (before : QueryCache HashSpec) (hbefore : Finite before) :=
    expected_potential_romImpl_le_charge potential
      (fun cache input => freshCoverageCharge parameter views cache input * ((2 ^ 176 : Nat) : ENNReal)⁻¹)
      (fun cache _ input hfresh => by
        simpa only [potential, mul_ite, mul_one, mul_zero, ← probEvent_eq_tsum_ite] using
          probEvent_uniform_coveredMessageCache_le_charge parameter views cache input hfresh)
      query before hbefore
  have hbound := expected_potential_simulateQ_le_queryCharge potential
    (fun cache input => freshCoverageCharge parameter views cache input * ((2 ^ 176 : Nat) : ENNReal)⁻¹)
    hstep computation cache hfinite
  simpa only [potential, mul_ite, mul_one, mul_zero, ← probEvent_eq_tsum_ite, expectedQueryCharge_mul] using hbound

end SphincsSecurity.Concrete

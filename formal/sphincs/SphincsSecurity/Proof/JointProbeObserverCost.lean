import SphincsSecurity.Proof.JointProbeErasedFields

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem expectedJointNativeProbeCost_eq_observer
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (hbound : computation.IsQueryBoundP OtsProbeSimulation.IsOuterHash q)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat) (hbudget : q ≤ ftsFuel)
    (context : OtsProbeSimulation.DeferredContext) (cache : JointSourceCache) :
    expectedJointNativeProbeCost table ((jointSourceComputation parameter root computation).run cache) state ftsFuel context =
      expectedJointQueryCharge parameter root table (jointOtsQueryCharge parameter) computation state ftsFuel context 0 [] cache.1 cache.2 := by
  induction computation using OracleComp.inductionOn generalizing q state ftsFuel context cache with
  | pure value =>
      exact expectedJointNativeProbeCost_eq_zero_of_probeFree table _
        (jointSourceNativeBlock_probeBound _ 0 (OtsProbeSimulation.ProbeFree.pure value) cache) state ftsFuel context
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      have hpositive : OtsProbeSimulation.IsOuterHash input → 0 < ftsFuel := by
        intro hhash
        have hpos := hbound.1.resolve_left (not_not.mpr hhash)
        omega
      rw [jointSourceComputation, construct_query_bind,
        expectedJointNativeProbeCost_source_bind table _ _ (jointOuterQuery parameter root input)
          (jointSourceOuterQuery_implements parameter root input), expectedJointNativeProbeCost_outerQuery,
        expectedJointQueryCharge_query_bind,
        runRaw_jointOuterQuery_eq_detailed parameter root table input state ftsFuel hpositive,
        tsum_probOutput_map_mul]
      congr 1
      apply tsum_congr
      intro result
      by_cases hresult : result ∈ support (AdaptiveRevealProbe.runDetailed table state ftsFuel
          ((jointOuterQuery parameter root input context 0 [] cache.1).run cache.2))
      · congr 1
        cases result with
        | stopped hit => rfl
        | done hit finalState value =>
            rcases value with ⟨entry, finalCache⟩
            cases entry with
            | none => rfl
            | some entry =>
                have hf := jointOuterQuery_erased_fields parameter root table input state finalState ftsFuel hpositive
                  context cache finalCache entry hit hresult
                dsimp only [AdaptiveRevealProbe.rawResultWithRemaining]
                rw [hf.1, hf.2]
                apply ih entry.value.1 (if OtsProbeSimulation.IsOuterHash input then q - 1 else q)
                  (hbound.2 entry.value.1) finalState (jointOuterRemaining parameter input ftsFuel) _ entry.context (entry.value.2, finalCache)
                apply le_trans _ (jointOuterRemaining_ge parameter input ftsFuel)
                by_cases hhash : OtsProbeSimulation.IsOuterHash input
                · simpa only [if_pos hhash] using Nat.sub_le_sub_right hbudget 1
                · simpa only [if_neg hhash] using hbudget
      · simp [probOutput_eq_zero_of_not_mem_support hresult]

end SphincsSecurity.Concrete.FtsProbeSimulation

import SphincsSecurity.Proof.FtsProbeJointOuterCharge

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem expectedRunChargedCost_maskedJointComputation
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (hbound : computation.IsQueryBoundP OtsProbeSimulation.IsOuterHash q)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat) (hbudget : q ≤ ftsFuel)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache) :
    AdaptiveRevealProbe.expectedRunChargedCost table state ftsFuel
      ((maskedJointComputation parameter root computation context fuel history cache).run ftsCache) =
      expectedJointQueryCharge parameter root table (jointFtsQueryCharge parameter) computation
        state ftsFuel context fuel history cache ftsCache := by
  induction computation using OracleComp.inductionOn generalizing q state ftsFuel context fuel history cache ftsCache with
  | pure value =>
      change AdaptiveRevealProbe.expectedRunChargedCost table state ftsFuel
        ((liftNativeBlock (pure value) context fuel history cache).run ftsCache) = 0
      exact AdaptiveRevealProbe.expectedRunChargedCost_probeFree table state ftsFuel _
        (liftNativeBlock_probeFree _ context fuel history cache ftsCache)
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      have hpositive : OtsProbeSimulation.IsOuterHash input → 0 < ftsFuel := by
        intro hhash
        have hpos := hbound.1.resolve_left (not_not.mpr hhash)
        omega
      have hhead : (jointOuterProbeCharge parameter input state : ENNReal) =
          jointFtsQueryCharge parameter input context cache state ftsCache := by
        cases input with
        | inl input => cases input <;> simp [jointOuterProbeCharge, jointFtsQueryCharge]
        | inr message => simp [jointOuterProbeCharge, jointFtsQueryCharge]
      rw [maskedJointComputation_query_bind, bindNativeSteps, StateT.run_bind,
        expectedJointQueryCharge_query_bind,
        AdaptiveRevealProbe.expectedRunChargedCost_bind_of_resume table state ftsFuel
          (jointOuterRemaining parameter input ftsFuel) (jointOuterProbeCharge parameter input state) _ _
          (by
            convert runCharged_jointOuterQuery_bind parameter root table input state ftsFuel hpositive context fuel history cache ftsCache _ using 1
            apply bind_congr
            intro result
            cases result <;> rfl), hhead]
      congr 1
      apply tsum_congr
      intro result
      congr 1
      cases result with
      | stopped hit => rfl
      | done hit finalState value =>
          rcases value with ⟨entry, finalCache⟩
          cases entry with
          | none => exact AdaptiveRevealProbe.expectedRunChargedCost_pure table finalState _ (none, finalCache)
          | some entry =>
              apply ih entry.value.1 (if OtsProbeSimulation.IsOuterHash input then q - 1 else q) (hbound.2 entry.value.1)
                finalState (jointOuterRemaining parameter input ftsFuel) _ entry.context entry.remaining entry.history entry.value.2 finalCache
              apply le_trans _ (jointOuterRemaining_ge parameter input ftsFuel)
              by_cases hhash : OtsProbeSimulation.IsOuterHash input
              · simpa only [if_pos hhash] using Nat.sub_le_sub_right hbudget 1
              · simpa only [if_neg hhash] using hbudget

theorem expectedJointOts_add_runChargedCost_le_outerBound
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (hbound : computation.IsQueryBoundP OtsProbeSimulation.IsOuterHash q)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat) (hbudget : q ≤ ftsFuel)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache) :
    expectedJointQueryCharge parameter root table (jointOtsQueryCharge parameter) computation
        state ftsFuel context fuel history cache ftsCache +
      AdaptiveRevealProbe.expectedRunChargedCost table state ftsFuel
        ((maskedJointComputation parameter root computation context fuel history cache).run ftsCache) ≤ q := by
  rw [expectedRunChargedCost_maskedJointComputation parameter root table computation q hbound state ftsFuel hbudget]
  exact expectedJointOts_add_fts_charge_le_outerBound parameter root table computation q hbound
    state ftsFuel context fuel history cache ftsCache

end SphincsSecurity.Concrete.FtsProbeSimulation

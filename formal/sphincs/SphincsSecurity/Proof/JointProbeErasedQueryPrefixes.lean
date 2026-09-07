import SphincsSecurity.Proof.JointProbeErasedPrefixCost

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def erasedQueryPrefixProbability
    (table : Coordinate → Digest) (parameter : PublicParameter) (root : Digest)
    (select : (OracleWorld + SigningSpec).Domain → Prop) (computation : OracleComp (OracleWorld + SigningSpec) α) (ordinal : Nat)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe) (cache : JointSourceCache) : ENNReal :=
  rawSourceEventProbability table (jointSourceComputation parameter root (beforeQueryOccurrence select computation ordinal))
    (fun value => value = true) state ftsFuel context fuel history cache

@[simp] theorem erasedQueryPrefixProbability_pure
    (table : Coordinate → Digest) (parameter : PublicParameter) (root : Digest)
    (select : (OracleWorld + SigningSpec).Domain → Prop) (value : α) (ordinal : Nat)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe) (cache : JointSourceCache) :
    erasedQueryPrefixProbability table parameter root select (pure value) ordinal state ftsFuel context fuel history cache = 0 := by
  unfold erasedQueryPrefixProbability
  rw [beforeQueryOccurrence_pure]
  change rawSourceEventProbability table (jointSourceNativeBlock (pure false)) _ _ _ _ _ _ _ = 0
  simp only [rawSourceEventProbability_pure, Bool.false_eq_true, if_false]

theorem erasedQueryPrefixProbability_query_bind
    (table : Coordinate → Digest) (parameter : PublicParameter) (root : Digest)
    (select : (OracleWorld + SigningSpec).Domain → Prop)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α) (ordinal : Nat)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe) (cache : JointSourceCache) :
    erasedQueryPrefixProbability table parameter root select (OracleSpec.query input >>= next) ordinal state ftsFuel context fuel history cache =
      let tailRisk := fun ordinal =>
        ∑' result, Pr[= result | AdaptiveRevealProbe.runRaw table state ftsFuel ((jointOuterQuery parameter root input context fuel history cache.1).run cache.2)] *
          match result with
          | .stopped _ => 0
          | .done finalState remaining (entry, finalCache) => match entry with
            | none => 0
            | some entry => erasedQueryPrefixProbability table parameter root select (next entry.value.1) ordinal
                finalState remaining entry.context entry.remaining entry.history (entry.value.2, finalCache)
      if select input then match ordinal with | 0 => 1 | ordinal + 1 => tailRisk ordinal else tailRisk ordinal := by
  unfold erasedQueryPrefixProbability
  rw [beforeQueryOccurrence_query_bind]
  by_cases hs : select input
  · rw [if_pos hs, if_pos hs]
    cases ordinal with
    | zero =>
        change rawSourceEventProbability table (jointSourceNativeBlock (pure true)) _ _ _ _ _ _ _ = 1
        simp only [rawSourceEventProbability_pure, if_true]
    | succ ordinal =>
        rw [jointSourceComputation, construct_query_bind]
        rw [rawSourceEventProbability_bind table _ _ (jointOuterQuery parameter root input)
          (jointSourceOuterQuery_implements parameter root input)]
        apply tsum_congr
        intro result
        congr 1
        cases result with
        | stopped hit => rfl
        | done finalState remaining value => rcases value with ⟨entry, finalCache⟩; cases entry <;> rfl
  · rw [if_neg hs, if_neg hs]
    rw [jointSourceComputation, construct_query_bind]
    rw [rawSourceEventProbability_bind table _ _ (jointOuterQuery parameter root input)
      (jointSourceOuterQuery_implements parameter root input)]
    apply tsum_congr
    intro result
    congr 1
    cases result with
    | stopped hit => rfl
    | done finalState remaining value => rcases value with ⟨entry, finalCache⟩; cases entry <;> rfl

theorem tsum_erasedQueryPrefixProbability_query_bind
    (table : Coordinate → Digest) (parameter : PublicParameter) (root : Digest)
    (select : (OracleWorld + SigningSpec).Domain → Prop)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe) (cache : JointSourceCache) :
    (∑' ordinal, erasedQueryPrefixProbability table parameter root select (OracleSpec.query input >>= next) ordinal
      state ftsFuel context fuel history cache) =
      (if select input then 1 else 0) +
        ∑' result, Pr[= result | AdaptiveRevealProbe.runRaw table state ftsFuel ((jointOuterQuery parameter root input context fuel history cache.1).run cache.2)] *
          match result with
          | .stopped _ => 0
          | .done finalState remaining (entry, finalCache) => match entry with
            | none => 0
            | some entry => ∑' ordinal, erasedQueryPrefixProbability table parameter root select (next entry.value.1) ordinal
                finalState remaining entry.context entry.remaining entry.history (entry.value.2, finalCache) := by
  by_cases hs : select input
  · rw [tsum_eq_zero_add' ENNReal.summable]
    simp only [erasedQueryPrefixProbability_query_bind, if_pos hs]
    congr 1
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro result
    cases result with
    | stopped hit => simp
    | done finalState remaining value =>
        rcases value with ⟨entry, finalCache⟩
        cases entry <;> simp only [mul_zero, tsum_zero, ENNReal.tsum_mul_left]
  · simp only [erasedQueryPrefixProbability_query_bind, if_neg hs, zero_add]
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro result
    cases result with
    | stopped hit => simp
    | done finalState remaining value =>
        rcases value with ⟨entry, finalCache⟩
        cases entry <;> simp only [mul_zero, tsum_zero, ENNReal.tsum_mul_left]

theorem tsum_erasedQueryPrefixProbability_eq_observer
    (table : Coordinate → Digest) (parameter : PublicParameter) (root : Digest)
    (select : (OracleWorld + SigningSpec).Domain → Prop) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (q : Nat) (hbound : computation.IsQueryBoundP OtsProbeSimulation.IsOuterHash q)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat) (hbudget : q ≤ ftsFuel)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe) (cache : JointSourceCache) :
    (∑' ordinal, erasedQueryPrefixProbability table parameter root select computation ordinal state ftsFuel context fuel history cache) =
      expectedJointQueryCharge parameter root table (fun input _ _ _ _ => if select input then 1 else 0)
        computation state ftsFuel context fuel history cache.1 cache.2 := by
  induction computation using OracleComp.inductionOn generalizing q state ftsFuel context fuel history cache with
  | pure value => simp [expectedJointQueryCharge]
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      have hpositive : OtsProbeSimulation.IsOuterHash input → 0 < ftsFuel := by
        intro hhash
        have hpos := hbound.1.resolve_left (not_not.mpr hhash)
        omega
      rw [tsum_erasedQueryPrefixProbability_query_bind, expectedJointQueryCharge_query_bind,
        runRaw_jointOuterQuery_eq_detailed parameter root table input state ftsFuel hpositive, tsum_probOutput_map_mul]
      congr 1
      apply tsum_congr
      intro result
      congr 1
      cases result with
      | stopped hit => rfl
      | done hit finalState value =>
          rcases value with ⟨entry, finalCache⟩
          cases entry with
          | none => rfl
          | some entry =>
              apply ih entry.value.1 (if OtsProbeSimulation.IsOuterHash input then q - 1 else q) (hbound.2 entry.value.1)
                finalState (jointOuterRemaining parameter input ftsFuel) _ entry.context entry.remaining entry.history (entry.value.2, finalCache)
              apply le_trans _ (jointOuterRemaining_ge parameter input ftsFuel)
              by_cases hhash : OtsProbeSimulation.IsOuterHash input
              · simpa only [if_pos hhash] using Nat.sub_le_sub_right hbudget 1
              · simpa only [if_neg hhash] using hbudget

end SphincsSecurity.Concrete.FtsProbeSimulation

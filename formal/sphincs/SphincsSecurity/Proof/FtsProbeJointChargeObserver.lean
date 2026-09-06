import SphincsSecurity.Proof.JointErasedProbeStepBudget

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

abbrev JointQueryCharge := (OracleWorld + SigningSpec).Domain → OtsProbeSimulation.DeferredContext →
  OtsProbeSimulation.SplitHashCache → AdaptiveRevealProbe.State Coordinate → SplitHashCache → ENNReal

noncomputable def jointOuterRemaining (parameter : PublicParameter) :
    (OracleWorld + SigningSpec).Domain → Nat → Nat
  | .inl (.inr input), fuel => if (decodeProbe? parameter input).isSome then fuel - 1 else fuel
  | _, fuel => fuel

noncomputable def expectedJointQueryCharge
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → Digest) (charge : JointQueryCharge)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache) : ENNReal :=
  OracleComp.construct
    (C := fun _ => AdaptiveRevealProbe.State Coordinate → Nat → OtsProbeSimulation.DeferredContext → Nat →
      List OtsProbeSimulation.Probe → OtsProbeSimulation.SplitHashCache → SplitHashCache → ENNReal)
    (fun _ _ _ _ _ _ _ _ => 0)
    (fun input _ next state ftsFuel context fuel history cache ftsCache =>
      charge input context cache state ftsCache +
        ∑' result, Pr[= result | AdaptiveRevealProbe.runDetailed table state ftsFuel
          ((jointOuterQuery parameter root input context fuel history cache).run ftsCache)] *
          match result with
          | .stopped _ => 0
          | .done _ finalState (entry, finalCache) => match entry with
            | none => 0
            | some entry => next entry.value.1 finalState (jointOuterRemaining parameter input ftsFuel)
                entry.context entry.remaining entry.history entry.value.2 finalCache)
    computation state ftsFuel context fuel history cache ftsCache

theorem expectedJointQueryCharge_query_bind
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → Digest) (charge : JointQueryCharge)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache) :
    expectedJointQueryCharge parameter root table charge
      ((liftM (OracleSpec.query input) : OracleComp (OracleWorld + SigningSpec) _) >>= next)
      state ftsFuel context fuel history cache ftsCache =
      charge input context cache state ftsCache +
        ∑' result, Pr[= result | AdaptiveRevealProbe.runDetailed table state ftsFuel
          ((jointOuterQuery parameter root input context fuel history cache).run ftsCache)] *
          match result with
          | .stopped _ => 0
          | .done _ finalState (entry, finalCache) => match entry with
            | none => 0
            | some entry => expectedJointQueryCharge parameter root table charge (next entry.value.1)
                finalState (jointOuterRemaining parameter input ftsFuel) entry.context entry.remaining entry.history entry.value.2 finalCache := by
  rw [expectedJointQueryCharge, construct_query_bind]
  rfl

theorem expectedJointQueryCharge_add
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → Digest) (left right : JointQueryCharge)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache) :
    expectedJointQueryCharge parameter root table (fun input context cache state ftsCache =>
      left input context cache state ftsCache + right input context cache state ftsCache)
      computation state ftsFuel context fuel history cache ftsCache =
      expectedJointQueryCharge parameter root table left computation state ftsFuel context fuel history cache ftsCache +
        expectedJointQueryCharge parameter root table right computation state ftsFuel context fuel history cache ftsCache := by
  induction computation using OracleComp.inductionOn generalizing state ftsFuel context fuel history cache ftsCache with
  | pure value => simp only [expectedJointQueryCharge, construct_pure, add_zero]
  | query_bind input next ih =>
      rw [expectedJointQueryCharge_query_bind, expectedJointQueryCharge_query_bind, expectedJointQueryCharge_query_bind,
        add_add_add_comm, ← ENNReal.tsum_add]
      apply congrArg (fun cost : ENNReal => left input context cache state ftsCache + right input context cache state ftsCache + cost)
      apply tsum_congr
      intro result
      rw [← mul_add]
      congr 1
      cases result with
      | stopped hit => simp
      | done hit finalState value =>
          rcases value with ⟨entry, finalCache⟩
          cases entry with
          | none => simp
          | some entry => exact ih entry.value.1 finalState _ entry.context entry.remaining entry.history entry.value.2 finalCache

theorem expectedJointQueryCharge_le_outerBound
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → Digest) (charge : JointQueryCharge)
    (hcharge : ∀ input context cache state ftsCache, charge input context cache state ftsCache ≤
      if OtsProbeSimulation.IsOuterHash input then 1 else 0)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (hbound : computation.IsQueryBoundP OtsProbeSimulation.IsOuterHash q)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache) :
    expectedJointQueryCharge parameter root table charge computation state ftsFuel context fuel history cache ftsCache ≤ q := by
  induction computation using OracleComp.inductionOn generalizing q state ftsFuel context fuel history cache ftsCache with
  | pure value => exact bot_le
  | query_bind input next ih =>
      rw [expectedJointQueryCharge_query_bind]
      rw [isQueryBoundP_query_bind_iff] at hbound
      let cost : Nat := if OtsProbeSimulation.IsOuterHash input then 1 else 0
      have hcost : cost ≤ q := by
        by_cases hhash : OtsProbeSimulation.IsOuterHash input
        · have hpos := hbound.1.resolve_left (not_not.mpr hhash)
          simp only [cost, if_pos hhash]
          omega
        · simp [cost, hhash]
      have hhead : charge input context cache state ftsCache ≤ (cost : ENNReal) := by
        simpa only [cost, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using hcharge input context cache state ftsCache
      have htail : (∑' result, Pr[= result | AdaptiveRevealProbe.runDetailed table state ftsFuel
          ((jointOuterQuery parameter root input context fuel history cache).run ftsCache)] *
          match result with
          | .stopped _ => 0
          | .done _ finalState (entry, finalCache) => match entry with
            | none => 0
            | some entry => expectedJointQueryCharge parameter root table charge (next entry.value.1)
                finalState (jointOuterRemaining parameter input ftsFuel) entry.context entry.remaining entry.history entry.value.2 finalCache) ≤
          ((q - cost : Nat) : ENNReal) := by
        calc
          _ ≤ ∑' result, Pr[= result | AdaptiveRevealProbe.runDetailed table state ftsFuel
              ((jointOuterQuery parameter root input context fuel history cache).run ftsCache)] * ((q - cost : Nat) : ENNReal) := by
            apply ENNReal.tsum_le_tsum
            intro result
            apply mul_le_mul' le_rfl
            cases result with
            | stopped hit => exact bot_le
            | done hit finalState value =>
                rcases value with ⟨entry, finalCache⟩
                cases entry with
                | none => exact bot_le
                | some entry =>
                    apply ih entry.value.1 (q - cost) _ finalState _ entry.context entry.remaining entry.history entry.value.2 finalCache
                    by_cases hhash : OtsProbeSimulation.IsOuterHash input <;> simpa [cost, hhash] using hbound.2 entry.value.1
          _ ≤ _ := by
            rw [ENNReal.tsum_mul_right]
            exact mul_le_of_le_one_left (by positivity) tsum_probOutput_le_one
      exact (add_le_add hhead htail).trans_eq (by rw [← Nat.cast_add, Nat.add_sub_of_le hcost])

end SphincsSecurity.Concrete.FtsProbeSimulation

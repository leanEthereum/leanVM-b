import SphincsSecurity.Proof.FtsProbeJointObserverBudget
import SphincsSecurity.Proof.AdaptiveRevealProbeCostDecomposition

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def jointOuterProbeCharge (parameter : PublicParameter)
    (input : (OracleWorld + SigningSpec).Domain) (state : AdaptiveRevealProbe.State Coordinate) : Nat :=
  match input with
  | .inl (.inr input) => jointHashProbeCharge parameter input state
  | _ => 0

theorem jointOuterRemaining_hash_succ (parameter : PublicParameter) (input : HashInput) (remaining : Nat) :
    jointOuterRemaining parameter (.inl (.inr input)) (remaining + 1) = jointHashRemaining parameter input remaining := by
  unfold jointOuterRemaining jointHashRemaining
  cases hdecode : decodeProbe? parameter input <;> simp [hdecode]

theorem jointOuterRemaining_ge (parameter : PublicParameter) (input : (OracleWorld + SigningSpec).Domain) (fuel : Nat) :
    (if OtsProbeSimulation.IsOuterHash input then fuel - 1 else fuel) ≤ jointOuterRemaining parameter input fuel := by
  cases input with
  | inl input =>
      cases input with
      | inl n => simp [jointOuterRemaining, OtsProbeSimulation.IsOuterHash]
      | inr input =>
          simp only [OtsProbeSimulation.IsOuterHash, if_true, jointOuterRemaining]
          split_ifs <;> omega
  | inr message => simp [jointOuterRemaining, OtsProbeSimulation.IsOuterHash]

theorem runCharged_jointOuterQuery_bind
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (hpositive : OtsProbeSimulation.IsOuterHash input → 0 < ftsFuel)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache)
    (next : NativeStepResult ((OracleWorld + SigningSpec).Range input) × SplitHashCache → OracleComp (AdaptiveRevealProbe.World Coordinate) α) :
    AdaptiveRevealProbe.runCharged table state ftsFuel
      (((jointOuterQuery parameter root input context fuel history cache).run ftsCache) >>= next) =
      AdaptiveRevealProbe.runDetailed table state ftsFuel
        ((jointOuterQuery parameter root input context fuel history cache).run ftsCache) >>= fun result =>
          match result with
          | .stopped hit => pure (.stopped hit, jointOuterProbeCharge parameter input state)
          | .done _ finalState value => (fun result => (result.1, result.2 + jointOuterProbeCharge parameter input state)) <$>
              AdaptiveRevealProbe.runCharged table finalState (jointOuterRemaining parameter input ftsFuel) (next value) := by
  cases input with
  | inl input =>
      cases input with
      | inl n =>
          simp only [jointOuterQuery, jointOuterProbeCharge, jointOuterRemaining, Nat.add_zero, Prod.mk.eta]
          rw [AdaptiveRevealProbe.runCharged_bind_probeFree table state ftsFuel _ next
            (liftNativeBlock_probeFree (OtsProbeSimulation.splitUniformImpl n) context fuel history cache ftsCache)]
          apply bind_congr
          intro result
          cases result <;> simp
      | inr input =>
          have hpos : 0 < ftsFuel := hpositive (by trivial)
          cases ftsFuel with
          | zero => omega
          | succ remaining =>
              simp only [jointOuterQuery, jointOuterProbeCharge, jointOuterRemaining_hash_succ]
              convert runCharged_maskedJointHashQuery_bind parameter table input state remaining context fuel history cache ftsCache next using 1
              apply bind_congr
              intro result
              cases result <;> rfl
  | inr message =>
      simp only [jointOuterQuery, jointOuterProbeCharge, jointOuterRemaining, Nat.add_zero, Prod.mk.eta]
      rw [runCharged_maskedJointSign_bind]
      apply bind_congr
      intro result
      cases result <;> simp

end SphincsSecurity.Concrete.FtsProbeSimulation

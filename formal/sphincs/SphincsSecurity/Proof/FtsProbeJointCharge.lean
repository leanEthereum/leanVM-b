import SphincsSecurity.Proof.SecurityJointFtsHitEndpoint
import SphincsSecurity.Proof.AdaptiveRevealProbeCostExpectation

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local irreducible] OtsProbeSimulation.maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

noncomputable def jointRetainedProbeCharge (adversary : Adversary) (parameter : PublicParameter) (q : Nat) : ENNReal :=
  AdaptiveRevealProbe.expectedProbeCharge
    ((maskedJointRetained adversary parameter q (OtsProbeSimulation.ensuredInitialContext ∅) 0 []
      OtsProbeSimulation.emptySplitHashCache).run emptySplitHashCache)
    AdaptiveRevealProbe.State.empty q

theorem jointRetainedProbeCharge_le_q (adversary : Adversary) (parameter : PublicParameter) (q : Nat) :
    jointRetainedProbeCharge adversary parameter q ≤ q :=
  AdaptiveRevealProbe.expectedProbeCharge_le_fuel _ _ _

theorem sampledJointRetainedFtsHitRisk_eq_experiment
    (adversary : Adversary) (parameter : PublicParameter) (q : Nat) :
    (∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      jointRetainedFtsHitRisk adversary parameter
        (fun coordinate => ftsSecret coordinate.1 coordinate.2.1 coordinate.2.2) q) =
      Pr[fun hit : Bool => hit = true | AdaptiveRevealProbe.experiment AdaptiveRevealProbe.State.empty q
        ((maskedJointRetained adversary parameter q (OtsProbeSimulation.ensuredInitialContext ∅) 0 []
          OtsProbeSimulation.emptySplitHashCache).run emptySplitHashCache)] := by
  let computation := (maskedJointRetained adversary parameter q (OtsProbeSimulation.ensuredInitialContext ∅) 0 []
    OtsProbeSimulation.emptySplitHashCache).run emptySplitHashCache
  have hextend (table : Coordinate → Digest) :
      AdaptiveRevealProbe.extendTable (AdaptiveRevealProbe.State.empty : AdaptiveRevealProbe.State Coordinate) table = table := by
    funext coordinate
    rfl
  have hdist : evalDist ((curryFtsTableEquiv <$> sampleFtsSecrets) >>= fun table =>
      AdaptiveRevealProbe.run table AdaptiveRevealProbe.State.empty q computation) =
      evalDist (AdaptiveRevealProbe.experiment AdaptiveRevealProbe.State.empty q computation) := by
    unfold AdaptiveRevealProbe.experiment
    simp only [hextend]
    rw [evalDist_bind, evalDist_bind, evalDist_uncurry_sampleFtsSecrets]
  rw [← probEvent_congr' (fun _ _ => Iff.rfl) hdist, bind_map_left, probEvent_bind_eq_tsum]
  apply tsum_congr
  intro ftsSecret
  unfold jointRetainedFtsHitRisk jointRetainedDetailed
  rw [← AdaptiveRevealProbe.runDetailed_hit_eq_run, probEvent_map]
  rfl

theorem sampledJointRetainedFtsHitRisk_le_probeCharge
    (adversary : Adversary) (parameter : PublicParameter) (q : Nat) :
    (∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      jointRetainedFtsHitRisk adversary parameter
        (fun coordinate => ftsSecret coordinate.1 coordinate.2.1 coordinate.2.2) q) ≤
      jointRetainedProbeCharge adversary parameter q * (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [sampledJointRetainedFtsHitRisk_eq_experiment]
  letI : Nonempty Coordinate :=
    ⟨(⟨0, by norm_num [totalHeight]⟩, ⟨0, by norm_num [ftsTrees]⟩, ⟨0, by norm_num [ftsTreeHeight]⟩)⟩
  exact AdaptiveRevealProbe.experiment_empty_probability_le_expectedProbeCharge q _

theorem jointRetainedProbeCharge_eq_expectedCost
    (adversary : Adversary) (parameter : PublicParameter) (q : Nat) :
    jointRetainedProbeCharge adversary parameter q =
      ∑' result, Pr[= result | AdaptiveRevealProbe.chargedExperiment AdaptiveRevealProbe.State.empty q
        ((maskedJointRetained adversary parameter q (OtsProbeSimulation.ensuredInitialContext ∅) 0 []
          OtsProbeSimulation.emptySplitHashCache).run emptySplitHashCache)] * (result.2 : ENNReal) :=
  (AdaptiveRevealProbe.chargedExperiment_expectedCost_eq _ _ _).symm

end SphincsSecurity.Concrete.FtsProbeSimulation

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

noncomputable def sampledJointRetainedProbeCharge (adversary : Adversary) (q : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] * FtsProbeSimulation.jointRetainedProbeCharge adversary parameter q

theorem sampledJointRetainedProbeCharge_le_q (adversary : Adversary) (q : Nat) :
    sampledJointRetainedProbeCharge adversary q ≤ q := by
  calc
    _ ≤ ∑' parameter, Pr[= parameter | sampleParameter] * (q : ENNReal) :=
      ENNReal.tsum_le_tsum fun parameter => mul_le_mul' le_rfl (FtsProbeSimulation.jointRetainedProbeCharge_le_q adversary parameter q)
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left (by positivity) tsum_probOutput_le_one

theorem sampledJointRetainedFtsHitRisk_le_probeCharge (adversary : Adversary) (q : Nat) :
    sampledJointRetainedFtsHitRisk adversary q ≤ sampledJointRetainedProbeCharge adversary q * (Fintype.card Digest : ENNReal)⁻¹ := by
  unfold sampledJointRetainedFtsHitRisk sampledJointRetainedProbeCharge
  rw [← ENNReal.tsum_mul_right]
  exact ENNReal.tsum_le_tsum fun parameter => by
    rw [mul_assoc]
    exact mul_le_mul' le_rfl (FtsProbeSimulation.sampledJointRetainedFtsHitRisk_le_probeCharge adversary parameter q)

end SphincsSecurity.Concrete

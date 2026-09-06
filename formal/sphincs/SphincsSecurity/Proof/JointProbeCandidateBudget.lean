import SphincsSecurity.Proof.OtsProbeSourceCandidateRisk
import SphincsSecurity.Proof.JointProbeRetainedCutBudget

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation
attribute [local instance] Classical.propDecidable

noncomputable def sampledNativeFtsDirectRisk
    (targets : Finset Position) (adversary : Adversary) (fuel q : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      initializedSourceDirectRisk targets
        (FtsProbeSimulation.nativeFtsRetainedSource adversary parameter (FtsProbeSimulation.curryFtsTableEquiv ftsSecret) q) fuel q

theorem sampledNativeFtsDirectRisk_le_history_charge
    (targets : Finset Position) (adversary : Adversary) (fuel q : Nat) (hq : q ≤ Fintype.card Digest) :
    sampledNativeFtsDirectRisk targets adversary fuel q ≤
      sampledNativeFtsHistoryCutCharge targets adversary q * (Fintype.card Digest : ENNReal)⁻¹ := by
  unfold sampledNativeFtsDirectRisk sampledNativeFtsHistoryCutCharge
  rw [← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro parameter
  rw [mul_assoc, ← ENNReal.tsum_mul_right]
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro ftsSecret
  rw [mul_assoc]
  exact mul_le_mul' le_rfl (initializedSourceDirectRisk_le_sharedHistory targets _ fuel q hq
    (FtsProbeSimulation.nativeFtsRetainedSource_probeBound adversary parameter _ q))

theorem sampledNativeFtsDirectRisk_le_cost
    (targets : Finset Position) (adversary : Adversary) (fuel q : Nat) (hq : q ≤ Fintype.card Digest) :
    sampledNativeFtsDirectRisk targets adversary fuel q ≤
      sampledNativeFtsOtsCharge adversary q * (Fintype.card Digest : ENNReal)⁻¹ :=
  (sampledNativeFtsDirectRisk_le_history_charge targets adversary fuel q hq).trans
    (mul_le_mul' (sampledNativeFtsHistoryCutCharge_le_cost targets adversary q) le_rfl)

theorem sampledNativeFtsDirect_add_fts_hit_le_query_rate
    (targets : Finset Position) (adversary : Adversary) (fuel q : Nat) (hq : q ≤ Fintype.card Digest) :
    sampledNativeFtsDirectRisk targets adversary fuel q + sampledJointRetainedFtsHitRisk adversary q ≤
      (q : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ :=
  (add_le_add (sampledNativeFtsDirectRisk_le_history_charge targets adversary fuel q hq) le_rfl).trans
    (sampledNativeFtsHistoryCut_add_fts_hit_le_query_rate targets adversary q)

end SphincsSecurity.Concrete

import SphincsSecurity.Proof.JointProbeRetainedCost
import SphincsSecurity.Proof.OtsProbeCappedCost

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

noncomputable def sampledNativeFtsHistoryCutCharge
    (targets : Finset Position) (adversary : Adversary) (q : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      OtsProbeSimulation.sharedHistoryCutCharge targets
        (OtsProbeSimulation.capProbeQueries
          (FtsProbeSimulation.nativeFtsRetainedSource adversary parameter (FtsProbeSimulation.curryFtsTableEquiv ftsSecret) q) q)
        (OtsProbeSimulation.ensuredInitialContext targets) q

theorem sampledNativeFtsHistoryCutCharge_le_cost
    (targets : Finset Position) (adversary : Adversary) (q : Nat) :
    sampledNativeFtsHistoryCutCharge targets adversary q ≤ sampledNativeFtsOtsCharge adversary q := by
  unfold sampledNativeFtsHistoryCutCharge sampledNativeFtsOtsCharge
  apply ENNReal.tsum_le_tsum
  intro parameter
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro ftsSecret
  exact mul_le_mul' le_rfl (OtsProbeSimulation.sharedHistoryCutCharge_cap_ensuredInitial_le_cost _ targets q
    (FtsProbeSimulation.nativeFtsRetainedSource_probeBound adversary parameter _ q))

theorem sampledNativeFtsHistoryCut_add_fts_charge_le_q
    (targets : Finset Position) (adversary : Adversary) (q : Nat) :
    sampledNativeFtsHistoryCutCharge targets adversary q + sampledJointRetainedProbeCharge adversary q ≤ q :=
  (add_le_add (sampledNativeFtsHistoryCutCharge_le_cost targets adversary q) le_rfl).trans
    (sampledNativeFtsOts_add_fts_charge_le_q adversary q)

theorem sampledNativeFtsHistoryCut_add_fts_hit_le_query_rate
    (targets : Finset Position) (adversary : Adversary) (q : Nat) :
    sampledNativeFtsHistoryCutCharge targets adversary q * (Fintype.card Digest : ENNReal)⁻¹ +
      sampledJointRetainedFtsHitRisk adversary q ≤ (q : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ :=
  (add_le_add (mul_le_mul' (sampledNativeFtsHistoryCutCharge_le_cost targets adversary q) le_rfl) le_rfl).trans
    (sampledNativeFtsOts_add_fts_hit_le_query_rate adversary q)

end SphincsSecurity.Concrete

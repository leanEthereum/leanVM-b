import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.FtsProbeCacheCharge
import SphincsSecurity.Proof.OtsProbeGroupedTerminal
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassification

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

noncomputable def ftsOpeningQueryReserve (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (input : HashInput) : ℝ≥0∞ :=
  FtsProbeSimulation.ftsHashQueryCharge secretKey.parameter cache input * (4 / 3)

noncomputable def otsOpeningQueryReserve (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (input : HashInput) : ℝ≥0∞ :=
  residualPrimitiveQueryCharge secretKey cache input - ftsOpeningQueryReserve secretKey cache input

def residualOtsOpeningEvent (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState) : Prop :=
  result.1.2.2 = true ∧ ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
    ¬ViewedEncodingCollisionWitness parameter otsSecret ftsSecret result ∧
    cleanOtsOpeningEvent parameter otsSecret ftsSecret result

theorem ftsOpeningQueryReserve_le_residual (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (input : HashInput) :
    ftsOpeningQueryReserve secretKey cache input ≤ residualPrimitiveQueryCharge secretKey cache input :=
  (mul_le_mul' le_rfl (show (4 / 3 : ℝ≥0∞) ≤ 2 by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num)).trans
    (FtsProbeSimulation.ftsHashQueryCharge_mul_two_le_residual secretKey cache input)

theorem openingQueryReserve_add (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) :
    ftsOpeningQueryReserve secretKey cache input + otsOpeningQueryReserve secretKey cache input =
      residualPrimitiveQueryCharge secretKey cache input :=
  add_tsub_cancel_of_le (ftsOpeningQueryReserve_le_residual secretKey cache input)

theorem sampled_ftsOpeningQueryReserve_eq (adversary : Adversary) :
    sampledQueryCharge ftsOpeningQueryReserve adversary =
      (4 / 3 : ℝ≥0∞) * sampledQueryCharge
        (fun secretKey => FtsProbeSimulation.ftsHashQueryCharge secretKey.parameter) adversary := by
  unfold sampledQueryCharge ftsOpeningQueryReserve
  simp only [expectedQueryCharge_mul]
  simp_rw [← mul_assoc, ENNReal.tsum_mul_right]
  exact mul_comm _ _

end SphincsSecurity.Concrete

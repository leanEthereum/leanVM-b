import SphincsSecurity.Proof.SettledEncodingReserve
import SphincsSecurity.Proof.SampledSigningReserve

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

noncomputable def sampledSettledEncodingReserve (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        ∑' initial, Pr[= initial | initializeRoot parameter table (curryFtsTableEquiv ftsSecret) q fuel] *
          expectedBeforeFailureOuterCharge (parentException parameter table (curryFtsTableEquiv ftsSecret))
            (settledEncodingQueryReserve (secretKey parameter initial.2.1 table (curryFtsTableEquiv ftsSecret)))
            parameter initial.2.1 table (curryFtsTableEquiv ftsSecret)
            (retainedComputation adversary parameter initial.2.1 q) initial.1 initial.2.2 false initial.1.isNone

theorem sampledBeforeFailureStructural_add_signingNonEncoding_add_settledEncoding_le (adversary : Adversary) (q fuel : Nat) :
    sampledBeforeFailureStructuralCharge adversary q fuel + sampledSigningNonEncodingReserve adversary q fuel +
      sampledSettledEncodingReserve adversary q fuel ≤
      sampledBeforeFailureHashCharge nonMessageHashCharge adversary q fuel +
        sampledBeforeFailureSelectedCharge NonMessageNonSecretHashInput adversary q fuel := by
  unfold sampledSettledEncodingReserve sampledBeforeFailureStructuralCharge initializedBeforeFailureStructuralCharge sampledSigningNonEncodingReserve
    sampledBeforeFailureHashCharge sampledBeforeFailureSelectedCharge
  rw [← ENNReal.tsum_add, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro parameter
  rw [← mul_add, ← mul_add, ← mul_add, ← ENNReal.tsum_add, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro ftsSecret
  rw [← mul_add, ← mul_add, ← mul_add, ← ENNReal.tsum_add, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro table
  rw [← mul_add, ← mul_add, ← mul_add, ← ENNReal.tsum_add, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro initial
  rw [← mul_add, ← mul_add, ← mul_add]
  exact mul_le_mul' le_rfl (beforeFailureStructural_add_signingNonEncoding_add_settledEncoding_le
    (parentException parameter table (curryFtsTableEquiv ftsSecret)) parameter initial.2.1 table (curryFtsTableEquiv ftsSecret)
    (retainedComputation adversary parameter initial.2.1 q) initial.1 initial.2.2 false initial.1.isNone)

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

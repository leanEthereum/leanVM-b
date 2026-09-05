import SphincsSecurity.Proof.EncodingPrehitMonitor
import SphincsSecurity.Proof.JointPrimitiveQueryBudget

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

structure EncodingPrehitGameResult where
  secrets : SampledSecrets
  verdict : Bool
  cache : QueryCache HashSpec
  prehit : Bool

def EncodingPrehitGameResult.Bad (result : EncodingPrehitGameResult) : Prop :=
  result.prehit = true ∨
  SphincsSecurity.Bad result.secrets.parameter result.secrets.otsSecret result.secrets.ftsSecret result.cache ∨
  EncodingBad result.cache (primitiveAccountingKey result.secrets.parameter result.secrets.otsSecret result.secrets.ftsSecret)

noncomputable def sampledEncodingPrehitGame (adversary : Adversary) : ProbComp EncodingPrehitGameResult := do
  let secrets ← sampleSecrets
  (fun result => ⟨secrets, result.1.1, result.1.2, result.2⟩) <$>
    TightEncoding.runEncodingPrehitMonitor
      (primitiveAccountingKey secrets.parameter secrets.otsSecret secrets.ftsSecret)
      (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret) ∅ false

theorem sampledEncodingPrehitGame_verdict_projection (adversary : Adversary) :
    EncodingPrehitGameResult.verdict <$> sampledEncodingPrehitGame adversary = sampledGame adversary := by
  unfold sampledEncodingPrehitGame sampledGame
  rw [map_bind]
  apply bind_congr
  intro secrets
  rw [Functor.map_map, StateT.run'_eq]
  rw [← TightEncoding.runEncodingPrehitMonitor_project
    (primitiveAccountingKey secrets.parameter secrets.otsSecret secrets.ftsSecret)
    (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret) ∅ false,
    Functor.map_map]

theorem probEvent_sampledEncodingPrehitGame_bad_le_queryCharge (adversary : Adversary) :
    Pr[EncodingPrehitGameResult.Bad | sampledEncodingPrehitGame adversary] ≤
    sampledQueryCharge TightEncoding.refinedStructuralEncodingQueryCharge adversary *
      (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  unfold sampledEncodingPrehitGame sampledQueryCharge
  rw [probEvent_bind_eq_tsum, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro secrets
  rw [mul_assoc]
  apply mul_le_mul' le_rfl
  rw [probEvent_map]
  exact TightEncoding.probEvent_prehit_or_bad_or_encodingBad_le_queryCharge
    (primitiveAccountingKey secrets.parameter secrets.otsSecret secrets.ftsSecret)
    (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret)

end SphincsSecurity.Concrete

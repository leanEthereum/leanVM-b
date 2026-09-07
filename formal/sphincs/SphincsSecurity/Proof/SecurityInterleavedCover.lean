import SphincsSecurity.Proof.InterleavedCoverGame
import SphincsSecurity.Proof.LiveObservedMessageResidual
import SphincsSecurity.Proof.SecurityJointMessageReserve

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

theorem probEvent_original_residual_le_actual_validObservedCover
    (adversary : Adversary) (parameter : PublicParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) :
    Pr[fun result => retainedNonSecretResidual (tableSecrets parameter otsTable ftsTable, result) |
      originalParentRecords adversary parameter otsTable ftsTable] ≤
        Pr[fun result => SigningTranscript.Valid result.1.2.1.2 ∧
          ObservedFewTimeCover (messageAnswers parameter result.2)
          result.1.1 result.1.2.1.2 result.1.2.1.1 |
            actualRetainedGameAfterSecrets adversary parameter
              (tableSecrets parameter otsTable ftsTable).otsSecret ftsTable] := by
  let secrets := tableSecrets parameter otsTable ftsTable
  let event : RetainedGameLogResult → Prop := fun result =>
    SigningTranscript.Valid result.2.2 ∧ ObservedFewTimeCover (messageAnswers parameter result.2.1) result.1.1 result.2.2 result.1.2.1
  have hview : Pr[fun result => retainedNonSecretResidual (secrets, result) |
      originalParentRecords adversary parameter otsTable ftsTable] ≤
        Pr[event ∘ viewedGameLogProjection |
          gameAfterSecretsWithViewTrace adversary parameter secrets.otsSecret secrets.ftsSecret] := by
    apply probEvent_le_of_relTriple (relTriple_and_right_support
      (relTriple_firstParentRetained_viewed_log adversary secrets.parameter secrets.otsSecret secrets.ftsSecret))
    intro left right hrel hleft
    have hobserved := retainedNonSecretResidual_observed_of_log adversary secrets left right hrel.1 hrel.2 hleft
    have hvalid : SigningTranscript.Valid left.1.1.2.1.2 := by
      have hwin := hobserved.1
      simp only [OtsProbeSimulation.retainedRestVerdict, Bool.and_eq_true, decide_eq_true_eq] at hwin
      exact hwin.1.1
    have hlog : left.1.1.2.1.2 = right.2.trace.signing.toSigningLog :=
      congrArg (fun value => value.2.2) hrel.1
    have hvalid' : SigningTranscript.Valid right.2.trace.signing.toSigningLog := hlog ▸ hvalid
    refine ⟨hvalid', ?_⟩
    exact messageOrForestEvent_observedCover adversary parameter secrets.otsSecret secrets.ftsSecret right hrel.2
      (messageOrForestEvent_of_retained_log adversary secrets left right hrel.1 hrel.2 hleft)
  have hproject := congrArg (fun computation => Pr[event | computation])
    (gameAfterSecretsWithViewTrace_actualRetained_projection adversary parameter secrets.otsSecret ftsTable)
  simp only [probEvent_map] at hproject
  exact hview.trans_eq hproject

theorem probEvent_liveNonSecretResidual_le_interleavedCharge
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127)
    (parameter : PublicParameter) (hp : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    Pr[LiveNonSecretResidual parameter otsTable ftsTable |
      runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] ≤
        expectedRetainedCoverCharge adversary parameter (tableSecrets parameter otsTable ftsTable).otsSecret ftsTable q := by
  apply (probEvent_liveNonSecretResidual_le_original adversary q hq parameter hp otsTable ftsTable hfts fuel).trans
  apply (probEvent_original_residual_le_actual_validObservedCover adversary parameter otsTable ftsTable).trans
  exact probEvent_actualRetained_validObservedCover_le_charge_of_hashQueryBound adversary parameter hp _
    (OtsProbeSimulation.mem_support_sampleOtsSecrets_all _) ftsTable hfts q hqMax hq

noncomputable def sampledRetainedCoverCharge (adversary : Adversary) (q : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        expectedRetainedCoverCharge adversary parameter
          (tableSecrets parameter table (curryFtsTableEquiv ftsSecret)).otsSecret (curryFtsTableEquiv ftsSecret) q

theorem sampledLiveNonSecretResidual_le_interleavedCharge
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledLiveNonSecretResidual adversary q fuel ≤ sampledRetainedCoverCharge adversary q := by
  unfold sampledLiveNonSecretResidual sampledRetainedCoverCharge
  apply ENNReal.tsum_le_tsum
  intro parameter
  by_cases hp : parameter ∈ support sampleParameter
  · apply mul_le_mul' le_rfl
    apply ENNReal.tsum_le_tsum
    intro ftsSecret
    by_cases hfts : ftsSecret ∈ support sampleFtsSecrets
    · apply mul_le_mul' le_rfl
      apply ENNReal.tsum_le_tsum
      intro table
      apply mul_le_mul' le_rfl
      exact probEvent_liveNonSecretResidual_le_interleavedCharge adversary q hq hqMax parameter hp table
        (curryFtsTableEquiv ftsSecret) hfts fuel
    · rw [probOutput_eq_zero_of_not_mem_support hfts, zero_mul, zero_mul]
  · rw [probOutput_eq_zero_of_not_mem_support hp, zero_mul, zero_mul]

theorem forgeAdvantage_add_messageReserves_le_interleavedCharge
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary +
      (sampledSelectedJointQueryCharge MessageHashInput adversary q + sampledBeforeFailureHashCharge messageHashCharge adversary q (q + 1)) *
        (Fintype.card Digest : ENNReal)⁻¹ ≤
      (sampledBeforeFailureRestHashCharge adversary q (q + 1) + (q : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ +
      (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) + sampledRetainedCoverCharge adversary q :=
  (forgeAdvantage_add_messageReserves_le_joint_beforeFailureBudget_live adversary q hq hqMax).trans
    (add_le_add le_rfl (sampledLiveNonSecretResidual_le_interleavedCharge adversary q hq hqMax (q + 1)))

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

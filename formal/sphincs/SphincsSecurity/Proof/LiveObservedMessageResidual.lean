import SphincsSecurity.Proof.ObservedMessageTerminal
import SphincsSecurity.Proof.SecurityLiveNonSecretResidual
import SphincsSecurity.Proof.JointProbeInitializedMessageAnswers

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable OtsProbeSimulation.maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

theorem original_retained_residual_observed
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (result) (hr : result ∈ support (originalParentRecords adversary parameter otsTable ftsTable))
    (hresidual : retainedNonSecretResidual (tableSecrets parameter otsTable ftsTable, result)) :
    ObservedRetainedCover result.1.1 (messageAnswers parameter result.1.2) := by
  let secrets := tableSecrets parameter otsTable ftsTable
  have hrel := relTriple_and_right_support
    (relTriple_firstParentRetained_viewed_log adversary secrets.parameter secrets.otsSecret secrets.ftsSecret)
  have hbad : Pr[fun left => retainedNonSecretResidual (secrets, left) ∧
        ¬ ObservedRetainedCover left.1.1 (messageAnswers parameter left.1.2) |
      originalParentRecords adversary parameter otsTable ftsTable] ≤
      Pr[fun _ => False | gameAfterSecretsWithViewTrace adversary secrets.parameter secrets.otsSecret secrets.ftsSecret] := by
    apply probEvent_le_of_relTriple hrel
    intro left right hrelation hleft
    exact hleft.2 (retainedNonSecretResidual_observed_of_log adversary secrets left right hrelation.1 hrelation.2 hleft.1)
  have hzero : Pr[fun left => retainedNonSecretResidual (secrets, left) ∧
        ¬ ObservedRetainedCover left.1.1 (messageAnswers parameter left.1.2) |
      originalParentRecords adversary parameter otsTable ftsTable] = 0 := le_antisymm (by simpa using hbad) bot_le
  by_contra hnot
  exact (probEvent_eq_zero_iff.mp hzero) result hr ⟨hresidual, hnot⟩

theorem liveNonSecretResidual_observed
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hp : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat)
    (result) (hr : result ∈ support (runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel))
    (hresidual : LiveNonSecretResidual parameter otsTable ftsTable result) :
    ∃ value, result.1.2.1.1 = some value ∧ ObservedRetainedCover value (messageAnswers parameter result.1.2.1.2) := by
  obtain ⟨hfailed, hhit, value, hv, hresidual⟩ := hresidual
  refine ⟨value, hv, ?_⟩
  have hzero : Pr[fun left => retainedNonSecretResidual (tableSecrets parameter otsTable ftsTable, left) ∧
        ¬ ObservedRetainedCover left.1.1 (messageAnswers parameter left.1.2) |
      originalParentRecords adversary parameter otsTable ftsTable] = 0 := by
    apply probEvent_eq_zero_iff.mpr
    intro left hl hbad
    exact hbad.2 (original_retained_residual_observed adversary parameter otsTable ftsTable left hl hbad.1)
  have hm := probEvent_originalRecords_eq_retained adversary q hq parameter hp otsTable ftsTable hfts fuel
    (fun left => retainedNonSecretResidual (tableSecrets parameter otsTable ftsTable, (left, none)) ∧
      ¬ ObservedRetainedCover left.1 (messageAnswers parameter left.2))
  change Pr[fun left => retainedNonSecretResidual (tableSecrets parameter otsTable ftsTable, left) ∧
    ¬ ObservedRetainedCover left.1.1 (messageAnswers parameter left.1.2) | _] = _ at hm
  rw [hm] at hzero
  by_contra hnot
  exact (probEvent_eq_zero_iff.mp hzero) result hr ⟨value, hv, hresidual, hnot⟩

def ObservedOptionalRetainedCover (value : Option RetainedGameResult) (answers : HashInput → Option HashOutput) : Prop :=
  ∃ returned, value = some returned ∧ ObservedRetainedCover returned answers

noncomputable def jointSourceRetained (adversary : Adversary) (parameter : PublicParameter) (q : Nat) : JointSource (Option RetainedGameResult) :=
  jointSourceNativeBlock OtsProbeSimulation.maskedPublishedTreeRoot >>= fun root =>
    jointSourceComputation parameter root (retainedComputation adversary parameter root q)

noncomputable def erasedObservedRetainedCoverRisk (adversary : Adversary) (parameter : PublicParameter) (ftsTable : Coordinate → Digest) (q : Nat) : ENNReal :=
  Pr[JointHistoryReturned (fun value => ObservedOptionalRetainedCover value.1 (messageAnswers parameter (ordinaryQueryCache value.2.2))) |
    AdaptiveRevealProbe.runDetailed ftsTable AdaptiveRevealProbe.State.empty q
      (runJointErasedHistory ((jointSourceRetained adversary parameter q).run
        (OtsProbeSimulation.emptySplitHashCache, emptySplitHashCache)) (OtsProbeSimulation.ensuredInitialContext ∅) 0 [])]

theorem liveNonSecretResidual_le_erasedObservedCover
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hp : parameter ∈ support sampleParameter) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    (∑' otsTable, Pr[= otsTable | OtsProbeSimulation.sampleOtsHashTable] *
      Pr[LiveNonSecretResidual parameter otsTable ftsTable |
        runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel]) ≤
      erasedObservedRetainedCoverRisk adversary parameter ftsTable q := by
  calc
    _ ≤ ∑' otsTable, Pr[= otsTable | OtsProbeSimulation.sampleOtsHashTable] *
        Pr[fun result => ObservedOptionalRetainedCover result.1.2.1.1 (messageAnswers parameter result.1.2.1.2) ∧
          result.1.2.2 = false ∧ result.2 = false |
          runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] := by
      apply ENNReal.tsum_le_tsum
      intro otsTable
      apply mul_le_mul' le_rfl
      exact probEvent_mono fun result hr hresidual =>
        ⟨liveNonSecretResidual_observed adversary q hq parameter hp otsTable ftsTable hfts fuel result hr hresidual, hresidual.2.1, hresidual.1⟩
    _ ≤ _ := by
      simp only [runRetainedWithFailure, probEvent_bind_eq_tsum]
      exact probEvent_sampled_initialized_live_message_value_le_erasedHistory
        (fun otsTable => parentException parameter otsTable ftsTable) parameter ftsTable
        (fun root => retainedComputation adversary parameter root q) ObservedOptionalRetainedCover q fuel
        (fun root => retainedComputation_hashBound adversary parameter root q)

noncomputable def sampledErasedObservedRetainedCoverRisk (adversary : Adversary) (q : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      erasedObservedRetainedCoverRisk adversary parameter (curryFtsTableEquiv ftsSecret) q

theorem sampledLiveNonSecretResidual_le_erasedObservedCover
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (fuel : Nat) :
    sampledLiveNonSecretResidual adversary q fuel ≤ sampledErasedObservedRetainedCoverRisk adversary q := by
  unfold sampledLiveNonSecretResidual sampledErasedObservedRetainedCoverRisk
  apply ENNReal.tsum_le_tsum
  intro parameter
  by_cases hp : parameter ∈ support sampleParameter
  · apply mul_le_mul' le_rfl
    apply ENNReal.tsum_le_tsum
    intro ftsSecret
    exact mul_le_mul' le_rfl (liveNonSecretResidual_le_erasedObservedCover adversary q hq parameter hp
      (curryFtsTableEquiv ftsSecret) (mem_support_sampleFtsSecrets ftsSecret) fuel)
  · rw [probOutput_eq_zero_of_not_mem_support hp, zero_mul, zero_mul]

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

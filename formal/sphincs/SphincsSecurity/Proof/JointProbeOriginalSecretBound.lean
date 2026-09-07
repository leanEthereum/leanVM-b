import SphincsSecurity.Proof.JointProbeOriginalOtsWitness
import SphincsSecurity.Proof.JointProbeOriginalOtsParentRetained

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex FirstOtsParentRecord WinningRetainedVerifyProbeAfterOtsSecret)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

def SecretWitness (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (result : RetainedGameResult × QueryCache HashSpec) : Prop :=
  WinningRetainedVerifyProbeAfterOtsSecret parameter otsSecret ftsSecret result ∨
    RetainedUncoveredFtsSecretWitness parameter otsSecret (fun coordinate => ftsSecret coordinate.1 coordinate.2.1 coordinate.2.2) result

theorem clean_secretWitness_imp_failure
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (hots : otsTable ∈ support OtsProbeSimulation.sampleOtsHashTable)
    (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat)
    (result) (hresult : result ∈ support (runRetainedWithFailure exception adversary parameter otsTable ftsTable q fuel))
    (hclean : result.1.2.2 = false) (value : RetainedGameResult) (hvalue : result.1.2.1.1 = some value)
    (hwitness : SecretWitness parameter (OtsProbeSimulation.tableOtsSecret (OtsProbeSimulation.extendStartTable otsTable))
      (fun index tree leaf => ftsTable (index, tree, leaf)) (value, result.1.2.1.2)) : result.2 = true := by
  rcases hwitness with hotsWitness | hftsWitness
  · apply runRetainedWithFailure_clean_otsWitness_imp_failure exception adversary q hq parameter hparameter otsTable ftsTable hfts fuel result hresult
    refine ⟨hclean, value, hvalue, ?_⟩
    exact (OtsProbeSimulation.winningRetainedVerifyProbe_congr_tableOtsSecret parameter _ _ _
      (OtsProbeSimulation.tableOtsSecret_tableOfOtsSecret _) _).mp hotsWitness
  · have heq : (fun coordinate : Coordinate => ftsTable (coordinate.1, coordinate.2.1, coordinate.2.2)) = ftsTable := by
      funext ⟨index, tree, leaf⟩
      rfl
    change RetainedUncoveredFtsSecretWitness parameter
      (OtsProbeSimulation.tableOtsSecret (OtsProbeSimulation.extendStartTable otsTable))
      (fun coordinate => ftsTable (coordinate.1, coordinate.2.1, coordinate.2.2)) (value, result.1.2.1.2) at hftsWitness
    rw [heq] at hftsWitness
    exact runRetainedWithFailure_clean_ftsWitness_imp_failure exception adversary q hq parameter hparameter otsTable hots ftsTable hfts fuel
      result hresult ⟨hclean, value, hvalue, hftsWitness⟩

theorem probEvent_original_firstOtsOrCleanSecret_le_sharedFailure
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (hots : otsTable ∈ support OtsProbeSimulation.sampleOtsHashTable)
    (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    Pr[FirstOtsOrClean parameter (SecretWitness parameter
        (OtsProbeSimulation.tableOtsSecret (OtsProbeSimulation.extendStartTable otsTable))
        (fun index tree leaf => ftsTable (index, tree, leaf))) | originalParentRecords adversary parameter otsTable ftsTable] ≤
    Pr[fun result => result.2 = true | runRetainedWithFailure (parentException parameter otsTable ftsTable)
      adversary parameter otsTable ftsTable q fuel] := by
  let witness := SecretWitness parameter (OtsProbeSimulation.tableOtsSecret (OtsProbeSimulation.extendStartTable otsTable))
    (fun index tree leaf => ftsTable (index, tree, leaf))
  let bad := fun result : Option RetainedGameResult × QueryCache HashSpec => ∃ value, result.1 = some value ∧ witness (value, result.2)
  have h := probEvent_firstOtsOrClean_le_runRetainedWithFailure (parentException parameter otsTable ftsTable)
    adversary parameter otsTable ftsTable (fun _ _ _ _ h => h.2) q fuel bad
  rw [firstRecordedRetained_parent_eq adversary q hq parameter hparameter otsTable ftsTable hfts, probEvent_map] at h
  have hbound : Pr[fun result => FirstOtsParentRecord parameter result ∨ (result.2 = none ∧ witness result.1) |
      originalParentRecords adversary parameter otsTable ftsTable] ≤
      Pr[SharedFailureOrClean bad | runRetainedWithFailure (parentException parameter otsTable ftsTable)
        adversary parameter otsTable ftsTable q fuel] := by
    simpa only [FirstOtsOrClean, FirstOtsParentRecord, Function.comp_def, bad, Option.some.injEq, exists_eq_left'] using h
  apply hbound.trans
  apply probEvent_mono
  intro result hr hevent
  rcases hevent with hf | ⟨hc, value, hv, hw⟩
  · exact hf
  · exact clean_secretWitness_imp_failure (parentException parameter otsTable ftsTable) adversary q hq parameter hparameter otsTable hots
      ftsTable hfts fuel result hr hc value hv hw

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

import SphincsSecurity.Proof.JointProbeOriginalOtsParentAdaptive
import SphincsSecurity.Proof.JointProbeOriginalParentFailure

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex FirstOtsParentRecord)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

noncomputable def firstRecordedRetained
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q : Nat) : ProbComp ((Option RetainedGameResult × QueryCache HashSpec) × Option ExceptionRecord) :=
  originalRoot parameter otsTable >>= fun initial => runFirstException exception
    (simulateQ (expandedAdversaryImpl (secretKey parameter initial.1 otsTable ftsTable))
      (retainedComputation adversary parameter initial.1 q)) initial.2 none

private theorem expected_evalDist_eq (computation : ProbComp α) (cost : α → ENNReal) :
    (∑' value, Pr[= value | evalDist computation] * cost value) =
      ∑' value, Pr[= value | computation] * cost value := rfl

theorem probEvent_firstOtsOrClean_le_runRetainedWithFailure
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hparent : ∀ root cache input answer, exception cache input answer →
      ParentSettlement parameter (secretKey parameter root otsTable ftsTable).otsSecret
        (secretKey parameter root otsTable ftsTable).ftsSecret cache input answer)
    (q fuel : Nat) (bad : Option RetainedGameResult × QueryCache HashSpec → Prop) :
    Pr[FirstOtsOrClean parameter bad | firstRecordedRetained exception adversary parameter otsTable ftsTable q] ≤
    Pr[SharedFailureOrClean bad | runRetainedWithFailure exception adversary parameter otsTable ftsTable q fuel] := by
  rw [firstRecordedRetained, probEvent_bind_eq_tsum]
  rw [← expected_evalDist_eq (originalRoot parameter otsTable),
    ← initializeRoot_original parameter otsTable ftsTable q fuel, tsum_probOutput_map_mul,
    runRetainedWithFailure, probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro initial
  by_cases hi : initial ∈ support (initializeRoot parameter otsTable ftsTable q fuel)
  · apply mul_le_mul' le_rfl
    cases hf : initial.1 with
    | none =>
        have hone : Pr[SharedFailureOrClean bad | runWithFailure exception parameter initial.2.1 otsTable ftsTable
            (retainedComputation adversary parameter initial.2.1 q) none initial.2.2 false true] = 1 := by
          apply probEvent_eq_one_iff.mpr
          exact ⟨runWithFailure_probFailure_eq_zero exception parameter initial.2.1 otsTable ftsTable _ _ _ _ _,
            fun result hr => Or.inl (runWithFailure_failed exception parameter initial.2.1 otsTable ftsTable _ _ _ _ result hr)⟩
        rw [Option.isNone_none, hone]
        exact probEvent_le_one
    | some frame =>
        have hv := initializeRoot_valid parameter otsTable ftsTable q fuel initial hi frame hf
        apply probEvent_firstOtsOrClean_le_runWithFailure exception parameter initial.2.1 otsTable ftsTable
          (hparent initial.2.1) _ frame initial.2.2 hv.2 _
          (initializeRoot_computed parameter otsTable ftsTable q fuel initial hi frame hf) bad
        rw [hv.1.1]
        exact retainedComputation_hashBound adversary parameter initial.2.1 q
  · rw [probOutput_eq_zero_of_not_mem_support hi, zero_mul, zero_mul]

noncomputable def originalParentRecords
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) :=
  runFirstException (parentException parameter otsTable ftsTable)
    (OtsProbeSimulation.retainedAfterSecretsComputation adversary parameter
      (OtsProbeSimulation.tableOtsSecret (OtsProbeSimulation.extendStartTable otsTable))
      (fun index tree leaf => ftsTable (index, tree, leaf))) ∅ none

theorem firstRecordedRetained_parent_eq
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) :
    firstRecordedRetained (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q =
      (fun result => ((some result.1.1, result.1.2), result.2)) <$> originalParentRecords adversary parameter otsTable ftsTable := by
  let otsSecret := OtsProbeSimulation.tableOtsSecret (OtsProbeSimulation.extendStartTable otsTable)
  let ftsSecret := fun index tree leaf => ftsTable (index, tree, leaf)
  let key := primitiveAccountingKey parameter otsSecret ftsSecret
  let exception := parentException parameter otsTable ftsTable
  let computation : OracleComp OracleWorld Digest := liftM (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree) : OracleComp HashSpec Digest)
  have hroot : runFirstException exception computation ∅ none =
      (fun result => (result, none)) <$> originalRoot parameter otsTable := by
    change runFirstException exception computation ∅ none =
      (fun result => (result, none)) <$> (simulateQ romImpl computation).run ∅
    rw [← runFirstException_project exception computation ∅ none, Functor.map_map]
    conv_lhs => rw [← id_map (runFirstException exception computation ∅ none)]
    simp only [map_eq_bind_pure_comp]
    apply _root_.OracleComp.bind_congr_of_forall_mem_support
    intro result hr
    have hn := runFirstException_treeRoot_no_record key exception (fun _ _ _ h => h.2) topLayer rootTree hr
    simp only [Function.comp_apply, id_eq]
    rw [← hn]
  rw [firstRecordedRetained, originalParentRecords, OtsProbeSimulation.retainedAfterSecretsComputation,
    runFirstException_bind, hroot, map_bind, bind_map_left]
  apply bind_congr
  rintro ⟨root, cache⟩
  dsimp only
  have hcap := OtsProbeSimulation.simulateQ_expandedRetained_capOuterHashQueries adversary q hq parameter hparameter otsTable
    (fun index tree leaf => ftsTable (index, tree, leaf)) hfts root
  change simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) _ =
    some <$> simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) _ at hcap
  rw [retainedComputation, simulateQ_map]
  change runFirstException (parentException parameter otsTable ftsTable)
    ((Option.map (fun rest => (root, rest))) <$> simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable))
      (OtsProbeSimulation.capOuterHashQueries (OtsProbeSimulation.retainedGameRestComputation adversary ⟨root, parameter⟩) q)) cache none = _
  rw [hcap]
  simp only [runFirstException_map, bind_pure_comp, Functor.map_map]
  rfl

theorem probEvent_original_firstOtsOrCleanFts_le_sharedFailure
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (hots : otsTable ∈ support OtsProbeSimulation.sampleOtsHashTable)
    (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    Pr[FirstOtsOrClean parameter (RetainedUncoveredFtsSecretWitness parameter
        (OtsProbeSimulation.tableOtsSecret (OtsProbeSimulation.extendStartTable otsTable)) ftsTable) |
      originalParentRecords adversary parameter otsTable ftsTable] ≤
    Pr[fun result => result.2 = true | runRetainedWithFailure (parentException parameter otsTable ftsTable)
      adversary parameter otsTable ftsTable q fuel] := by
  let bad := fun result : Option RetainedGameResult × QueryCache HashSpec => ∃ value, result.1 = some value ∧
    RetainedUncoveredFtsSecretWitness parameter
      (OtsProbeSimulation.tableOtsSecret (OtsProbeSimulation.extendStartTable otsTable)) ftsTable (value, result.2)
  have h := probEvent_firstOtsOrClean_le_runRetainedWithFailure (parentException parameter otsTable ftsTable)
    adversary parameter otsTable ftsTable (fun _ _ _ _ h => h.2) q fuel bad
  rw [firstRecordedRetained_parent_eq adversary q hq parameter hparameter otsTable ftsTable hfts, probEvent_map] at h
  have hbound : Pr[FirstOtsOrClean parameter (RetainedUncoveredFtsSecretWitness parameter
      (OtsProbeSimulation.tableOtsSecret (OtsProbeSimulation.extendStartTable otsTable)) ftsTable) |
      originalParentRecords adversary parameter otsTable ftsTable] ≤
      Pr[SharedFailureOrClean bad | runRetainedWithFailure (parentException parameter otsTable ftsTable)
        adversary parameter otsTable ftsTable q fuel] := by
    change Pr[fun result => FirstOtsParentRecord parameter result ∨ (result.2 = none ∧
      RetainedUncoveredFtsSecretWitness parameter
        (OtsProbeSimulation.tableOtsSecret (OtsProbeSimulation.extendStartTable otsTable)) ftsTable result.1) | _] ≤ _
    simpa only [FirstOtsOrClean, FirstOtsParentRecord, Function.comp_def, bad, Option.some.injEq, exists_eq_left'] using h
  apply hbound.trans
  apply probEvent_mono
  intro result hr hevent
  rcases hevent with hf | hc
  · exact hf
  · exact runRetainedWithFailure_clean_ftsWitness_imp_failure (parentException parameter otsTable ftsTable)
      adversary q hq parameter hparameter otsTable hots ftsTable hfts fuel result hr hc

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

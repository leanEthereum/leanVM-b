import SphincsSecurity.Proof.DeficitStructuralRun
import SphincsSecurity.Proof.JointProbeCollisionInitialization
import SphincsSecurity.Proof.JointFailureCacheCap
import SphincsSecurity.Proof.RootCache

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable

noncomputable def runRetainedWithDeficit
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) : SPMF ((Option Frame × ((Option RetainedGameResult × QueryCache HashSpec) × Bool)) × Bool) :=
  initializeRoot parameter otsTable ftsTable q fuel >>= fun initial =>
    runWithFailure
      (deficitStoppingException (secretKey parameter initial.2.1 otsTable ftsTable) (parentException parameter otsTable ftsTable))
      parameter initial.2.1 otsTable ftsTable (retainedComputation adversary parameter initial.2.1 q)
      initial.1 initial.2.2 false initial.1.isNone

theorem runRetainedWithDeficit_originalCapped
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) :
    (fun result => result.1.2.1) <$> runRetainedWithDeficit adversary parameter otsTable ftsTable q fuel =
      evalDist (originalCappedRetained adversary parameter otsTable ftsTable q) := by
  rw [runRetainedWithDeficit, map_bind]
  simp_rw [runWithFailure_original_cache_projection]
  rw [originalCappedRetained, evalDist_bind, ← initializeRoot_original parameter otsTable ftsTable q fuel, bind_map_left]

theorem runRetainedWithDeficit_originalActual
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    (fun result => result.1.2.1) <$> runRetainedWithDeficit adversary parameter otsTable ftsTable q fuel =
      (fun actual => (some actual.1, actual.2)) <$>
        evalDist (OtsProbeSimulation.actualRetainedGameAfterTable adversary parameter
          (fun index tree leaf => ftsTable (index, tree, leaf)) (OtsProbeSimulation.extendStartTable otsTable)) := by
  rw [runRetainedWithDeficit_originalCapped, originalCappedRetained_eq_actual adversary q hq parameter hparameter otsTable ftsTable hfts,
    evalDist_map]

theorem retainedComputation_expanded_hashBound
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (root : Digest) :
    (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable))
      (retainedComputation adversary parameter root q)).IsQueryBoundP (· matches Sum.inr _) q := by
  have hraw := OtsProbeSimulation.isQueryBoundP_expandedRetained_all_tables_roots adversary q hq parameter hparameter otsTable
    (fun index tree leaf => ftsTable (index, tree, leaf)) hfts root
  change (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable))
    (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP (· matches Sum.inr _) q at hraw
  rw [retainedComputation, simulateQ_map, isQueryBoundP_map_iff,
    OtsProbeSimulation.simulateQ_expanded_capOuterHashQueries _ _ q hraw, isQueryBoundP_map_iff]
  exact hraw

theorem runRetainedWithDeficit_cache_finite
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) (result) (hr : result ∈ support (runRetainedWithDeficit adversary parameter otsTable ftsTable q fuel)) :
    Finite result.1.2.1.2 := by
  rw [runRetainedWithDeficit, mem_support_bind_iff] at hr
  obtain ⟨initial, hi, ht⟩ := hr
  have ha := initializeRoot_original_support parameter otsTable ftsTable q fuel initial hi
  have hfin := finite_cache_of_mem_support _ ∅ initial.2.1 initial.2.2 ha finite_empty
  exact runWithFailure_cache_finite _ parameter initial.2.1 otsTable ftsTable _ initial.1 initial.2.2 false initial.1.isNone hfin result ht

noncomputable def initializedDeficitCollisionCharge
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) : ENNReal :=
  ∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
    expectedBeforeFailureCharge
      (deficitStoppingException (secretKey parameter initial.2.1 otsTable ftsTable) (parentException parameter otsTable ftsTable))
      (collisionSigningStructuralCharge (secretKey parameter initial.2.1 otsTable ftsTable))
      parameter initial.2.1 otsTable ftsTable (retainedComputation adversary parameter initial.2.1 q)
      initial.1 initial.2.2 false initial.1.isNone

theorem expected_deficitCollisionSurvivingStructuralPotential_retained_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    (∑' result, Pr[= result | runRetainedWithDeficit adversary parameter otsTable ftsTable q fuel] *
      collisionSurvivingStructuralPotential (secretKey parameter default otsTable ftsTable) result.1.2.1.2 result.1.2.2 result.2) ≤
      initializedDeficitCollisionCharge adversary parameter otsTable ftsTable q fuel * (Fintype.card Digest : ENNReal)⁻¹ +
        (q : ENNReal) / 2 ^ 223 := by
  let charge := fun initial : Option Frame × (Digest × QueryCache HashSpec) =>
    expectedBeforeFailureCharge
      (deficitStoppingException (secretKey parameter initial.2.1 otsTable ftsTable) (parentException parameter otsTable ftsTable))
      (collisionSigningStructuralCharge (secretKey parameter initial.2.1 otsTable ftsTable))
      parameter initial.2.1 otsTable ftsTable (retainedComputation adversary parameter initial.2.1 q)
      initial.1 initial.2.2 false initial.1.isNone
  rw [runRetainedWithDeficit, tsum_probOutput_bind_mul]
  calc
    _ ≤ ∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
        (charge initial * (Fintype.card Digest : ENNReal)⁻¹ + (q : ENNReal) / 2 ^ 223) := by
      apply ENNReal.tsum_le_tsum
      intro initial
      by_cases hi : initial ∈ support (initializeRoot parameter otsTable ftsTable q fuel)
      · apply mul_le_mul' le_rfl
        let key := secretKey parameter initial.2.1 otsTable ftsTable
        let exception := deficitStoppingException key (parentException parameter otsTable ftsTable)
        have ha := initializeRoot_original_support parameter otsTable ftsTable q fuel initial hi
        have hfin := finite_cache_of_mem_support _ ∅ initial.2.1 initial.2.2 ha finite_empty
        have hz := collisionStructuralRecordPotential_treeRoot_eq_zero key topLayer rootTree initial.2 ha
        cases hf : initial.1 with
        | none =>
            simp only [Option.isNone_none]
            have hzero := expected_collisionSurvivingStructuralPotential_failed_eq_zero exception
              parameter initial.2.1 otsTable ftsTable (retainedComputation adversary parameter initial.2.1 q) none initial.2.2 false
            simp_rw [collisionSurvivingStructuralPotential_root_irrel parameter otsTable ftsTable initial.2.1 default] at hzero
            rw [hzero]
            exact zero_le
        | some frame =>
            have hv := initializeRoot_valid parameter otsTable ftsTable q fuel initial hi frame hf
            have hb : (retainedComputation adversary parameter initial.2.1 q).IsQueryBoundP OtsProbeSimulation.IsOuterHash frame.ftsFuel := by
              rw [hv.1.1]
              exact retainedComputation_hashBound adversary parameter initial.2.1 q
            have hroot := ha
            rw [originalRoot, simulateQ_romImpl_liftM] at hroot
            have hnone := treeRoot_cache_message_none parameter topLayer rootTree (key.otsSecret topLayer rootTree)
              initial.2.1 initial.2.2 hroot
            have h := expected_deficitCollisionSurvivingStructuralPotential_run_le parameter initial.2.1 otsTable ftsTable
              (retainedComputation adversary parameter initial.2.1 q) frame initial.2.2 hfin hv.2 hb
              (initializeRoot_computed parameter otsTable ftsTable q fuel initial hi frame hf) q hqMax
              (retainedComputation_expanded_hashBound adversary q hq parameter hparameter otsTable ftsTable hfts initial.2.1) hnone
            rw [hz, zero_add] at h
            simp_rw [collisionSurvivingStructuralPotential_root_irrel parameter otsTable ftsTable initial.2.1 default] at h
            simpa only [charge, hf, Option.isNone_some] using h
      · rw [probOutput_eq_zero_of_not_mem_support hi, zero_mul, zero_mul]
    _ ≤ _ := by
      simp_rw [mul_add, ENNReal.tsum_add, ← mul_assoc, ENNReal.tsum_mul_right]
      exact add_le_add le_rfl (mul_le_of_le_one_left' tsum_probOutput_le_one)

theorem probEvent_deficitSurvivingStructuralFailure_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    Pr[SurvivingStructuralFailure parameter otsTable ftsTable | runRetainedWithDeficit adversary parameter otsTable ftsTable q fuel] ≤
      initializedDeficitCollisionCharge adversary parameter otsTable ftsTable q fuel * (Fintype.card Digest : ENNReal)⁻¹ +
        (q : ENNReal) / 2 ^ 223 := by
  apply le_trans _ (expected_deficitCollisionSurvivingStructuralPotential_retained_le adversary q hq hqMax parameter hparameter
    otsTable ftsTable hfts fuel)
  rw [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ support (runRetainedWithDeficit adversary parameter otsTable ftsTable q fuel)
  · by_cases he : SurvivingStructuralFailure parameter otsTable ftsTable result
    · rw [if_pos he]
      apply le_mul_of_one_le_right'
      obtain ⟨hf, ho | hb⟩ := he
      · simp [collisionSurvivingStructuralPotential, hf, ho]
      · cases ho : result.1.2.2 with
        | true => simp [collisionSurvivingStructuralPotential, hf]
        | false =>
            simp only [collisionSurvivingStructuralPotential, hf, Bool.false_eq_true, if_false]
            exact collisionStructuralRecordPotential_none_ge_bad (secretKey parameter default otsTable ftsTable) result.1.2.1.2
              (runRetainedWithDeficit_cache_finite adversary parameter otsTable ftsTable q fuel result hr) hb
    · rw [if_neg he]
      exact zero_le
  · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul]
    split_ifs <;> rfl

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

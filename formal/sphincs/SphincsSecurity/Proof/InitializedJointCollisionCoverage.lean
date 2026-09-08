import SphincsSecurity.Proof.JointCollisionCoverageExecution
import SphincsSecurity.Proof.SecurityJointCollisionCoverage
import SphincsSecurity.Proof.CollisionStructuralRootPotential

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

private theorem probOutput_evalDist_eq (computation : ProbComp α) (result : α) :
    Pr[= result | evalDist computation] = Pr[= result | computation] := rfl

theorem expected_initializeRoot_encodingExhaustionReserve
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q fuel : Nat) :
    (∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
      encodingExhaustionBudgetReserve q initial.2.2) = encodingExhaustionBudgetReserve q ∅ := by
  have hm := congrArg (fun computation => ∑' result, Pr[= result | computation] * encodingExhaustionTotalPotential result.2)
    (initializeRoot_original parameter otsTable ftsTable q fuel)
  rw [tsum_probOutput_map_mul] at hm
  have hg : (∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
      encodingExhaustionTotalPotential initial.2.2) = encodingExhaustionTotalPotential ∅ := by
    apply hm.trans
    simpa only [originalRoot, probOutput_evalDist_eq] using expected_encodingExhaustionTotalPotential_run
      (liftM (treeRoot parameter topLayer rootTree
        (fun leafIdx chainIdx => truncateHash (otsTable ⟨topLayer, rootTree, leafIdx, chainIdx⟩)) : OracleComp HashSpec Digest)) ∅
  simp only [encodingExhaustionBudgetReserve]
  simp_rw [mul_left_comm (Pr[= _ | initializeRoot parameter otsTable ftsTable q fuel]), ENNReal.tsum_mul_left]
  rw [hg]

noncomputable def initializedJointCollisionCoverageCharge (adversary : Adversary) (parameter : PublicParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q fuel : Nat) : ENNReal :=
  (1 - min 1 ((q : ENNReal) * initialRawIndexRate q)) *
      Pr[fun initial => initial.1 = none | initializeRoot parameter otsTable ftsTable q fuel] +
    ∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
      expectedJointCollisionCoverageCharge parameter initial.2.1 otsTable ftsTable q
        (unloggedRetainedRestComputation adversary ⟨initial.2.1, parameter⟩) q initial.1 (initial.2.2, []) false initial.1.isNone

noncomputable def initializedJointCollisionCoverageCredit (adversary : Adversary) (parameter : PublicParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q fuel : Nat) : ENNReal :=
  ∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
    expectedJointCollisionCoverageCredit parameter initial.2.1 otsTable ftsTable q
      (unloggedRetainedRestComputation adversary ⟨initial.2.1, parameter⟩) q initial.1 (initial.2.2, []) false initial.1.isNone

theorem expected_initialized_jointCollisionCoverage_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hp : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    (∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
      jointCollisionCoverageBudgetPotential (secretKey parameter initial.2.1 otsTable ftsTable) q q
        (initial.2.2, []) false initial.1.isNone) ≤
      min 1 ((q : ENNReal) * initialRawIndexRate q) +
        (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ +
        (1 - min 1 ((q : ENNReal) * initialRawIndexRate q)) *
          Pr[fun initial => initial.1 = none | initializeRoot parameter otsTable ftsTable q fuel] := by
  let start := min 1 ((q : ENNReal) * initialRawIndexRate q)
  have hphi : (∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
      jointCollisionCoveragePotential (secretKey parameter initial.2.1 otsTable ftsTable) q q
        (initial.2.2, []) false initial.1.isNone) ≤
      start + (1 - start) * Pr[fun initial => initial.1 = none | initializeRoot parameter otsTable ftsTable q fuel] := by
    calc
      _ = ∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
          (start + if initial.1 = none then 1 - start else 0) := by
        apply tsum_congr
        intro initial
        by_cases hi : initial ∈ support (initializeRoot parameter otsTable ftsTable q fuel)
        · have hconditions := initialized_stoppedTarget_conditions adversary q hq parameter hp otsTable ftsTable hfts fuel initial hi
          have ha := initializeRoot_original_support parameter otsTable ftsTable q fuel initial hi
          have hz := collisionStructuralRecordPotential_treeRoot_eq_zero (secretKey parameter initial.2.1 otsTable ftsTable)
            topLayer rootTree initial.2 ha
          have hstart := jointCollisionCoveragePotential_initial (secretKey parameter initial.2.1 otsTable ftsTable)
            q initial.2.2 hconditions.1 hz
          cases hf : initial.1 with
          | none =>
              rw [jointCollisionCoveragePotential_eq_one_of_stopped _ _ _ _ _ _ (by simp), if_pos rfl,
                add_tsub_cancel_of_le (show start ≤ 1 from min_le_left _ _)]
          | some frame =>
              simp only [Option.isNone_some, reduceCtorEq, if_false, add_zero]
              rw [hstart]
        · rw [probOutput_eq_zero_of_not_mem_support hi, zero_mul, zero_mul]
      _ = (∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel]) * start +
          (1 - start) * Pr[fun initial => initial.1 = none | initializeRoot parameter otsTable ftsTable q fuel] := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, probEvent_eq_tsum_ite]
        rw [← ENNReal.tsum_mul_left]
        congr 1
        apply tsum_congr
        intro initial
        split_ifs <;> ring
      _ ≤ _ := add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) le_rfl
  simp only [jointCollisionCoverageBudgetPotential, mul_add, ENNReal.tsum_add]
  rw [expected_initializeRoot_encodingExhaustionReserve]
  exact (add_le_add hphi (encodingExhaustionBudgetReserve_initial_le q)).trans_eq (add_right_comm _ _ _)

theorem expected_retained_jointCollisionCoverage_add_credit_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127)
    (parameter : PublicParameter) (hp : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    (∑' result, Pr[= result | runRetainedWithFailure (parentException parameter otsTable ftsTable)
      adversary parameter otsTable ftsTable q fuel] * retainedJointCollisionCoveragePotential parameter otsTable ftsTable q result) +
      initializedJointCollisionCoverageCredit adversary parameter otsTable ftsTable q fuel ≤
        min 1 ((q : ENNReal) * initialRawIndexRate q) + (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ +
          initializedJointCollisionCoverageCharge adversary parameter otsTable ftsTable q fuel := by
  have hrun : (∑' result, Pr[= result | runRetainedWithFailure (parentException parameter otsTable ftsTable)
      adversary parameter otsTable ftsTable q fuel] * retainedJointCollisionCoveragePotential parameter otsTable ftsTable q result) +
      initializedJointCollisionCoverageCredit adversary parameter otsTable ftsTable q fuel ≤
        ∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
          (jointCollisionCoverageBudgetPotential (secretKey parameter initial.2.1 otsTable ftsTable) q q (initial.2.2, []) false initial.1.isNone +
            expectedJointCollisionCoverageCharge parameter initial.2.1 otsTable ftsTable q
              (unloggedRetainedRestComputation adversary ⟨initial.2.1, parameter⟩) q initial.1 (initial.2.2, []) false initial.1.isNone) := by
    rw [runRetainedWithFailure, tsum_probOutput_bind_mul, initializedJointCollisionCoverageCredit, ← ENNReal.tsum_add]
    apply ENNReal.tsum_le_tsum
    intro initial
    rw [← mul_add]
    by_cases hi : initial ∈ support (initializeRoot parameter otsTable ftsTable q fuel)
    · apply mul_le_mul' le_rfl
      let key := secretKey parameter initial.2.1 otsTable ftsTable
      have hconditions := initialized_stoppedTarget_conditions adversary q hq parameter hp otsTable ftsTable hfts fuel initial hi
      have ha := initializeRoot_original_support parameter otsTable ftsTable q fuel initial hi
      have hfin := finite_cache_of_mem_support _ ∅ initial.2.1 initial.2.2 ha finite_empty
      have hroot := ha
      rw [originalRoot, simulateQ_romImpl_liftM] at hroot
      have hgame := isQueryBoundP_gameAfterSecrets adversary q hq hp
        (OtsProbeSimulation.mem_support_sampleOtsSecrets_all key.otsSecret) hfts
      have hbudget := retainedRoot_expanded_rest_queryBound adversary parameter key.otsSecret ftsTable q hgame initial.2 hroot
      have htrace := OtsProbeSimulation.isQueryBoundP_expandedRetained_all_tables_roots adversary q hq parameter hp otsTable
        (fun index tree leaf => ftsTable (index, tree, leaf)) hfts initial.2.1
      have hvalid : ∀ live, initial.1 = some live → live.Valid parameter otsTable ftsTable initial.2.2 :=
        fun live hlive => (initializeRoot_valid parameter otsTable ftsTable q fuel initial hi live hlive).2
      have hfuel : ∀ live, initial.1 = some live → q ≤ live.ftsFuel := by
        intro live hlive
        rw [(initializeRoot_valid parameter otsTable ftsTable q fuel initial hi live hlive).1.1]
      have hsigned : SigningDigestsCached parameter initial.2.2 initial.2.1 [] := by
        intro entry hentry
        simp only [List.not_mem_nil] at hentry
      rw [runWithFailure_retainedComputation_trace _ adversary parameter initial.2.1 otsTable ftsTable q htrace, tsum_probOutput_map_mul]
      simpa only [retainedJointCollisionCoveragePotential, arrangeRetainedTrace] using
        expected_runWithFailure_jointCollisionCoverage_add_credit_le parameter initial.2.1 otsTable ftsTable q q hqMax
          (unloggedRetainedRestComputation adversary ⟨initial.2.1, parameter⟩) initial.1 (initial.2.2, []) false initial.1.isNone
          hfin hvalid hfuel (initializeRoot_computed parameter otsTable ftsTable q fuel initial hi) rfl hbudget hsigned hconditions.2
    · rw [probOutput_eq_zero_of_not_mem_support hi, zero_mul, zero_mul]
  simp only [mul_add, ENNReal.tsum_add] at hrun
  exact hrun.trans ((add_le_add (expected_initialized_jointCollisionCoverage_le adversary q hq parameter hp otsTable ftsTable hfts fuel)
    le_rfl).trans_eq (add_assoc _ _ _))

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

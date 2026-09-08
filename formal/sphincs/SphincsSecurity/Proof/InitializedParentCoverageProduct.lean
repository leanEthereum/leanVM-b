import SphincsSecurity.Proof.JointParentCoverageProduct
import SphincsSecurity.Proof.SecurityJointTerminalParentRefund
import SphincsSecurity.Proof.InitializedParentReserveConservation

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem terminalParentCoverageOverlap_le_product
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap : Nat) (result) (value : RetainedGameResult) (hv : result.1.2.1.1 = some value) :
    terminalParentCoverageOverlap parameter otsTable ftsTable result ≤
      survivingLogPotential (parentCoverageProduct (secretKey parameter value.1 otsTable ftsTable) cap 0)
        (result.1.2.1.2, value.2.1.2) result.1.2.2 result.2 := by
  rw [terminalParentCoverageOverlap, hv, survivingLogPotential]
  by_cases hstop : (result.1.2.2 || result.2) = true
  · rw [if_pos hstop, terminalPendingParentCount_eq_zero_of_stopped parameter otsTable ftsTable result hstop]
    simp only [Nat.cast_zero, zero_mul, mul_zero, le_refl]
  · rw [if_neg hstop]
    unfold parentCoverageProduct
    apply mul_le_mul' (min_le_min le_rfl (mul_le_mul'
      (completedCoveragePotential_le_remaining (secretKey parameter value.1 otsTable ftsTable) cap 0 _) le_rfl))
    apply mul_le_mul' ?_ le_rfl
    apply Nat.cast_le.mpr
    unfold terminalPendingParentCount
    split_ifs
    · exact le_rfl
    · exact Nat.zero_le _

theorem expected_retained_terminalParentOverlap_le_afterParentRefund
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127)
    (parameter : PublicParameter) (hp : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    (∑' result, Pr[= result | runRetainedWithFailure (parentException parameter otsTable ftsTable)
      adversary parameter otsTable ftsTable q fuel] * terminalParentCoverageOverlap parameter otsTable ftsTable result) ≤
      initializedJointCoverageAfterParentRefund adversary parameter otsTable ftsTable q fuel := by
  rw [runRetainedWithFailure, tsum_probOutput_bind_mul, initializedJointCoverageAfterParentRefund]
  apply le_trans ?_ le_add_self
  apply ENNReal.tsum_le_tsum
  intro initial
  by_cases hi : initial ∈ support (initializeRoot parameter otsTable ftsTable q fuel)
  · apply mul_le_mul' le_rfl
    let key := secretKey parameter initial.2.1 otsTable ftsTable
    have hconditions := initialized_stoppedTarget_conditions adversary q hq parameter hp otsTable ftsTable hfts fuel initial hi
    have ha := initializeRoot_original_support parameter otsTable ftsTable q fuel initial hi
    have hz := survivingFtsParentReserve_treeRoot_eq_zero key topLayer rootTree initial.2 ha
    have hroot := ha
    rw [originalRoot, simulateQ_romImpl_liftM] at hroot
    have hgame := isQueryBoundP_gameAfterSecrets adversary q hq hp
      (OtsProbeSimulation.mem_support_sampleOtsSecrets_all key.otsSecret) hfts
    have hbudget := retainedRoot_expanded_rest_queryBound adversary parameter key.otsSecret ftsTable q hgame initial.2 hroot
    have htrace := OtsProbeSimulation.isQueryBoundP_expandedRetained_all_tables_roots adversary q hq parameter hp otsTable
      (fun index tree leaf => ftsTable (index, tree, leaf)) hfts initial.2.1
    have hsigned : SigningDigestsCached parameter initial.2.2 initial.2.1 [] := by
      intro entry he
      simp only [List.not_mem_nil] at he
    have hrun := expected_parentCoverageProduct_le_afterParentRefund parameter initial.2.1 otsTable ftsTable q q hqMax
      (unloggedRetainedRestComputation adversary ⟨initial.2.1, parameter⟩) initial.1 (initial.2.2, []) false initial.1.isNone
      hbudget hsigned hconditions.2
    have hzero : survivingLogPotential (parentCoverageProduct key q q) (initial.2.2, []) false initial.1.isNone = 0 := by
      change (parentReserve key.parameter key.otsSecret key.ftsSecret (fun position => ¬ OtsProbeSimulation.IsOtsPosition position) initial.2.2 : ENNReal) = 0 at hz
      simp only [survivingLogPotential, parentCoverageProduct, hz, zero_mul, mul_zero, ite_self]
    rw [hzero, zero_add] at hrun
    apply le_trans ?_ hrun
    rw [runWithFailure_retainedComputation_trace _ adversary parameter initial.2.1 otsTable ftsTable q htrace, tsum_probOutput_map_mul]
    apply ENNReal.tsum_le_tsum
    intro result
    exact mul_le_mul' le_rfl (terminalParentCoverageOverlap_le_product parameter otsTable ftsTable q _
      (initial.2.1, arrangeRetainedTrace result.1.2.1.1) rfl)
  · rw [probOutput_eq_zero_of_not_mem_support hi, zero_mul, zero_mul]

theorem sampled_terminalParentOverlap_le_afterParentRefund
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledTerminalParentCoverageOverlap adversary q fuel ≤ sampledJointCoverageAfterParentRefund adversary q fuel := by
  unfold sampledTerminalParentCoverageOverlap sampledJointCoverageAfterParentRefund
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
      exact mul_le_mul' le_rfl (expected_retained_terminalParentOverlap_le_afterParentRefund adversary q hq hqMax parameter hp table
        (curryFtsTableEquiv ftsSecret) hfts fuel)
    · rw [probOutput_eq_zero_of_not_mem_support hfts, zero_mul, zero_mul]
  · rw [probOutput_eq_zero_of_not_mem_support hp, zero_mul, zero_mul]

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

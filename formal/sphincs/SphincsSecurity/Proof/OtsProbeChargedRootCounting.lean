import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeChargedRootSelection
import SphincsSecurity.Proof.OtsProbeLiveHashSelection

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def chargedRootOuterCharge (parameter : PublicParameter)
    (input : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) : ENNReal :=
  knownStructuralRootOuterCharge parameter input context fuel cache * (4 / 3 : ENNReal) +
    materializedEncodingRootOuterCharge parameter input context fuel cache

theorem chargedRootOuterCharge_eq_zero_of_not_hash
    (parameter : PublicParameter) (input : (OracleWorld + SigningSpec).Domain)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (hnot : ¬IsOuterHash input) :
    chargedRootOuterCharge parameter input context fuel cache = 0 := by
  cases input with
  | inl query => cases query <;> simp_all [IsOuterHash, chargedRootOuterCharge, knownStructuralRootOuterCharge, materializedEncodingRootOuterCharge]
  | inr message => simp [chargedRootOuterCharge, knownStructuralRootOuterCharge, materializedEncodingRootOuterCharge]

theorem canonicalSelection_chargedRootCharge
    (parameter : PublicParameter) (selection : Option CanonicalQuerySelection) :
    CanonicalQuerySelection.charge (chargedRootOuterCharge parameter) selection =
      CanonicalQuerySelection.charge (knownStructuralRootOuterCharge parameter) selection * (4 / 3 : ENNReal) +
        CanonicalQuerySelection.charge (materializedEncodingRootOuterCharge parameter) selection := by
  cases selection <;> simp [CanonicalQuerySelection.charge, chargedRootOuterCharge]

theorem sum_targets_chargedRootSelection_probability_le_charge
    (targets : Finset Position) (parameter : PublicParameter) (run : ProbComp (Option CanonicalQuerySelection)) :
    (∑ target ∈ targets, Pr[fun selection => chargedNativeRootSelectionCandidate parameter target selection ≠ none | run]) * (4 / 3 : ENNReal) ≤
      ∑' selection, Pr[= selection | run] * CanonicalQuerySelection.charge (chargedRootOuterCharge parameter) selection := by
  simp_rw [probEvent_eq_tsum_ite]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro selection
  cases selection with
  | none => simp [chargedNativeRootSelectionCandidate, CanonicalQuerySelection.charge]
  | some selection =>
      have hfactor : (∑ target ∈ targets,
          if chargedNativeRootSelectionCandidate parameter target (some selection) ≠ none then Pr[= some selection | run] else 0) =
          Pr[= some selection | run] * (∑ target ∈ targets,
            if chargedNativeRootQueryCandidate parameter target selection.input selection.context ≠ none then (1 : ENNReal) else 0) := by
        rw [Finset.mul_sum]
        simp [chargedNativeRootSelectionCandidate, mul_ite]
      rw [hfactor, mul_assoc]
      exact mul_le_mul' le_rfl (sum_targets_chargedRootQueryCandidate_le_charge targets parameter selection.input
        selection.context selection.fuel selection.cache)

theorem sum_targets_hashSelections_chargedRoot_probability_le_charge
    (targets : Finset Position) (parameter : PublicParameter)
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    (∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
      Pr[fun selection => chargedNativeRootSelectionCandidate parameter target selection ≠ none |
        liveNativeHashQuerySelection impl computation ordinal context fuel table cache]) * (4 / 3 : ENNReal) ≤
      expectedLiveNativeContextCharge impl (chargedRootOuterCharge parameter) computation context fuel table cache := by
  rw [Finset.sum_comm, Finset.sum_mul]
  apply (Finset.sum_le_sum (fun ordinal _ => sum_targets_chargedRootSelection_probability_le_charge targets parameter
    (liveNativeHashQuerySelection impl computation ordinal context fuel table cache))).trans
  exact (ENNReal.sum_le_tsum (Finset.range q)).trans_eq
    (tsum_liveNativeHashQuerySelection_charge impl _ (chargedRootOuterCharge_eq_zero_of_not_hash parameter)
      computation context fuel table cache)

theorem expectedLiveChargedRootCharge_eq_components
    (parameter : PublicParameter)
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    expectedLiveNativeContextCharge impl (chargedRootOuterCharge parameter) computation context fuel table cache =
      expectedLiveNativeContextCharge impl (knownStructuralRootOuterCharge parameter) computation context fuel table cache * (4 / 3 : ENNReal) +
        expectedLiveNativeContextCharge impl (materializedEncodingRootOuterCharge parameter) computation context fuel table cache := by
  have hstructural : ∀ input context fuel cache, ¬IsOuterHash input → knownStructuralRootOuterCharge parameter input context fuel cache = 0 := by
    intro input context fuel cache hnot
    cases input with
    | inl query => cases query <;> simp_all [IsOuterHash, knownStructuralRootOuterCharge]
    | inr message => rfl
  have hencoding : ∀ input context fuel cache, ¬IsOuterHash input → materializedEncodingRootOuterCharge parameter input context fuel cache = 0 := by
    intro input context fuel cache hnot
    cases input with
    | inl query => cases query <;> simp_all [IsOuterHash, materializedEncodingRootOuterCharge]
    | inr message => rfl
  rw [← tsum_liveNativeHashQuerySelection_charge impl _ (chargedRootOuterCharge_eq_zero_of_not_hash parameter),
    ← tsum_liveNativeHashQuerySelection_charge impl _ hstructural,
    ← tsum_liveNativeHashQuerySelection_charge impl _ hencoding]
  simp only [canonicalSelection_chargedRootCharge, mul_add, ← mul_assoc, ENNReal.tsum_add, ENNReal.tsum_mul_right]

end SphincsSecurity.Concrete.OtsProbeSimulation

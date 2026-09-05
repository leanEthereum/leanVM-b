import SphincsSecurity.Proof.OtsProbeChargedRootGlobalRisk

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

noncomputable def initializedChargedRootChargeAfterTable
    (targets : Finset Position) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) : ENNReal :=
  ∑' result, Pr[= result | runResolvedFromTable (ensuredInitialContext targets) fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)] *
    match result with
    | none => 0
    | some result => expectedLiveNativeContextCharge
        (maskedChronologicalExpandedAdversaryImpl parameter result.value.1 ftsSecret) (chargedRootOuterCharge parameter)
        (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩)
        result.context result.remaining table result.value.2

theorem sum_roots_initializedChargedRootCut_hits_le_charge
    (targets roots : Finset Position) (hsubset : roots ⊆ targets)
    (hroot : ∀ target ∈ roots, IsLayerRoot target)
    (hne : ∀ target ∈ roots, target ≠ layerRootPosition topLayer rootTree)
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel q : Nat) (hq : q ≤ 2 ^ 126) :
    (∑ target ∈ roots, ∑ ordinal ∈ Finset.range q,
      Pr[fun b => b = false | initializedChargedRootCutObservation targets adversary parameter target table ftsSecret fuel ordinal
        (fun pair => pair.2 = some (truncateHash pair.1))]) ≤
      initializedChargedRootChargeAfterTable targets adversary parameter table ftsSecret fuel * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  by_cases hempty : roots = ∅
  · simp [hempty]
  obtain ⟨selected, hselected⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  unfold initializedChargedRootCutObservation initializedChargedRootChargeAfterTable
  simp only [probEvent_bind_eq_tsum]
  simp_rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  rw [← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro result
  cases result with
  | none => simp
  | some result =>
      by_cases hresult : some result ∈ support (runResolvedFromTable (ensuredInitialContext targets) fuel table
          (maskedPublishedTreeRoot.run emptySplitHashCache))
      · have hfacts target htarget := initializedNativeRoot_fresh_facts parameter targets target (hsubset htarget)
          (hroot target htarget) (hne target htarget) fuel table result hresult
        obtain ⟨hvalid, hcomplete, _⟩ := hfacts selected hselected
        have hlocal := sum_targets_originalChargedRootCut_hits_le_charge roots parameter result.value.1 ftsSecret
          (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩) q hq result.context result.remaining table result.value.2
          hvalid hcomplete hroot
          (fun target htarget => (hfacts target htarget).2.2.1)
          (fun target htarget => (hfacts target htarget).2.2.2.1)
          (fun target htarget => (hfacts target htarget).2.2.2.2.1)
          (fun target htarget => (hfacts target htarget).2.2.2.2.2.1)
          (fun target htarget => (hfacts target htarget).2.2.2.2.2.2)
        simpa only [Finset.mul_sum, mul_assoc] using mul_le_mul'
          (le_refl (Pr[= some result | runResolvedFromTable (ensuredInitialContext targets) fuel table
            (maskedPublishedTreeRoot.run emptySplitHashCache)])) hlocal
      · simp [probOutput_eq_zero_of_not_mem_support hresult]

end SphincsSecurity.Concrete.OtsProbeSimulation

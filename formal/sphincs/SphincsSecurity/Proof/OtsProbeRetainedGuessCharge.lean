import SphincsSecurity.Proof.OtsProbeRiskAccumulation

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local irreducible] maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

theorem resolvedContextFailureRisk_of_no_pending
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hvalid : context.Valid) (hstarts : StartTableAgrees context.state table)
    (hcovered : PendingCoveredBy [] context) :
    resolvedContextFailureRisk table context = 0 := by
  have hcoordinates : PendingCovered [] context := by
    intro entry hentry
    obtain ⟨candidate, hcandidate, _⟩ := hcovered entry hentry
    simp at hcandidate
  have hcard := hcovered.card_le
  rw [resolvedContextFailureRisk_eq_finalize_coordinates table context [] hvalid hstarts hcoordinates
    (by simp) (by simpa using lt_of_le_of_lt hcard (Fintype.card_pos : 0 < Fintype.card Digest))]
  simp [finalizeResolvedCoordinates]

noncomputable def canonicalRetainedGuessCharge
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) : ℝ≥0∞ :=
  ∑' root, Pr[= root | runResolvedFromTable
    { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
    fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)] *
    match root with
    | none => 0
    | some root => expectedCanonicalQueryCharge parameter root.value.1 ftsSecret
        (canonicalGuessCharge parameter table)
        (retainedGameRestComputation adversary ⟨root.value.1, parameter⟩)
        root.context root.remaining root.table root.value.2

theorem probEvent_canonicalRetainedTrace_none_le_guessCharge
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[fun result => result.1 = none | canonicalRetainedQueryTrace adversary parameter table ftsSecret fuel] ≤
      canonicalRetainedGuessCharge adversary parameter table ftsSecret fuel := by
  unfold canonicalRetainedQueryTrace canonicalRetainedGuessCharge
  rw [probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro option
  by_cases hroot : option ∈ support (runResolvedFromTable
      { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
      fuel table (maskedPublishedTreeRoot.run emptySplitHashCache))
  · cases option with
    | none => exact False.elim (none_not_mem_resolved_maskedPublishedTreeRoot table fuel hroot)
    | some root =>
        dsimp only
        apply mul_le_mul_right
        have hcore := resolvedCore_of_mem_runResolvedFromTable
          (maskedPublishedTreeRoot.run emptySplitHashCache)
          { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
          fuel table root (by intro coordinate output hvalue; simp [LazyRevealProbe.State.empty] at hvalue)
          (by intro index output hvalue; simp [LazyRevealProbe.State.empty] at hvalue) hroot
        have hcomplete := deferredCompletable_of_mem_resolved_maskedPublishedTreeRoot parameter table fuel root hroot
        rw [hcore.1] at hcomplete
        have hcovered := pendingCoveredBy_of_mem_runResolvedFromTable [] _ _ fuel table root pendingCoveredBy_empty
          (OracleComp.IsQueryBoundP.of_imp (isUncoveredProbe_imp_isProbe [])
            (maskedPublishedTreeRoot_probeFree emptySplitHashCache)) hroot
        have hzero := resolvedContextFailureRisk_of_no_pending table root.context
          (valid_of_resolvedCore_completable table root.context hcore.2.1 hcore.2.2 hcomplete) hcore.2.2 hcovered
        have hprojection := probEvent_bind_pure_comp
          (runCanonicalQueryTrace parameter root.value.1 ftsSecret
            (retainedGameRestComputation adversary ⟨root.value.1, parameter⟩)
            root.context root.remaining root.table root.value.2)
          (fun rest => (rest.1.map (retainedResultWithRoot root.value.1), rest.2))
          (fun result => result.1 = none)
        have hbound := probEvent_canonicalTrace_none_le_initial_add_guessCharge parameter root.value.1 table ftsSecret
          (retainedGameRestComputation adversary ⟨root.value.1, parameter⟩)
          root.context root.remaining root.value.2 hcore.2.1 hcore.2.2
        rw [hzero, zero_add] at hbound
        rw [hcore.1]
        calc
          _ = Pr[fun result => result.1 = none | runCanonicalQueryTrace parameter root.value.1 ftsSecret
              (retainedGameRestComputation adversary ⟨root.value.1, parameter⟩)
              root.context root.remaining table root.value.2] := by
            simpa only [Function.comp_def, Option.map_eq_none_iff, hcore.1] using hprojection
          _ ≤ _ := hbound
  · rw [probOutput_eq_zero_of_not_mem_support hroot, zero_mul, zero_mul]

theorem probEvent_retainedVerifyProbe_le_guessCharge
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[WinningRetainedVerifyProbeWitness parameter (extendStartTable table) ftsSecret |
      actualRetainedGameAfterTable adversary parameter ftsSecret (extendStartTable table)] ≤
      canonicalRetainedGuessCharge adversary parameter table ftsSecret fuel := by
  apply (probEvent_retainedVerifyProbe_le_rejectionRisk adversary parameter table ftsSecret fuel).trans
  rw [← probEvent_canonicalRetainedTrace_none_eq_rejectionRisk]
  exact probEvent_canonicalRetainedTrace_none_le_guessCharge adversary parameter table ftsSecret fuel

end SphincsSecurity.Concrete.OtsProbeSimulation

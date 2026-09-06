import SphincsSecurity.Proof.OtsProbeNativeAfterRootAllowance

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] maskedPublishedTreeRoot instFintypePosition
set_option backward.isDefEq.respectTransparency false

theorem expectedOutcomeRisk_probeFree_eq_initial
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe 0)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hcard : context.state.pending.card < Fintype.card Digest) :
    (∑' result, Pr[= result | runResolvedFromTable context fuel table computation] * resolvedOutcomeFailureRisk result) =
      resolvedContextFailureRisk table context := by
  rw [← probEvent_finished_eq_expected_outcomeRisk]
  have heq := probEvent_congr' (fun _ _ => Iff.rfl)
    (evalDist_runResolvedFinishIsNone_probeFree_of_core computation context fuel table () hbound hconsistent hstarts hcard)
    (p := fun verdict => verdict = true)
  change Pr[fun verdict => verdict = true | runResolvedFinishIsNone context fuel table computation] = _
  rw [heq, finishResolvedRunIsNone_metadata_eq context table fuel 0 () ()]
  rfl

theorem expectedOutcomeRisk_initializedRoot_eq_zero
    (targets : Finset Position) (table : OtsSecretIndex → HashOutput) (fuel : Nat) :
    (∑' result, Pr[= result | runResolvedFromTable (ensuredInitialContext targets) fuel table
      (maskedPublishedTreeRoot.run emptySplitHashCache)] * resolvedOutcomeFailureRisk result) = 0 := by
  have hstarts := startTableAgrees_of_deferredCompletable (ensuredInitialContext_completable targets table)
  rw [expectedOutcomeRisk_probeFree_eq_initial _ (ensuredInitialContext targets) fuel table
    (maskedPublishedTreeRoot_probeFree emptySplitHashCache) (ensuredInitialContext_valid targets).valuesConsistent hstarts
    (by simp [ensuredInitialContext, LazyRevealProbe.State.empty])]
  exact resolvedContextFailureRisk_of_no_pending table (ensuredInitialContext targets) (ensuredInitialContext_valid targets) hstarts
    (by intro entry hentry; simp [ensuredInitialContext, LazyRevealProbe.State.empty] at hentry)

theorem expectedNativeTerminalRisk_afterRoot_le_guessCharge
    (targets : Finset Position) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    (∑' trace, Pr[= trace | nativeChainTraceAfterRoot targets parameter table ftsSecret fuel
      (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩)] * resolvedOutcomeFailureRisk trace.1) ≤
    (∑' trace, Pr[= trace | nativeChainTraceAfterRoot targets parameter table ftsSecret fuel
      (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩)] *
      canonicalTraceCharge (canonicalGuessCharge parameter table) trace.2) := by
  have hbound :
      (∑' trace, Pr[= trace | nativeChainTraceAfterRoot targets parameter table ftsSecret fuel
        (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩)] * resolvedOutcomeFailureRisk trace.1) ≤
      (∑' result, Pr[= result | runResolvedFromTable (ensuredInitialContext targets) fuel table
        (maskedPublishedTreeRoot.run emptySplitHashCache)] * resolvedOutcomeFailureRisk result) +
      (∑' trace, Pr[= trace | nativeChainTraceAfterRoot targets parameter table ftsSecret fuel
        (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩)] *
        canonicalTraceCharge (canonicalGuessCharge parameter table) trace.2) := by
    simp only [nativeChainTraceAfterRoot, tsum_probOutput_bind_mul]
    rw [← ENNReal.tsum_add]
    apply ENNReal.tsum_le_tsum
    intro root
    by_cases hroot : root ∈ support (runResolvedFromTable (ensuredInitialContext targets) fuel table
        (maskedPublishedTreeRoot.run emptySplitHashCache))
    · rw [← mul_add]
      apply mul_le_mul_right
      cases root with
      | none => simp [canonicalTraceCharge, resolvedOutcomeFailureRisk]
      | some root =>
          have hcore := resolvedCore_of_mem_runResolvedFromTable _ (ensuredInitialContext targets) fuel table root
            (ensuredInitialContext_valid targets).valuesConsistent
            (startTableAgrees_of_deferredCompletable (ensuredInitialContext_completable targets table)) hroot
          simp only [resolvedOutcomeFailureRisk, hcore.1, expectedNativeTraceCharge_eq]
          exact expectedNativeTerminalRisk_le_initial_add_guessCharge parameter root.value.1 table ftsSecret
            (retainedGameRestComputation adversary ⟨root.value.1, parameter⟩) root.context root.remaining root.value.2 hcore.2.1 hcore.2.2
    · simp [probOutput_eq_zero_of_not_mem_support hroot]
  simpa only [expectedOutcomeRisk_initializedRoot_eq_zero, zero_add] using hbound

theorem expectedNativeTerminalRisk_afterRoot_le_missing_add_erasure_of_querySpace
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqSpace : q + 1 < Fintype.card Digest)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    (∑' trace, Pr[= trace | nativeChainTraceAfterRoot Finset.univ parameter table ftsSecret (q + 1)
      (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩)] * resolvedOutcomeFailureRisk trace.1) ≤
      liveStartProbeAllowance (nativeChronologicalRetainedComputation adversary parameter ftsSecret) (ensuredInitialContext Finset.univ) (q + 1) table +
        (∑ target : Position, privateLiveMissingProbeAllowance target
          (nativeChronologicalRetainedComputation adversary parameter ftsSecret) (ensuredInitialContext Finset.univ) (q + 1) table) +
        (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  have hbound := (expectedNativeTerminalRisk_afterRoot_le_guessCharge Finset.univ adversary parameter table ftsSecret (q + 1)).trans
    (expected_nativeRetainedGuessCharge_le_missing_add_erasure_of_querySpace Finset.univ adversary q hq hqSpace parameter hparameter table ftsSecret hfts)
  rw [expected_nativeMissingTraceCharges_eq_liveAllowances] at hbound
  exact hbound

theorem expectedNativeTerminalRisk_afterRoot_le_missing_add_erasure
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 126)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    (∑' trace, Pr[= trace | nativeChainTraceAfterRoot Finset.univ parameter table ftsSecret (q + 1)
      (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩)] * resolvedOutcomeFailureRisk trace.1) ≤
      liveStartProbeAllowance (nativeChronologicalRetainedComputation adversary parameter ftsSecret) (ensuredInitialContext Finset.univ) (q + 1) table +
        (∑ target : Position, privateLiveMissingProbeAllowance target
          (nativeChronologicalRetainedComputation adversary parameter ftsSecret) (ensuredInitialContext Finset.univ) (q + 1) table) +
        (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  exact expectedNativeTerminalRisk_afterRoot_le_missing_add_erasure_of_querySpace adversary q hq
    (by
      have hspace : 2 ^ 126 + 1 < Fintype.card Digest := by norm_num [digestBits]
      omega) parameter hparameter table ftsSecret hfts

end SphincsSecurity.Concrete.OtsProbeSimulation

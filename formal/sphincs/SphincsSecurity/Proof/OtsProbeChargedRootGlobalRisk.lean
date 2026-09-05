import SphincsSecurity.Proof.OtsProbeChargedRootCounting

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem sum_targets_originalChargedRootCut_hits_le_charge
    (targets : Finset Position) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (q : Nat) (hq : q ≤ 2 ^ 126) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hroot : ∀ target ∈ targets, IsLayerRoot target)
    (hensured : ∀ target ∈ targets, .position target ∈ context.state.ensured)
    (hstate : ∀ target ∈ targets, context.state.values (.position target) = none)
    (hvalue : ∀ target ∈ targets, context.values target = none)
    (hpending : ∀ target ∈ targets, context.state.pendingAt (.position target) = ∅)
    (hcache : ∀ target ∈ targets, ∀ digest, NoEncodingRootGuessCached parameter target digest cache) :
    (∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
      Pr[fun b => b = false | originalChargedRootCutObservation parameter root target ftsSecret computation
        context fuel table cache ∅ ordinal (fun pair => pair.2 = some (truncateHash pair.1))]) ≤
      expectedLiveNativeContextCharge (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
        (chargedRootOuterCharge parameter) computation context fuel table cache * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  calc
    _ ≤ ∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
        Pr[fun selection => chargedNativeRootSelectionCandidate parameter target selection ≠ none |
          liveNativeHashQuerySelection (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
            computation ordinal context fuel table cache] * ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
      apply Finset.sum_le_sum
      intro target htarget
      apply Finset.sum_le_sum
      intro ordinal hordinal
      have hlocal := probEvent_originalChargedRootCutObservation_hit_le_trace_occurrence parameter root target
        (hroot target htarget) ftsSecret computation context fuel table cache ∅ hvalid hcomplete
        (hensured target htarget) (hstate target htarget) (hvalue target htarget)
        (by rw [hpending target htarget]) (fun digest _ => hcache target htarget digest) ordinal
        (by simpa using (Nat.le_of_lt (Finset.mem_range.mp hordinal)).trans hq)
      rw [probEvent_chargedNativeRootTraceCutCandidate_occurrence_eq_selection parameter root target ftsSecret
        computation ordinal context fuel table cache hvalid.valuesConsistent (startTableAgrees_of_deferredCompletable hcomplete)] at hlocal
      exact hlocal
    _ = ((∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
        Pr[fun selection => chargedNativeRootSelectionCandidate parameter target selection ≠ none |
          liveNativeHashQuerySelection (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
            computation ordinal context fuel table cache]) * (4 / 3 : ENNReal)) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
      simp only [Finset.sum_mul, mul_assoc]
    _ ≤ _ := mul_le_mul' (sum_targets_hashSelections_chargedRoot_probability_le_charge targets parameter
      (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) computation q context fuel table cache) le_rfl

theorem chronological_liveProbe_add_chargedRoots_le_refinedReserve
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (actualCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) actualCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context actualCache)
    (hpublished : PublishedValues context.state) (hcomputed : DeferredComputationsClosed context)
    (hmat : LayerRootsMaterialized context) :
    let secretKey : SecretKey := ⟨parameter, root,
      fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
    expectedLiveResolvedQueryCharge nativeProbeQueryCharge
        ((simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) computation).run cache) context fuel table * (4 / 3 : ENNReal) +
      expectedLiveNativeContextCharge (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
        (chargedRootOuterCharge parameter) computation context fuel table cache ≤
      expectedQueryCharge (otsOpeningRefinedQueryReserve secretKey)
        (simulateQ (expandedAdversaryImpl secretKey) computation) actualCache := by
  dsimp only
  rw [expectedLiveChargedRootCharge_eq_components, ← add_assoc, ← add_mul]
  exact chronological_liveProbe_add_materializedRoots_le_refinedReserve parameter root table ftsSecret computation
    context fuel cache actualCache hinvariant hvisible hpublished hcomputed hmat

end SphincsSecurity.Concrete.OtsProbeSimulation

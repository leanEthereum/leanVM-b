import SphincsSecurity.Proof.OtsProbeLiveJointCharge

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def directOtsQueryCharge (parameter : PublicParameter) (_cache : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  otsHashInputCharge parameter input * (4 / 3)

noncomputable def remainingOtsQueryReserve (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  otsOpeningRefinedQueryReserve secretKey cache input - directOtsQueryCharge secretKey.parameter cache input

theorem directOtsQueryCharge_le_refinedReserve (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) :
    directOtsQueryCharge secretKey.parameter cache input ≤ otsOpeningRefinedQueryReserve secretKey cache input := by
  exact weightedOtsOuterQueryCharge_le_refinedReserve secretKey (.inl (.inr input)) cache

theorem direct_add_remaining_otsQueryReserve (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) :
    directOtsQueryCharge secretKey.parameter cache input + remainingOtsQueryReserve secretKey cache input =
      otsOpeningRefinedQueryReserve secretKey cache input := by
  unfold remainingOtsQueryReserve
  exact add_tsub_cancel_of_le (directOtsQueryCharge_le_refinedReserve secretKey cache input)

theorem remainingOtsQueryReserve_eq_refined_of_not_ots
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput)
    (hnot : ¬∃ position : Position, IsOtsPosition position ∧ AtPosition secretKey.parameter input position) :
    remainingOtsQueryReserve secretKey cache input = otsOpeningRefinedQueryReserve secretKey cache input := by
  simp [remainingOtsQueryReserve, directOtsQueryCharge, otsHashInputCharge, hnot]

theorem expected_direct_add_remaining_otsQueryReserve
    (secretKey : SecretKey) (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    expectedQueryCharge (directOtsQueryCharge secretKey.parameter) computation cache +
      expectedQueryCharge (remainingOtsQueryReserve secretKey) computation cache =
      expectedQueryCharge (otsOpeningRefinedQueryReserve secretKey) computation cache := by
  rw [← expectedQueryCharge_add]
  simp only [direct_add_remaining_otsQueryReserve]

theorem sampled_direct_add_remaining_otsQueryReserve (adversary : Adversary) :
    sampledQueryCharge (fun secretKey => directOtsQueryCharge secretKey.parameter) adversary +
      sampledQueryCharge remainingOtsQueryReserve adversary = sampledQueryCharge otsOpeningRefinedQueryReserve adversary := by
  rw [← sampledQueryCharge_add]
  simp only [direct_add_remaining_otsQueryReserve]

theorem otsOuterQueryCharge_hash (parameter : PublicParameter) (input : HashInput) :
    otsOuterQueryCharge parameter (.inl (.inr input)) = otsHashInputCharge parameter input := rfl

theorem outerHashQueryCharge_hash (charge : QueryCache HashSpec → HashInput → ENNReal)
    (input : HashInput) (cache : QueryCache HashSpec) :
    outerHashQueryCharge charge (.inl (.inr input)) cache = charge cache input := rfl

theorem directOtsQueryCharge_eq (parameter : PublicParameter) (cache : QueryCache HashSpec) (input : HashInput) :
    directOtsQueryCharge parameter cache input = otsHashInputCharge parameter input * (4 / 3 : ENNReal) := rfl

theorem weightedOtsOuterQueryCharge_le_directCharge (parameter : PublicParameter)
    (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec) :
    otsOuterQueryCharge parameter input * (4 / 3 : ENNReal) ≤
      outerHashQueryCharge (directOtsQueryCharge parameter) input cache := by
  cases input with
  | inl query =>
      cases query with
      | inl n => exact (zero_mul (4 / 3 : ENNReal)).le
      | inr input => rw [otsOuterQueryCharge_hash, outerHashQueryCharge_hash, directOtsQueryCharge_eq]
  | inr message => exact (zero_mul (4 / 3 : ENNReal)).le

theorem expectedLiveChronologicalOtsCharge_le_directCharge
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (actualCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) actualCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context actualCache)
    (hpublished : PublishedValues context.state) :
    expectedLiveNativeOuterCharge (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
      (fun input => otsOuterQueryCharge parameter input * (4 / 3 : ENNReal)) computation context fuel table cache ≤
      expectedQueryCharge (directOtsQueryCharge parameter)
        (simulateQ (expandedAdversaryImpl
          (⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩ : SecretKey)) computation) actualCache := by
  let secretKey : SecretKey := ⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
  have hbound : expectedLiveNativeOuterCharge (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
      (fun input => otsOuterQueryCharge parameter input * (4 / 3 : ENNReal)) computation context fuel table cache ≤
      expectedOuterQueryCharge secretKey (directOtsQueryCharge parameter) computation actualCache := by
    exact expectedLiveNativeOuterCharge_le_actualOuterCharge parameter root table ftsSecret
      (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
      (fun input => otsOuterQueryCharge parameter input * (4 / 3 : ENNReal))
      (directOtsQueryCharge parameter)
      (reachableResolvedCouples_chronologicalNative_concrete parameter root table ftsSecret)
      (weightedOtsOuterQueryCharge_le_directCharge parameter)
      computation context fuel cache actualCache hinvariant hvisible hpublished
  exact hbound.trans (expectedOuterQueryCharge_le_expanded secretKey (directOtsQueryCharge parameter) computation actualCache)

theorem expectedLiveChronologicalOtsCount_mul_le_directCharge
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (actualCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) actualCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context actualCache)
    (hpublished : PublishedValues context.state) :
    expectedLiveNativeOuterCharge (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
      (otsOuterQueryCharge parameter) computation context fuel table cache * (4 / 3 : ENNReal) ≤
      expectedQueryCharge (directOtsQueryCharge parameter)
        (simulateQ (expandedAdversaryImpl
          (⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩ : SecretKey)) computation) actualCache := by
  rw [← expectedLiveNativeOuterCharge_mul]
  exact expectedLiveChronologicalOtsCharge_le_directCharge parameter root table ftsSecret computation context fuel cache actualCache
    hinvariant hvisible hpublished

theorem liveChainStartCharge_add_structuralHits_le_directCharge
    (targets : Finset Position) (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (q : Nat) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (cache : SplitHashCache) (actualCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) actualCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context actualCache)
    (hpublished : PublishedValues context.state)
    (hensured : ∀ target ∈ targets, .position target ∈ context.state.ensured)
    (hstate : ∀ target ∈ targets, context.state.values (.position target) = none)
    (hvalue : ∀ target ∈ targets, context.values target = none)
    (hhidden : ∀ target ∈ targets, .position target ∉ context.state.revealed)
    (hcard : ∀ target ∈ targets, (context.state.pendingAt (.position target)).card + q ≤ 2 ^ 126) :
    expectedLiveResolvedQueryCharge chainStartProbeQueryCharge
        ((simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) computation).run cache) context fuel table *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) +
      (∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
        Pr[PrivateCandidatePairHit | privateResolvedSelectedCandidate target (privateRawCutCandidate target) <$>
          runPrivateResolvedView target table context fuel (privatePositionProbeCutAt target
            ((simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) computation).run cache) ordinal)]) ≤
      expectedQueryCharge (directOtsQueryCharge parameter)
        (simulateQ (expandedAdversaryImpl
          (⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩ : SecretKey)) computation)
        actualCache * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  let native := ((simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) computation).run cache)
  let count := expectedLiveNativeOuterCharge (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
    (otsOuterQueryCharge parameter) computation context fuel table cache
  calc
    _ ≤ expectedLiveResolvedQueryCharge chainStartProbeQueryCharge native context fuel table *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) +
        expectedLiveResolvedQueryCharge structuralProbeQueryCharge native context fuel table *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) :=
      add_le_add le_rfl (sum_targets_privateResolvedRawCandidate_hit_le_expectedLiveStructuralCharge targets native q context fuel table
        hinvariant.2.1 hinvariant.2.2.2.1 hensured hstate hvalue hhidden hcard)
    _ = (expectedLiveResolvedQueryCharge chainStartProbeQueryCharge native context fuel table +
        expectedLiveResolvedQueryCharge structuralProbeQueryCharge native context fuel table) *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := (add_mul _ _ _).symm
    _ ≤ count * ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) :=
      mul_le_mul' (chronological_liveChainStart_add_structural_le_liveOuterCharge parameter root ftsSecret computation context fuel table cache
        hinvariant.2.1.valuesConsistent hinvariant.2.2.1) le_rfl
    _ = (count * (4 / 3 : ENNReal)) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := (mul_assoc _ _ _).symm
    _ ≤ _ := mul_le_mul' (expectedLiveChronologicalOtsCount_mul_le_directCharge parameter root table ftsSecret computation
      context fuel cache actualCache hinvariant hvisible hpublished) le_rfl

end SphincsSecurity.Concrete.OtsProbeSimulation

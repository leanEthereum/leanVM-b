import SphincsSecurity.Proof.OtsProbePrivateValueLiveProbeCounting

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem expectedLiveResolvedQueryCharge_le_raw
    (charge : LazyRevealProbe.Query Coordinate → ENNReal) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    expectedLiveResolvedQueryCharge charge computation context fuel table ≤ expectedResolvedQueryCharge charge computation context fuel table := by
  induction computation using OracleComp.inductionOn generalizing context fuel table with
  | pure value => rfl
  | query_bind input next ih =>
      rw [expectedLiveResolvedQueryCharge_query_bind, expectedResolvedQueryCharge_query_bind]
      by_cases hcomplete : DeferredCompletable table context
      · rw [if_pos hcomplete]
        apply add_le_add le_rfl
        apply ENNReal.tsum_le_tsum
        intro result
        cases result with
        | none => rfl
        | some result => exact mul_le_mul' le_rfl (ih result.value result.context result.remaining result.table)
      · simp [hcomplete]

noncomputable def liveResolvedContinuationCharge
    (charge : LazyRevealProbe.Query Coordinate → ENNReal)
    (next : α → OracleComp (LazyRevealProbe.World Coordinate) β) : Option (ResolvedRunResult α) → ENNReal
  | none => 0
  | some result => expectedLiveResolvedQueryCharge charge (next result.value) result.context result.remaining result.table

theorem expectedLiveResolvedQueryCharge_bind
    (charge : LazyRevealProbe.Query Coordinate → ENNReal)
    (left : OracleComp (LazyRevealProbe.World Coordinate) α) (next : α → OracleComp (LazyRevealProbe.World Coordinate) β)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    expectedLiveResolvedQueryCharge charge (left >>= next) context fuel table =
      expectedLiveResolvedQueryCharge charge left context fuel table +
        ∑' result, Pr[= result | runResolvedFromTable context fuel table left] * liveResolvedContinuationCharge charge next result := by
  induction left using OracleComp.inductionOn generalizing context fuel table with
  | pure value => simp [expectedLiveResolvedQueryCharge, runResolvedFromTable, liveResolvedContinuationCharge]
  | query_bind input continuation ih =>
      by_cases hcomplete : DeferredCompletable table context
      · rw [bind_assoc, expectedLiveResolvedQueryCharge_query_bind, expectedLiveResolvedQueryCharge_query_bind,
          if_pos hcomplete, if_pos hcomplete, runResolvedFromTable_bind, tsum_probOutput_bind_mul, add_assoc, ← ENNReal.tsum_add]
        congr 1
        apply tsum_congr
        intro result
        by_cases hresult : result ∈ support (runResolvedFromTable context fuel table (liftM (OracleSpec.query input)))
        · cases result with
          | none => simp [liveResolvedContinuationCharge]
          | some result =>
              have hcore := resolvedCore_of_mem_runResolvedFromTable (liftM (OracleSpec.query input)) context fuel table result hconsistent hstarts hresult
              dsimp only
              rw [ih result.value result.context result.remaining result.table hcore.2.1 (hcore.1 ▸ hcore.2.2), mul_add, ← ENNReal.tsum_mul_left]
        · simp [probOutput_eq_zero_of_not_mem_support hresult]
      · rw [expectedLiveResolvedQueryCharge_eq_zero_of_not_completable charge _ context fuel table hcomplete,
          expectedLiveResolvedQueryCharge_eq_zero_of_not_completable charge _ context fuel table hcomplete, zero_add]
        symm
        apply ENNReal.tsum_eq_zero.mpr
        intro result
        by_cases hresult : result ∈ support (runResolvedFromTable context fuel table
            ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= continuation))
        · cases result with
          | none => simp [liveResolvedContinuationCharge]
          | some result =>
              have hcore := resolvedCore_of_mem_runResolvedFromTable _ context fuel table result hconsistent hstarts hresult
              have hdoomed := not_deferredCompletable_of_mem_runResolvedFromTable _ context fuel table result hconsistent hstarts hresult hcomplete
              simp only [liveResolvedContinuationCharge, hcore.1,
                expectedLiveResolvedQueryCharge_eq_zero_of_not_completable charge _ _ _ _ hdoomed, mul_zero]
        · simp [probOutput_eq_zero_of_not_mem_support hresult]

theorem chronological_expectedLiveStructuralCharge_le_liveOuterCharge
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    expectedLiveResolvedQueryCharge structuralProbeQueryCharge
      ((simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) computation).run cache) context fuel table ≤
      expectedLiveNativeOuterCharge (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
        (otsOuterQueryCharge parameter) computation context fuel table cache := by
  induction computation using OracleComp.inductionOn generalizing context fuel table cache with
  | pure value => simp [expectedLiveResolvedQueryCharge, expectedLiveNativeOuterCharge]
  | query_bind input next ih =>
      by_cases hcomplete : DeferredCompletable table context
      · rw [simulateQ_query_bind, StateT.run_bind,
          expectedLiveResolvedQueryCharge_bind _ _ _ context fuel table hconsistent hstarts,
          expectedLiveNativeOuterCharge_query_bind, if_pos hcomplete]
        apply add_le_add ((expectedLiveResolvedQueryCharge_le_raw structuralProbeQueryCharge _ context fuel table).trans
          (chronologicalAdversaryImpl_expectedResolvedStructuralCharge_le parameter root ftsSecret input cache context fuel table))
        apply ENNReal.tsum_le_tsum
        intro result
        by_cases hresult : result ∈ support (runResolvedFromTable context fuel table
            ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache))
        · cases result with
          | none => rfl
          | some result =>
              have hcore := resolvedCore_of_mem_runResolvedFromTable _ context fuel table result hconsistent hstarts hresult
              exact mul_le_mul' le_rfl (ih result.value.1 result.context result.remaining result.table result.value.2 hcore.2.1 (hcore.1 ▸ hcore.2.2))
        · simp [probOutput_eq_zero_of_not_mem_support hresult]
      · rw [expectedLiveResolvedQueryCharge_eq_zero_of_not_completable _ _ context fuel table hcomplete,
          expectedLiveNativeOuterCharge_eq_zero_of_not_completable _ _ _ context fuel table cache hcomplete]


theorem sum_targets_privateResolvedRawCandidate_hit_le_actualReserve
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
    (∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
      Pr[PrivateCandidatePairHit | privateResolvedSelectedCandidate target (privateRawCutCandidate target) <$>
        runPrivateResolvedView target table context fuel (privatePositionProbeCutAt target
          ((simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) computation).run cache) ordinal)]) ≤
      expectedQueryCharge
        (otsOpeningRefinedQueryReserve
          (⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩ : SecretKey))
        (simulateQ (expandedAdversaryImpl
          (⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩ : SecretKey)) computation)
        actualCache * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  let native := ((simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) computation).run cache)
  let count := expectedLiveNativeOuterCharge (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
    (otsOuterQueryCharge parameter) computation context fuel table cache
  calc
    _ ≤ expectedLiveResolvedQueryCharge structuralProbeQueryCharge native context fuel table *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) :=
      sum_targets_privateResolvedRawCandidate_hit_le_expectedLiveStructuralCharge targets native q context fuel table
        hinvariant.2.1 hinvariant.2.2.2.1 hensured hstate hvalue hhidden hcard
    _ ≤ count * ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) :=
      mul_le_mul' (chronological_expectedLiveStructuralCharge_le_liveOuterCharge parameter root ftsSecret computation
        context fuel table cache hinvariant.2.1.valuesConsistent hinvariant.2.2.1) le_rfl
    _ = (count * (4 / 3 : ENNReal)) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := (mul_assoc _ _ _).symm
    _ ≤ _ := mul_le_mul' (expectedLiveChronologicalOtsCount_mul_le_actualReserve parameter root table ftsSecret computation
      context fuel cache actualCache hinvariant hvisible hpublished) le_rfl

end SphincsSecurity.Concrete.OtsProbeSimulation

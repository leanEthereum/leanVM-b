import SphincsSecurity.Proof.OtsProbeNativePlannedReserve

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem simulateQ_expectedLiveQueryCharge_add_contextCharge_le_outer
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (charge : LazyRevealProbe.Query Coordinate → ENNReal)
    (extra : (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ENNReal)
    (outer : (OracleWorld + SigningSpec).Domain → ENNReal)
    (hstep : ∀ input cache context fuel table,
      expectedLiveResolvedQueryCharge charge ((impl input).run cache) context fuel table +
        extra input context fuel cache ≤ outer input)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    expectedLiveResolvedQueryCharge charge ((simulateQ impl computation).run cache) context fuel table +
      expectedLiveNativeContextCharge impl extra computation context fuel table cache ≤
      expectedLiveNativeOuterCharge impl outer computation context fuel table cache := by
  induction computation using OracleComp.inductionOn generalizing context fuel table cache with
  | pure value => simp [expectedLiveResolvedQueryCharge, expectedLiveNativeContextCharge, expectedLiveNativeOuterCharge]
  | query_bind input next ih =>
      by_cases hcomplete : DeferredCompletable table context
      · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
        rw [expectedLiveResolvedQueryCharge_bind _ _ _ context fuel table hconsistent hstarts,
          expectedLiveNativeContextCharge_query_bind, expectedLiveNativeOuterCharge_query_bind,
          if_pos hcomplete, if_pos hcomplete, add_add_add_comm, ← ENNReal.tsum_add]
        apply add_le_add (hstep input cache context fuel table)
        apply ENNReal.tsum_le_tsum
        intro result
        rw [← mul_add]
        by_cases hresult : result ∈ support (runResolvedFromTable context fuel table ((impl input).run cache))
        · cases result with
          | none => simp [liveResolvedContinuationCharge]
          | some result =>
              have hcore := resolvedCore_of_mem_runResolvedFromTable _ context fuel table result hconsistent hstarts hresult
              exact mul_le_mul' le_rfl (ih result.value.1 result.context result.remaining result.table result.value.2
                hcore.2.1 (hcore.1 ▸ hcore.2.2))
        · simp [probOutput_eq_zero_of_not_mem_support hresult]
      · rw [expectedLiveResolvedQueryCharge_eq_zero_of_not_completable _ _ context fuel table hcomplete,
          expectedLiveNativeContextCharge_eq_zero_of_not_completable _ _ _ context fuel table cache hcomplete,
          expectedLiveNativeOuterCharge_eq_zero_of_not_completable _ _ _ context fuel table cache hcomplete]
        simp

theorem chronological_liveProbe_add_unused_le_liveOuterCharge
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    expectedLiveResolvedQueryCharge nativeProbeQueryCharge
        ((simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) computation).run cache) context fuel table +
      expectedLiveNativeContextCharge (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
        (nativeUnusedProbeOuterCharge parameter) computation context fuel table cache ≤
      expectedLiveNativeOuterCharge (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
        (otsOuterQueryCharge parameter) computation context fuel table cache :=
  simulateQ_expectedLiveQueryCharge_add_contextCharge_le_outer _ _ _ _
    (chronologicalAdversaryImpl_probeCharge_add_unused_le_ots parameter root ftsSecret)
    computation context fuel table cache hconsistent hstarts

theorem chronological_liveProbe_add_unused_mul_le_directCharge
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (actualCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) actualCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context actualCache)
    (hpublished : PublishedValues context.state) :
    (expectedLiveResolvedQueryCharge nativeProbeQueryCharge
        ((simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) computation).run cache) context fuel table +
      expectedLiveNativeContextCharge (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
        (nativeUnusedProbeOuterCharge parameter) computation context fuel table cache) * (4 / 3 : ENNReal) ≤
      expectedQueryCharge (directOtsQueryCharge parameter)
        (simulateQ (expandedAdversaryImpl
          (⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩ : SecretKey))
          computation) actualCache := by
  exact (mul_le_mul'
    (chronological_liveProbe_add_unused_le_liveOuterCharge parameter root ftsSecret computation context fuel table cache
      hinvariant.2.1.valuesConsistent hinvariant.2.2.1) le_rfl).trans
    (expectedLiveChronologicalOtsCount_mul_le_directCharge parameter root table ftsSecret computation context fuel cache actualCache
      hinvariant hvisible hpublished)

end SphincsSecurity.Concrete.OtsProbeSimulation

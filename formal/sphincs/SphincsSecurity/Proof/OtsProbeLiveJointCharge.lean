import SphincsSecurity.Proof.OtsProbeLiveNativeComposition

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def nativeProbeQueryCharge (input : LazyRevealProbe.Query Coordinate) : ENNReal :=
  if LazyRevealProbe.IsProbe input then 1 else 0

noncomputable def chainStartProbeQueryCharge : LazyRevealProbe.Query Coordinate → ENNReal
  | .probe (.chainStart _ _ _ _) _ => 1
  | _ => 0

theorem chainStart_add_structural_probeQueryCharge (input : LazyRevealProbe.Query Coordinate) :
    chainStartProbeQueryCharge input + structuralProbeQueryCharge input = nativeProbeQueryCharge input := by
  cases input with
  | probe coordinate digest =>
      cases coordinate <;> simp [chainStartProbeQueryCharge, structuralProbeQueryCharge, nativeProbeQueryCharge, LazyRevealProbe.IsProbe]
  | _ => simp [chainStartProbeQueryCharge, structuralProbeQueryCharge, nativeProbeQueryCharge, LazyRevealProbe.IsProbe]

theorem expectedLiveResolvedQueryCharge_add
    (left right : LazyRevealProbe.Query Coordinate → ENNReal) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    expectedLiveResolvedQueryCharge (fun input => left input + right input) computation context fuel table =
      expectedLiveResolvedQueryCharge left computation context fuel table + expectedLiveResolvedQueryCharge right computation context fuel table := by
  have hsum := expectedLiveResolvedQueryCharge_finset_sum (Finset.univ : Finset Bool)
    (fun index => if index then left else right) computation context fuel table
  simpa [Fintype.sum_bool, add_comm] using hsum

theorem expectedLiveChainStart_add_structural_eq_probeCharge
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    expectedLiveResolvedQueryCharge chainStartProbeQueryCharge computation context fuel table +
      expectedLiveResolvedQueryCharge structuralProbeQueryCharge computation context fuel table =
      expectedLiveResolvedQueryCharge nativeProbeQueryCharge computation context fuel table := by
  rw [← expectedLiveResolvedQueryCharge_add]
  simp only [chainStart_add_structural_probeQueryCharge]

theorem expectedResolvedProbeCharge_le_probeBound
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (bound : Nat)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe bound) :
    expectedResolvedQueryCharge nativeProbeQueryCharge computation context fuel table ≤ bound :=
  expectedResolvedQueryCharge_le_queryBound nativeProbeQueryCharge LazyRevealProbe.IsProbe (fun _ => le_rfl)
    computation bound context fuel table hbound

theorem chronologicalAdversaryImpl_expectedResolvedProbeCharge_le
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (cache : SplitHashCache)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    expectedResolvedQueryCharge nativeProbeQueryCharge ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache)
      context fuel table ≤ otsOuterQueryCharge parameter input := by
  cases input with
  | inl query =>
      cases query with
      | inl n =>
          change expectedResolvedQueryCharge nativeProbeQueryCharge ((splitUniformImpl n).run cache) context fuel table ≤ 0
          simpa only [Nat.cast_zero] using expectedResolvedProbeCharge_le_probeBound _ 0 context fuel table (splitUniformImpl_probeFree n cache)
      | inr input =>
          change expectedResolvedQueryCharge nativeProbeQueryCharge ((probingHashQuery parameter input).run cache) context fuel table ≤ otsHashInputCharge parameter input
          unfold otsHashInputCharge
          split_ifs with hots
          · simpa only [Nat.cast_one] using expectedResolvedProbeCharge_le_probeBound _ 1 context fuel table (probingHashQuery_run_isProbeBound parameter input cache)
          · rw [probingHashQuery_eq_split_of_not_atOtsPosition parameter input hots]
            simpa only [Nat.cast_zero] using expectedResolvedProbeCharge_le_probeBound _ 0 context fuel table (splitHashQuery_probeFree _ cache)
  | inr message =>
      change expectedResolvedQueryCharge nativeProbeQueryCharge ((maskedPublishedChronologicalSign parameter root ftsSecret message).run cache) context fuel table ≤ 0
      simpa only [Nat.cast_zero] using expectedResolvedProbeCharge_le_probeBound _ 0 context fuel table
        (maskedPublishedChronologicalSign_probeFree parameter root ftsSecret message cache)

theorem simulateQ_expectedLiveQueryCharge_le_liveOuterCharge
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (charge : LazyRevealProbe.Query Coordinate → ENNReal) (outerCharge : (OracleWorld + SigningSpec).Domain → ENNReal)
    (hstep : ∀ input cache context fuel table,
      expectedLiveResolvedQueryCharge charge ((impl input).run cache) context fuel table ≤ outerCharge input)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    expectedLiveResolvedQueryCharge charge ((simulateQ impl computation).run cache) context fuel table ≤
      expectedLiveNativeOuterCharge impl outerCharge computation context fuel table cache := by
  induction computation using OracleComp.inductionOn generalizing context fuel table cache with
  | pure value => simp [expectedLiveResolvedQueryCharge, expectedLiveNativeOuterCharge]
  | query_bind input next ih =>
      by_cases hcomplete : DeferredCompletable table context
      · rw [simulateQ_query_bind, StateT.run_bind,
          expectedLiveResolvedQueryCharge_bind _ _ _ context fuel table hconsistent hstarts,
          expectedLiveNativeOuterCharge_query_bind, if_pos hcomplete]
        apply add_le_add (hstep input cache context fuel table)
        apply ENNReal.tsum_le_tsum
        intro result
        by_cases hresult : result ∈ support (runResolvedFromTable context fuel table ((impl input).run cache))
        · cases result with
          | none => rfl
          | some result =>
              have hcore := resolvedCore_of_mem_runResolvedFromTable _ context fuel table result hconsistent hstarts hresult
              exact mul_le_mul' le_rfl (ih result.value.1 result.context result.remaining result.table result.value.2 hcore.2.1 (hcore.1 ▸ hcore.2.2))
        · simp [probOutput_eq_zero_of_not_mem_support hresult]
      · rw [expectedLiveResolvedQueryCharge_eq_zero_of_not_completable _ _ context fuel table hcomplete,
          expectedLiveNativeOuterCharge_eq_zero_of_not_completable _ _ _ context fuel table cache hcomplete]

theorem chronological_liveChainStart_add_structural_le_liveOuterCharge
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    expectedLiveResolvedQueryCharge chainStartProbeQueryCharge
        ((simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) computation).run cache) context fuel table +
      expectedLiveResolvedQueryCharge structuralProbeQueryCharge
        ((simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) computation).run cache) context fuel table ≤
      expectedLiveNativeOuterCharge (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
        (otsOuterQueryCharge parameter) computation context fuel table cache := by
  rw [expectedLiveChainStart_add_structural_eq_probeCharge]
  apply simulateQ_expectedLiveQueryCharge_le_liveOuterCharge _ _ _ _ computation context fuel table cache hconsistent hstarts
  intro input nextCache nextContext remaining nextTable
  exact (expectedLiveResolvedQueryCharge_le_raw nativeProbeQueryCharge _ nextContext remaining nextTable).trans
    (chronologicalAdversaryImpl_expectedResolvedProbeCharge_le parameter root ftsSecret input nextCache nextContext remaining nextTable)

end SphincsSecurity.Concrete.OtsProbeSimulation

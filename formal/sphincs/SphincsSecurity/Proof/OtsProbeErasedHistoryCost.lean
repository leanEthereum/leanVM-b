import SphincsSecurity.Proof.OtsProbeHistoryCutCounting

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def runErasedHistoryCharged (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) : ProbComp (Option (HistoryResolvedPrefix α) × Nat) :=
  OracleComp.construct
    (C := fun _ => DeferredContext → ProbComp (Option (HistoryResolvedPrefix α) × Nat))
    (fun value context => pure (some ⟨context, 0, value, []⟩, 0))
    (fun input _ next context => do
      let entry ← runResolvedHistoryPrefix (eraseProbeQueries (liftM (OracleSpec.query input))) context 0 []
      let charge : Nat := if LazyRevealProbe.IsProbe input then 1 else 0
      match entry with
      | none => pure (none, charge)
      | some entry => (fun result => (result.1, result.2 + charge)) <$> next entry.value entry.context)
    computation context

theorem runErasedHistoryCharged_query_bind
    (input : LazyRevealProbe.Query Coordinate)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) :
    runErasedHistoryCharged ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next) context =
      runResolvedHistoryPrefix (eraseProbeQueries (liftM (OracleSpec.query input))) context 0 [] >>= fun entry =>
        match entry with
        | none => pure (none, if LazyRevealProbe.IsProbe input then 1 else 0)
        | some entry => (fun result : Option (HistoryResolvedPrefix α) × Nat => (result.1, result.2 + if LazyRevealProbe.IsProbe input then 1 else 0)) <$>
            runErasedHistoryCharged (next entry.value) entry.context := by
  rw [runErasedHistoryCharged, construct_query_bind]
  rfl

theorem runErasedHistoryCharged_result
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (context : DeferredContext) :
    evalDist (Prod.fst <$> runErasedHistoryCharged computation context) =
      evalDist (runResolvedHistoryPrefix (eraseProbeQueries computation) context 0 []) := by
  induction computation using OracleComp.inductionOn generalizing context with
  | pure value => simp [runErasedHistoryCharged, eraseProbeQueries, runResolvedHistoryPrefix]
  | query_bind input next ih =>
      rw [runErasedHistoryCharged_query_bind, map_bind, eraseProbeQueries_query_bind, runResolvedHistoryPrefix_bind]
      apply evalDist_bind_congr
      intro entry hentry
      cases entry with
      | none => rfl
      | some entry =>
          rw [Functor.map_map]
          change evalDist (Prod.fst <$> runErasedHistoryCharged (next entry.value) entry.context) = _
          obtain ⟨hfuel, hhistory⟩ := erasedHistoryQueryStep_fields input context entry hentry
          dsimp only
          rw [hfuel, hhistory]
          exact ih entry.value entry.context

noncomputable def expectedErasedHistoryProbeCost
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (context : DeferredContext) : ENNReal :=
  ∑' result, Pr[= result | runErasedHistoryCharged computation context] * (result.2 : ENNReal)

theorem expectedErasedHistoryProbeCost_query_bind
    (input : LazyRevealProbe.Query Coordinate)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) :
    expectedErasedHistoryProbeCost ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next) context =
      nativeProbeQueryCharge input +
        ∑' entry, Pr[= entry | runResolvedHistoryPrefix (eraseProbeQueries (liftM (OracleSpec.query input))) context 0 []] *
          match entry with
          | none => 0
          | some entry => expectedErasedHistoryProbeCost (next entry.value) entry.context := by
  unfold expectedErasedHistoryProbeCost
  rw [runErasedHistoryCharged_query_bind, tsum_probOutput_bind_mul]
  have hcast : ((if LazyRevealProbe.IsProbe input then 1 else 0 : Nat) : ENNReal) = nativeProbeQueryCharge input := by
    by_cases hprobe : LazyRevealProbe.IsProbe input <;> simp [nativeProbeQueryCharge, hprobe]
  have heq (entry : Option (HistoryResolvedPrefix ((LazyRevealProbe.World Coordinate).Range input))) :
      (∑' result, Pr[= result | (match entry with
        | none => pure (none, if LazyRevealProbe.IsProbe input then 1 else 0)
        | some entry => (fun result : Option (HistoryResolvedPrefix α) × Nat => (result.1, result.2 + if LazyRevealProbe.IsProbe input then 1 else 0)) <$>
            runErasedHistoryCharged (next entry.value) entry.context)] * (result.2 : ENNReal)) =
        nativeProbeQueryCharge input + match entry with
          | none => 0
          | some entry => ∑' result, Pr[= result | runErasedHistoryCharged (next entry.value) entry.context] * (result.2 : ENNReal) := by
    cases entry with
    | none => simp only [tsum_probOutput_pure_mul, hcast, add_zero]
    | some entry =>
        rw [tsum_probOutput_map_mul]
        simp only [Nat.cast_add, mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul, hcast, add_comm]
  calc
    _ = ∑' entry, Pr[= entry | runResolvedHistoryPrefix (eraseProbeQueries (liftM (OracleSpec.query input))) context 0 []] *
        (nativeProbeQueryCharge input + match entry with
          | none => 0
          | some entry => ∑' result, Pr[= result | runErasedHistoryCharged (next entry.value) entry.context] * (result.2 : ENNReal)) := by
      apply tsum_congr
      intro entry
      apply congrArg (fun cost => _ * cost)
      cases entry with
      | none => exact heq none
      | some entry => exact heq (some entry)
    _ = _ := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]

theorem sharedHistoryCutCharge_le_expectedProbeCost
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (ordinals : Nat) :
    sharedHistoryCutCharge targets computation context ordinals ≤ expectedErasedHistoryProbeCost computation context := by
  induction computation using OracleComp.inductionOn generalizing context with
  | pure value =>
      simp [sharedHistoryCutCharge, erasedHistoryStartCutCharge, erasedHistoryPrivateCutCharge,
        nativeProbeCutAt, privatePositionProbeCutAt, eraseProbeQueries, runResolvedHistoryPrefix,
        HistoryChainStartCutReached, HistoryPrivateProbeCutReached, IsChainStartCut, privatePositionAccessCandidate]
  | query_bind input next ih =>
      rw [expectedErasedHistoryProbeCost_query_bind]
      apply (sharedHistoryCutCharge_query_bind_le targets input next context ordinals).trans
      apply add_le_add le_rfl
      apply ENNReal.tsum_le_tsum
      intro entry
      apply mul_le_mul' le_rfl
      cases entry with
      | none => rfl
      | some entry => exact ih entry.value entry.context

end SphincsSecurity.Concrete.OtsProbeSimulation

import SphincsSecurity.Proof.OtsProbeHistoryCutCap

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem erasedHistoryQueryStep_fields
    (input : LazyRevealProbe.Query Coordinate) (context : DeferredContext)
    (entry : HistoryResolvedPrefix ((LazyRevealProbe.World Coordinate).Range input))
    (hentry : some entry ∈ support (runResolvedHistoryPrefix (eraseProbeQueries (liftM (OracleSpec.query input))) context 0 [])) :
    entry.remaining = 0 ∧ entry.history = [] := by
  have hh := historyPrefix_history_eq_of_probeFree _ context 0 [] entry (eraseProbeQueries_probeFree _) hentry
  refine ⟨?_, hh⟩
  cases input <;> simp_all [runResolvedHistoryPrefix, eraseProbeQueries, historyAdaptiveQueryStep,
    historyCompletionQueryStep]
  case uniform => obtain ⟨_, rfl⟩ := hentry; rfl
  case hashOutput => obtain ⟨_, _, rfl⟩ := hentry; rfl
  case reveal coordinate =>
    cases coordinate with
    | chainStart lay tree leafIdx chainIdx =>
        dsimp only at hentry
        split at hentry
        · split_ifs at hentry
          · simp at hentry
          · simp only [mem_support_pure_iff, Option.some.injEq] at hentry
            cases hentry
            rfl
        · simp only [ChainStartHistoryOutputHit, List.not_mem_nil, false_and, exists_false, if_false,
            mem_support_bind_iff, mem_support_pure_iff, Option.some.injEq] at hentry
          obtain ⟨_, _, rfl⟩ := hentry
          rfl
    | position position =>
        simp only [mem_support_bind_iff] at hentry
        obtain ⟨option, _, hentry⟩ := hentry
        cases option with
        | none => simp at hentry
        | some resolved =>
            simp only [mem_support_pure_iff, Option.some.injEq] at hentry
            cases hentry
            rfl

theorem erasedHistoryPrivateCutCharge_query_bind_of_no_access
    (target : Position) (input : LazyRevealProbe.Query Coordinate)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (ordinal : Nat)
    (hdisclose : ¬IsPrivatePositionDisclosure target input) (hprobe : ¬IsPrivatePositionProbe target input) :
    erasedHistoryPrivateCutCharge target ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next)
      context ordinal =
      ∑' result, Pr[= result | runResolvedHistoryPrefix (eraseProbeQueries (liftM (OracleSpec.query input))) context 0 []] *
        match result with
        | none => 0
        | some result => erasedHistoryPrivateCutCharge target (next result.value) result.context ordinal := by
  unfold erasedHistoryPrivateCutCharge
  rw [privatePositionProbeCutAt_query_bind, if_neg hdisclose, if_neg hprobe, eraseProbeQueries_query_bind,
    runResolvedHistoryPrefix_bind, probEvent_bind_eq_tsum]
  apply tsum_congr
  intro result
  by_cases hresult : result ∈ support (runResolvedHistoryPrefix (eraseProbeQueries (liftM (OracleSpec.query input))) context 0 [])
  · cases result with
    | none => simp [HistoryPrivateProbeCutReached, privatePositionAccessCandidate]
    | some result =>
        have hf := erasedHistoryQueryStep_fields input context result hresult
        simp only [hf.1, hf.2]
  · simp [probOutput_eq_zero_of_not_mem_support hresult]

theorem erasedHistoryPrivateCutCharge_disclosure
    (target : Position) (input : LazyRevealProbe.Query Coordinate)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (ordinal : Nat)
    (hdisclose : IsPrivatePositionDisclosure target input) :
    erasedHistoryPrivateCutCharge target ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next)
      context ordinal = 0 := by
  unfold erasedHistoryPrivateCutCharge
  rw [privatePositionProbeCutAt_query_bind, if_pos hdisclose]
  cases input <;> simp_all [IsPrivatePositionDisclosure, eraseProbeQueries, runResolvedHistoryPrefix,
    HistoryPrivateProbeCutReached, privatePositionAccessCandidate]

theorem erasedHistoryPrivateCutCharge_probe_target_zero
    (target : Position) (digest : Digest) (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) :
    erasedHistoryPrivateCutCharge target ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) (.probe (.position target) digest)) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next)
      context 0 = 1 := by
  unfold erasedHistoryPrivateCutCharge
  rw [privatePositionProbeCutAt_query_bind target (.probe (.position target) digest) next 0]
  simp [IsPrivatePositionDisclosure, IsPrivatePositionProbe,
    eraseProbeQueries, runResolvedHistoryPrefix, HistoryPrivateProbeCutReached, privatePositionAccessCandidate]

theorem erasedHistoryPrivateCutCharge_probe_target_succ
    (target : Position) (digest : Digest) (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (ordinal : Nat) :
    erasedHistoryPrivateCutCharge target ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) (.probe (.position target) digest)) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next)
      context (ordinal + 1) = erasedHistoryPrivateCutCharge target (next ()) context ordinal := by
  unfold erasedHistoryPrivateCutCharge
  rw [privatePositionProbeCutAt_query_bind target (.probe (.position target) digest) next (ordinal + 1)]
  simp only [IsPrivatePositionDisclosure, IsPrivatePositionProbe, if_false, if_true, eraseProbeQueries, OracleComp.construct_query_bind]

theorem sum_erasedHistoryPrivateCutCharge_query_bind_le
    (target : Position) (input : LazyRevealProbe.Query Coordinate)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (q : Nat) :
    (∑ ordinal ∈ Finset.range q, erasedHistoryPrivateCutCharge target
      ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next) context ordinal) ≤
      privatePositionProbeQueryCharge target input +
        ∑' result, Pr[= result | runResolvedHistoryPrefix (eraseProbeQueries (liftM (OracleSpec.query input))) context 0 []] *
          match result with
          | none => 0
          | some result => ∑ ordinal ∈ Finset.range q, erasedHistoryPrivateCutCharge target (next result.value) result.context ordinal := by
  by_cases hdisclose : IsPrivatePositionDisclosure target input
  · simp only [erasedHistoryPrivateCutCharge_disclosure target input next context _ hdisclose, Finset.sum_const_zero]
    exact bot_le
  · by_cases hprobe : IsPrivatePositionProbe target input
    · cases input <;> simp only [IsPrivatePositionProbe] at hprobe
      case probe coordinate digest =>
        subst coordinate
        have hstep : runResolvedHistoryPrefix
            (eraseProbeQueries (liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) (.probe (.position target) digest)))) context 0 [] =
            pure (some (⟨context, 0, (), []⟩ : HistoryResolvedPrefix Unit)) := rfl
        rw [hstep, tsum_probOutput_pure_mul]
        simp only [privatePositionProbeQueryCharge, IsPrivatePositionProbe, if_true]
        cases q with
        | zero => simp
        | succ q =>
            rw [Finset.sum_range_succ']
            rw [erasedHistoryPrivateCutCharge_probe_target_zero target digest next context]
            simp_rw [erasedHistoryPrivateCutCharge_probe_target_succ target digest next context]
            rw [add_comm]
            apply add_le_add le_rfl
            exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.le_succ q))
    · simp only [privatePositionProbeQueryCharge, if_neg hprobe, zero_add]
      apply le_of_eq
      simp_rw [erasedHistoryPrivateCutCharge_query_bind_of_no_access target input next context _ hdisclose hprobe]
      rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      apply tsum_congr
      intro result
      cases result <;> simp [Finset.mul_sum]

theorem erasedHistoryStartCutCharge_query_bind_of_not_probe
    (input : LazyRevealProbe.Query Coordinate)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (ordinal : Nat) (hprobe : ¬LazyRevealProbe.IsProbe input) :
    erasedHistoryStartCutCharge ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next) context ordinal =
      ∑' result, Pr[= result | runResolvedHistoryPrefix (eraseProbeQueries (liftM (OracleSpec.query input))) context 0 []] *
        match result with
        | none => 0
        | some result => erasedHistoryStartCutCharge (next result.value) result.context ordinal := by
  unfold erasedHistoryStartCutCharge
  rw [nativeProbeCutAt_query_bind, if_neg hprobe, eraseProbeQueries_query_bind,
    runResolvedHistoryPrefix_bind, probEvent_bind_eq_tsum]
  apply tsum_congr
  intro result
  by_cases hresult : result ∈ support (runResolvedHistoryPrefix (eraseProbeQueries (liftM (OracleSpec.query input))) context 0 [])
  · cases result with
    | none => simp [HistoryChainStartCutReached]
    | some result =>
        have hf := erasedHistoryQueryStep_fields input context result hresult
        simp only [hf.1, hf.2]
  · simp [probOutput_eq_zero_of_not_mem_support hresult]

theorem erasedHistoryStartCutCharge_probe_zero
    (coordinate : Coordinate) (digest : Digest) (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) :
    erasedHistoryStartCutCharge ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) (.probe coordinate digest)) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next)
      context 0 = chainStartProbeQueryCharge (.probe coordinate digest) := by
  unfold erasedHistoryStartCutCharge
  rw [nativeProbeCutAt_query_bind (.probe coordinate digest) next 0]
  cases coordinate <;> simp [LazyRevealProbe.IsProbe, eraseProbeQueries, runResolvedHistoryPrefix,
    HistoryChainStartCutReached, IsChainStartCut, chainStartProbeQueryCharge]

theorem erasedHistoryStartCutCharge_probe_succ
    (coordinate : Coordinate) (digest : Digest) (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (ordinal : Nat) :
    erasedHistoryStartCutCharge ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) (.probe coordinate digest)) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next)
      context (ordinal + 1) = erasedHistoryStartCutCharge (next ()) context ordinal := by
  unfold erasedHistoryStartCutCharge
  rw [nativeProbeCutAt_query_bind (.probe coordinate digest) next (ordinal + 1)]
  simp only [LazyRevealProbe.IsProbe, if_true, eraseProbeQueries, construct_query_bind]

theorem sum_erasedHistoryStartCutCharge_query_bind_le
    (input : LazyRevealProbe.Query Coordinate)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (q : Nat) :
    (∑ ordinal ∈ Finset.range q, erasedHistoryStartCutCharge
      ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next) context ordinal) ≤
      chainStartProbeQueryCharge input +
        ∑' result, Pr[= result | runResolvedHistoryPrefix (eraseProbeQueries (liftM (OracleSpec.query input))) context 0 []] *
          match result with
          | none => 0
          | some result => ∑ ordinal ∈ Finset.range q, erasedHistoryStartCutCharge (next result.value) result.context ordinal := by
  by_cases hprobe : LazyRevealProbe.IsProbe input
  · cases input <;> simp only [LazyRevealProbe.IsProbe] at hprobe
    case probe coordinate digest =>
      have hstep : runResolvedHistoryPrefix
          (eraseProbeQueries (liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) (.probe coordinate digest)))) context 0 [] =
          pure (some (⟨context, 0, (), []⟩ : HistoryResolvedPrefix Unit)) := rfl
      rw [hstep, tsum_probOutput_pure_mul]
      cases q with
      | zero => simp
      | succ q =>
          rw [Finset.sum_range_succ', erasedHistoryStartCutCharge_probe_zero coordinate digest next context]
          simp_rw [erasedHistoryStartCutCharge_probe_succ coordinate digest next context]
          rw [add_comm]
          apply add_le_add le_rfl
          exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.le_succ q))
  · have hz : chainStartProbeQueryCharge input = 0 := by cases input <;> simp_all [LazyRevealProbe.IsProbe, chainStartProbeQueryCharge]
    rw [hz, zero_add]
    apply le_of_eq
    simp_rw [erasedHistoryStartCutCharge_query_bind_of_not_probe input next context _ hprobe]
    rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    apply tsum_congr
    intro result
    cases result <;> simp [Finset.mul_sum]

noncomputable def sharedHistoryCutCharge
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (ordinals : Nat) : ENNReal :=
  (∑ ordinal ∈ Finset.range ordinals, erasedHistoryStartCutCharge computation context ordinal) +
    ∑ target ∈ targets, ∑ ordinal ∈ Finset.range ordinals, erasedHistoryPrivateCutCharge target computation context ordinal

theorem sharedHistoryCutCharge_query_bind_le
    (targets : Finset Position) (input : LazyRevealProbe.Query Coordinate)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (ordinals : Nat) :
    sharedHistoryCutCharge targets ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next) context ordinals ≤
      nativeProbeQueryCharge input +
        ∑' result, Pr[= result | runResolvedHistoryPrefix (eraseProbeQueries (liftM (OracleSpec.query input))) context 0 []] *
          match result with
          | none => 0
          | some result => sharedHistoryCutCharge targets (next result.value) result.context ordinals := by
  unfold sharedHistoryCutCharge
  apply (add_le_add (sum_erasedHistoryStartCutCharge_query_bind_le input next context ordinals)
    (Finset.sum_le_sum (fun target _ => sum_erasedHistoryPrivateCutCharge_query_bind_le target input next context ordinals))).trans
  rw [Finset.sum_add_distrib, ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  rw [add_add_add_comm]
  apply add_le_add
  · rw [← chainStart_add_structural_probeQueryCharge]
    exact add_le_add le_rfl (sum_privatePositionProbeQueryCharge_le_structural targets input)
  · rw [← ENNReal.tsum_add]
    apply ENNReal.tsum_le_tsum
    intro result
    cases result <;> simp [Finset.mul_sum, mul_add]

theorem sharedHistoryCutCharge_le_probeBound
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (q ordinals : Nat) (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe q) :
    sharedHistoryCutCharge targets computation context ordinals ≤ q := by
  induction computation using OracleComp.inductionOn generalizing context q with
  | pure value =>
      simp [sharedHistoryCutCharge, erasedHistoryStartCutCharge, erasedHistoryPrivateCutCharge,
        nativeProbeCutAt, privatePositionProbeCutAt, eraseProbeQueries, runResolvedHistoryPrefix,
        HistoryChainStartCutReached, HistoryPrivateProbeCutReached, IsChainStartCut, privatePositionAccessCandidate]
  | query_bind input next ih =>
      apply (sharedHistoryCutCharge_query_bind_le targets input next context ordinals).trans
      rw [isQueryBoundP_query_bind_iff] at hbound
      let cost : Nat := if LazyRevealProbe.IsProbe input then 1 else 0
      have hcost : nativeProbeQueryCharge input = (cost : ENNReal) := by
        by_cases hp : LazyRevealProbe.IsProbe input <;> simp [nativeProbeQueryCharge, cost, hp]
      have hle : cost ≤ q := by
        by_cases hp : LazyRevealProbe.IsProbe input
        · have hpos := hbound.1.resolve_left (not_not.mpr hp)
          simp only [cost, if_pos hp]
          omega
        · simp [cost, hp]
      have htail : (∑' result, Pr[= result | runResolvedHistoryPrefix (eraseProbeQueries (liftM (OracleSpec.query input))) context 0 []] *
          match result with
          | none => 0
          | some result => sharedHistoryCutCharge targets (next result.value) result.context ordinals) ≤ ((q - cost : Nat) : ENNReal) := by
        calc
          _ ≤ ∑' result, Pr[= result | runResolvedHistoryPrefix (eraseProbeQueries (liftM (OracleSpec.query input))) context 0 []] *
              ((q - cost : Nat) : ENNReal) := by
            apply ENNReal.tsum_le_tsum
            intro result
            apply mul_le_mul' le_rfl
            cases result with
            | none => exact bot_le
            | some result =>
                apply ih result.value result.context (q - cost)
                by_cases hp : LazyRevealProbe.IsProbe input <;> simpa [cost, hp] using hbound.2 result.value
          _ ≤ _ := by
            rw [ENNReal.tsum_mul_right]
            exact mul_le_of_le_one_left (by positivity) tsum_probOutput_le_one
      rw [hcost]
      exact (add_le_add le_rfl htail).trans_eq (by rw [← Nat.cast_add, Nat.add_sub_of_le hle])

end SphincsSecurity.Concrete.OtsProbeSimulation

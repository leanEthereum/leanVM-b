import SphincsSecurity.Proof.OtsProbeErasedHistoryCost

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem runErasedHistoryCharged_cost_le_probeBound
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (context : DeferredContext) (q : Nat)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe q)
    (result : Option (HistoryResolvedPrefix α) × Nat)
    (hresult : result ∈ support (runErasedHistoryCharged computation context)) : result.2 ≤ q := by
  induction computation using OracleComp.inductionOn generalizing context q result with
  | pure value =>
      simp only [runErasedHistoryCharged, construct_pure, mem_support_pure_iff] at hresult
      rw [hresult]
      exact Nat.zero_le _
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      let charge : Nat := if LazyRevealProbe.IsProbe input then 1 else 0
      have hcharge : charge ≤ q := by
        by_cases hprobe : LazyRevealProbe.IsProbe input
        · have hpos := hbound.1.resolve_left (not_not.mpr hprobe)
          simp only [charge, if_pos hprobe]
          omega
        · simp [charge, hprobe]
      rw [runErasedHistoryCharged_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨entry, _, hresult⟩ := hresult
      cases entry with
      | none =>
          simp only [mem_support_pure_iff] at hresult
          rw [hresult]
          exact hcharge
      | some entry =>
          rw [support_map] at hresult
          obtain ⟨tail, htail, rfl⟩ := hresult
          have htailBound : (next entry.value).IsQueryBoundP LazyRevealProbe.IsProbe (q - charge) := by
            by_cases hprobe : LazyRevealProbe.IsProbe input <;> simpa [charge, hprobe] using hbound.2 entry.value
          have hle := ih entry.value entry.context (q - charge) htailBound tail htail
          change tail.2 + charge ≤ q
          omega

theorem expectedErasedHistoryProbeCost_le_probeBound
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (context : DeferredContext) (q : Nat)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe q) :
    expectedErasedHistoryProbeCost computation context ≤ q := by
  calc
    _ ≤ ∑' result, Pr[= result | runErasedHistoryCharged computation context] * (q : ENNReal) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hresult : result ∈ support (runErasedHistoryCharged computation context)
      · exact mul_le_mul' le_rfl (Nat.cast_le.mpr (runErasedHistoryCharged_cost_le_probeBound computation context q hbound result hresult))
      · simp only [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, le_refl]
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left (by positivity) tsum_probOutput_le_one

theorem expectedErasedHistoryProbeCost_eq_zero_of_probeFree
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (context : DeferredContext)
    (hfree : computation.IsQueryBoundP LazyRevealProbe.IsProbe 0) :
    expectedErasedHistoryProbeCost computation context = 0 := by
  exact le_antisymm (by simpa only [Nat.cast_zero] using expectedErasedHistoryProbeCost_le_probeBound computation context 0 hfree) bot_le

theorem runErasedHistoryCharged_bind
    (left : OracleComp (LazyRevealProbe.World Coordinate) α)
    (next : α → OracleComp (LazyRevealProbe.World Coordinate) β) (context : DeferredContext) :
    runErasedHistoryCharged (left >>= next) context =
      runErasedHistoryCharged left context >>= fun result =>
        match result.1 with
        | none => pure (none, result.2)
        | some entry => (fun tail => (tail.1, tail.2 + result.2)) <$>
            runErasedHistoryCharged (next entry.value) entry.context := by
  induction left using OracleComp.inductionOn generalizing context with
  | pure value =>
      simp only [pure_bind, runErasedHistoryCharged, construct_pure, Nat.add_zero, Prod.mk.eta]
      change _ = id <$> _
      rw [id_map]
  | query_bind input continuation ih =>
      rw [bind_assoc, runErasedHistoryCharged_query_bind, runErasedHistoryCharged_query_bind, bind_assoc]
      apply bind_congr
      intro entry
      cases entry with
      | none => rfl
      | some entry =>
          dsimp only
          rw [ih, map_bind, bind_map_left]
          apply bind_congr
          rintro ⟨result, cost⟩
          cases result with
          | none => rfl
          | some result =>
              simp only [Functor.map_map]
              apply congrArg (fun f => f <$> _)
              funext tail
              simp only [Nat.add_assoc]

theorem expectedErasedHistoryProbeCost_bind
    (left : OracleComp (LazyRevealProbe.World Coordinate) α)
    (next : α → OracleComp (LazyRevealProbe.World Coordinate) β) (context : DeferredContext) :
    expectedErasedHistoryProbeCost (left >>= next) context = expectedErasedHistoryProbeCost left context +
      ∑' entry, Pr[= entry | runResolvedHistoryPrefix (eraseProbeQueries left) context 0 []] *
        match entry with
        | none => 0
        | some entry => expectedErasedHistoryProbeCost (next entry.value) entry.context := by
  let tailCost : Option (HistoryResolvedPrefix α) → ENNReal := fun entry =>
    match entry with
    | none => 0
    | some entry => expectedErasedHistoryProbeCost (next entry.value) entry.context
  unfold expectedErasedHistoryProbeCost at ⊢
  rw [runErasedHistoryCharged_bind, tsum_probOutput_bind_mul]
  have hresume (result : Option (HistoryResolvedPrefix α) × Nat) :
      (∑' tail, Pr[= tail | (match result.1 with
        | none => pure (none, result.2)
        | some entry => (fun tail : Option (HistoryResolvedPrefix β) × Nat => (tail.1, tail.2 + result.2)) <$>
            runErasedHistoryCharged (next entry.value) entry.context)] * (tail.2 : ENNReal)) =
        (result.2 : ENNReal) + tailCost result.1 := by
    rcases result with ⟨entry, cost⟩
    cases entry with
    | none => simp only [tsum_probOutput_pure_mul, tailCost, add_zero]
    | some entry =>
        rw [tsum_probOutput_map_mul]
        simp only [Nat.cast_add, mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
        exact add_comm _ _
  calc
    _ = ∑' result, Pr[= result | runErasedHistoryCharged left context] * ((result.2 : ENNReal) + tailCost result.1) := by
      apply tsum_congr
      intro result
      apply congrArg (fun cost => _ * cost)
      rcases result with ⟨entry, cost⟩
      cases entry with
      | none => exact hresume (none, cost)
      | some entry => exact hresume (some entry, cost)
    _ = (∑' result, Pr[= result | runErasedHistoryCharged left context] * (result.2 : ENNReal)) +
        ∑' entry, Pr[= entry | Prod.fst <$> runErasedHistoryCharged left context] * tailCost entry := by
      rw [tsum_probOutput_map_mul]
      simp_rw [mul_add]
      rw [ENNReal.tsum_add]
    _ = _ := by
      apply congrArg (fun cost => _ + cost)
      apply tsum_congr
      intro entry
      rw [OracleComp.probOutput_congr (x := entry) (y := entry) rfl (runErasedHistoryCharged_result left context)]
      cases entry <;> rfl

end SphincsSecurity.Concrete.OtsProbeSimulation

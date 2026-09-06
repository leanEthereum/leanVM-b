import SphincsSecurity.Proof.FewTimeWeightedOriginAdaptive
import SphincsSecurity.Proof.FewTimeRawTargetBound

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

noncomputable def OriginTargetMonitorState.weightedPotential
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginTargetMonitorState configuration) (reuseWeight : ℝ≥0∞)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop) : ℝ≥0∞ :=
  if state.valid then
    match state.targetView with
    | some target => state.origin.weightedPotential reuseWeight fun views => event (views, target)
    | none => ∑ target, Pr[fun value : FewTimeView => value = target |
        ($ᵗ FewTimeView : ProbComp FewTimeView)] *
          state.origin.weightedPotential reuseWeight (fun views => event (views, target))
  else 0

theorem OriginTargetMonitorState.expected_weightedPotential_advanceOrigin_le {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginTargetMonitorState configuration)
    (mass : α → ℝ≥0∞) (nextOrigin : α → OriginMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (hnext : ∀ target,
      (∑' result, mass result *
        (nextOrigin result).weightedPotential reuseWeight (fun views => event (views, target))) ≤
      state.origin.weightedPotential reuseWeight (fun views => event (views, target))) :
    (∑' result, mass result *
      (state.advanceOrigin (nextOrigin result)).weightedPotential reuseWeight event) ≤
      state.weightedPotential reuseWeight event := by
  classical
  cases hvalid : state.valid with
  | false =>
      simp [OriginTargetMonitorState.weightedPotential,
        OriginTargetMonitorState.advanceOrigin, hvalid]
  | true =>
      cases htarget : state.targetView with
      | some target =>
          simpa [OriginTargetMonitorState.weightedPotential,
            OriginTargetMonitorState.advanceOrigin, hvalid, htarget] using hnext target
      | none =>
          simp only [OriginTargetMonitorState.weightedPotential,
            OriginTargetMonitorState.advanceOrigin, hvalid, htarget, if_true]
          calc
            (∑' result, mass result *
                ∑ target, Pr[fun value : FewTimeView => value = target |
                  ($ᵗ FewTimeView : ProbComp FewTimeView)] *
                    (nextOrigin result).weightedPotential reuseWeight (fun views => event (views, target))) =
                ∑ target, Pr[fun value : FewTimeView => value = target |
                  ($ᵗ FewTimeView : ProbComp FewTimeView)] *
                    ∑' result, mass result *
                      (nextOrigin result).weightedPotential reuseWeight
                        (fun views => event (views, target)) := by
              calc
                _ = ∑' result, ∑ target,
                    mass result *
                      (Pr[fun value : FewTimeView => value = target |
                          ($ᵗ FewTimeView : ProbComp FewTimeView)] *
                        (nextOrigin result).weightedPotential reuseWeight
                          (fun views => event (views, target))) := by
                    apply tsum_congr
                    intro result
                    rw [Finset.mul_sum]
                _ = ∑ target, ∑' result,
                    mass result *
                      (Pr[fun value : FewTimeView => value = target |
                          ($ᵗ FewTimeView : ProbComp FewTimeView)] *
                        (nextOrigin result).weightedPotential reuseWeight
                          (fun views => event (views, target))) := by
                    exact Summable.tsum_finsetSum fun _ _ => ENNReal.summable
                _ = _ := by
                    apply Finset.sum_congr rfl
                    intro target _
                    calc
                      _ = ∑' result,
                          Pr[fun value : FewTimeView => value = target |
                              ($ᵗ FewTimeView : ProbComp FewTimeView)] *
                            (mass result *
                              (nextOrigin result).weightedPotential reuseWeight
                                (fun views => event (views, target))) := by
                            apply tsum_congr
                            intro result
                            ac_rfl
                      _ = _ := ENNReal.tsum_mul_left
            _ ≤ _ := by
              apply Finset.sum_le_sum
              intro target _
              exact mul_le_mul' le_rfl (hnext target)

theorem OriginTargetMonitorState.weightedPotential_eq_one_of_complete {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (hcomplete : state.Complete)
    (hevent : ∀ target, state.targetView = some target →
      event (state.origin.observation.views, target)) :
    state.weightedPotential reuseWeight event = 1 := by
  rcases hcomplete with ⟨hvalid, horigin, target, htarget⟩
  simp [OriginTargetMonitorState.weightedPotential, hvalid, htarget,
    state.origin.weightedPotential_eq_one_of_complete
      (fun views => event (views, target)) horigin (hevent target htarget)]

theorem OriginTargetMonitorState.weightedPotential_initial {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources)
    (cache : QueryCache HashSpec)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop) :
    (OriginTargetMonitorState.initial configuration cache).weightedPotential reuseWeight event =
      (((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ * reuseWeight) ^ configuration.prehit.card *
        Pr[event | ($ᵗ ((pattern.selected → FewTimeView) × FewTimeView) :
          ProbComp ((pattern.selected → FewTimeView) × FewTimeView))] := by
  classical
  rw [OriginTargetMonitorState.weightedPotential]
  simp only [OriginTargetMonitorState.initial, if_true]
  simp_rw [OriginMonitorState.weightedPotential_initial]
  rw [probEvent_uniform_views_target_eq_sum pattern event]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro target _
  ac_rfl

noncomputable def OriginTargetMonitorState.rawWeightedPotential
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginTargetMonitorState configuration) (reuseWeight : ℝ≥0∞)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop) : ℝ≥0∞ :=
  (if state.targetView = none then ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ else 1) *
    state.weightedPotential reuseWeight event

theorem OriginTargetMonitorState.expected_rawWeightedPotential_advanceOrigin_le {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginTargetMonitorState configuration)
    (mass : α → ℝ≥0∞) (nextOrigin : α → OriginMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (hnext : ∀ target,
      (∑' result, mass result *
        (nextOrigin result).weightedPotential reuseWeight (fun views => event (views, target))) ≤
      state.origin.weightedPotential reuseWeight (fun views => event (views, target))) :
    (∑' result, mass result *
      (state.advanceOrigin (nextOrigin result)).rawWeightedPotential reuseWeight event) ≤
      state.rawWeightedPotential reuseWeight event := by
  have hbound := state.expected_weightedPotential_advanceOrigin_le mass nextOrigin event hnext
  simp only [advanceOrigin] at hbound
  cases htarget : state.targetView with
  | none =>
      simp only [htarget] at hbound
      simp only [rawWeightedPotential, advanceOrigin, htarget, ↓reduceIte]
      simp_rw [mul_left_comm (mass _)]
      rw [ENNReal.tsum_mul_left]
      exact mul_le_mul_right hbound (((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹)
  | some target =>
      simpa only [rawWeightedPotential, advanceOrigin, htarget, reduceCtorEq, ↓reduceIte, one_mul]
        using hbound

theorem OriginTargetMonitorState.rawWeightedPotential_afterRawDirect_of_ordinal_ne {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (state : OriginTargetMonitorState configuration)
    (input : HashInput) (output : HashOutput)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (hne : state.candidateOrdinal ≠ targetOrdinal) :
    (state.afterRawDirect targetOrdinal input output).rawWeightedPotential reuseWeight event =
      (state.advanceOrigin (state.origin.afterDirect input output)).rawWeightedPotential reuseWeight event := by
  by_cases hfresh : state.origin.viewed.cache input = none
  · simp [afterRawDirect, hfresh, rawWeightedPotential, weightedPotential, recordCandidate, advanceOrigin, hne]
  · simp [afterRawDirect, hfresh]

theorem OriginTargetMonitorState.expected_rawWeightedPotential_afterRawDirect_le {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (targetOrdinal : Nat) (state : OriginTargetMonitorState configuration)
    (input : HashInput)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (horigin : state.origin.ScheduleCoherent)
    (htarget : state.TargetScheduleCoherent targetOrdinal) :
    (∑' result, Pr[= result | (randomOracle input).run state.origin.viewed.cache] *
      (state.afterRawDirect targetOrdinal input result.1).rawWeightedPotential reuseWeight event) ≤
      state.rawWeightedPotential reuseWeight event := by
  classical
  by_cases hfresh : state.origin.viewed.cache input = none
  · by_cases heq : state.candidateOrdinal = targetOrdinal
    · cases hsource : configuration.sourceAt? state.origin.directOrdinal with
      | some selected =>
          have hzero : ∀ output,
              (state.afterRawDirect targetOrdinal input output).rawWeightedPotential reuseWeight event = 0 := by
            intro output
            simp [afterRawDirect, hfresh, hsource, rawWeightedPotential, weightedPotential,
              recordCandidate, advanceOrigin, heq]
          simp_rw [hzero]
          simp
      | none =>
          cases hvalid : state.valid with
          | false =>
              have hzero : ∀ output,
                  (state.afterRawDirect targetOrdinal input output).rawWeightedPotential reuseWeight event = 0 := by
                intro output
                simp [afterRawDirect, hfresh, hsource, rawWeightedPotential, weightedPotential,
                  recordCandidate, advanceOrigin, heq, hvalid]
              simp_rw [hzero]
              simp
          | true =>
              have htargetView : state.targetView = none :=
                state.targetView_eq_none_of_candidateOrdinal_eq htarget heq
              calc
                _ ≤ ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ *
                    ∑ target, Pr[fun value : FewTimeView => value = target |
                      ($ᵗ FewTimeView : ProbComp FewTimeView)] *
                        state.origin.weightedPotential reuseWeight (fun views => event (views, target)) := by
                  apply tsum_probOutput_randomOracle_fresh_admissible_view_mul_le_expected
                    input state.origin.viewed.cache hfresh
                  · intro result _ hnone
                    simp [afterRawDirect, hfresh, hsource, rawWeightedPotential, weightedPotential,
                      recordCandidate, advanceOrigin, heq, hvalid, hnone]
                  · intro result _ hsome
                    simp [afterRawDirect, hfresh, hsource, rawWeightedPotential, weightedPotential,
                      recordCandidate, advanceOrigin, heq, hvalid, hsome,
                      state.origin.weightedPotential_afterDirect_of_sourceAt?_eq_none
                        input result.1 _ hsource]
                _ = state.rawWeightedPotential reuseWeight event := by
                  simp [rawWeightedPotential, weightedPotential, hvalid, htargetView]
    · simp_rw [state.rawWeightedPotential_afterRawDirect_of_ordinal_ne targetOrdinal input _ event heq]
      apply state.expected_rawWeightedPotential_advanceOrigin_le
      intro target
      exact state.origin.expected_weightedPotential_afterDirect_le input
        (fun views => event (views, target)) horigin
  · simp_rw [afterRawDirect, hfresh, if_false]
    apply state.expected_rawWeightedPotential_advanceOrigin_le
    intro target
    exact state.origin.expected_weightedPotential_afterDirect_le input
      (fun views => event (views, target)) horigin

theorem OriginTargetMonitorState.rawWeightedPotential_eq_one_of_complete {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginTargetMonitorState configuration)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop)
    (hcomplete : state.Complete)
    (hevent : ∀ target, state.targetView = some target →
      event (state.origin.observation.views, target)) :
    state.rawWeightedPotential reuseWeight event = 1 := by
  obtain ⟨target, htarget⟩ := hcomplete.2.2
  simp only [rawWeightedPotential, htarget, reduceCtorEq, ↓reduceIte, one_mul]
  exact state.weightedPotential_eq_one_of_complete event hcomplete hevent

theorem OriginTargetMonitorState.rawWeightedPotential_initial {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources)
    (cache : QueryCache HashSpec)
    (event : (pattern.selected → FewTimeView) × FewTimeView → Prop) :
    (OriginTargetMonitorState.initial configuration cache).rawWeightedPotential reuseWeight event =
      ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ *
        ((((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ * reuseWeight) ^ configuration.prehit.card *
          Pr[event | ($ᵗ ((pattern.selected → FewTimeView) × FewTimeView) : ProbComp _)]) := by
  rw [rawWeightedPotential, weightedPotential_initial]
  simp only [initial, ↓reduceIte]

end SphincsSecurity.Concrete

import SphincsSecurity.Proof.FewTimeOriginInvariant

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

namespace Concrete

noncomputable def OriginMonitorState.weightedPotential {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) (reuseWeight : ℝ≥0∞)
    (event : (pattern.selected → FewTimeView) → Prop) : ℝ≥0∞ :=
  if state.valid then
    (((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ * reuseWeight) ^ state.pendingSources.card *
      reuseWeight ^ state.pendingReuses.card *
        state.completionMass event
  else 0


theorem OriginMonitorState.weightedPotential_eq_potential
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration)
    (event : (pattern.selected → FewTimeView) → Prop) :
    state.weightedPotential ((2 ^ 117 : Nat) : ℝ≥0∞)⁻¹ event = state.potential event := by
  unfold OriginMonitorState.weightedPotential OriginMonitorState.potential
  rw [mul_comm ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹, prehit_race_source_weight]

theorem source_reuse_parametric_weighted_sum
    {Index : Type} [Fintype Index] (probability mass : Index → ℝ≥0∞)
    (reuseWeight : ℝ≥0∞) (sourceCount reuseCount : Nat) (totalMass : ℝ≥0∞)
    (hmass : (∑ index, probability index * mass index) = totalMass) :
    ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ *
        ∑ index, probability index *
          ((((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ * reuseWeight) ^ sourceCount *
            reuseWeight ^ (reuseCount + 1) * mass index) =
      (((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ * reuseWeight) ^ (sourceCount + 1) *
        reuseWeight ^ reuseCount * totalMass := by
  rw [uniform_weighted_sum probability mass _ totalMass hmass, pow_succ, pow_succ]
  ring

theorem OriginMonitorState.weightedPotential_initial {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources)
    (cache : QueryCache HashSpec)
    (event : (pattern.selected → FewTimeView) → Prop) :
    (OriginMonitorState.initial configuration cache).weightedPotential reuseWeight event =
      (((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ * reuseWeight) ^ configuration.prehit.card *
        Pr[event | ($ᵗ (pattern.selected → FewTimeView) :
          ProbComp (pattern.selected → FewTimeView))] := by
  classical
  rw [OriginMonitorState.weightedPotential]
  rw [if_pos (show (OriginMonitorState.initial configuration cache).valid = true from rfl),
    OriginMonitorState.pendingSources_initial,
    OriginMonitorState.pendingReuses_initial, pow_zero, mul_one]
  rw [OriginMonitorState.completionMass]
  change (((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ * reuseWeight) ^ configuration.prehit.card *
      Pr[event | (OriginObservation.empty configuration).completedViews] = _
  rw [OriginObservation.completedViews_empty]

theorem OriginMonitorState.weightedPotential_advanceSigner_of_selectedAt?_eq_none {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration)
    (event : (pattern.selected → FewTimeView) → Prop)
    (hselected : pattern.selectedAt? state.signerOrdinal = none) :
    state.advanceSigner.weightedPotential reuseWeight event = state.weightedPotential reuseWeight event := by
  classical
  rw [OriginMonitorState.weightedPotential, OriginMonitorState.weightedPotential]
  have hvalid : state.advanceSigner.valid = state.valid := rfl
  rw [hvalid]
  congr 1
  rw [congrArg Finset.card state.pendingSources_advanceSigner,
    congrArg Finset.card
      (state.pendingReuses_advanceSigner_of_selectedAt?_eq_none hselected)]
  rfl

theorem OriginMonitorState.sum_uniform_weightedPotential_recordSourceState {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) (selected : ↑configuration.prehit)
    (input : HashInput) (event : (pattern.selected → FewTimeView) → Prop)
    (hvalid : state.valid = true)
    (hnotSource : selected ∉ state.observation.seenSources)
    (hnotView : selected.1 ∉ state.observation.seenViews)
    (hpending : state.signerOrdinal ≤ selected.1.1.val) :
    ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ *
        ∑ view, Pr[fun value : FewTimeView => value = view |
          ($ᵗ FewTimeView : ProbComp FewTimeView)] *
            (state.recordSourceState selected input view).weightedPotential reuseWeight event =
      state.weightedPotential reuseWeight event := by
  classical
  have hsource := state.pendingSources_recordSourceState_card_add_one
    selected input default hnotSource
  have hsourceView : ∀ view,
      (state.recordSourceState selected input view).pendingSources.card =
        (state.recordSourceState selected input default).pendingSources.card := fun view => by
    rw [state.pendingSources_recordSourceState selected input view,
      state.pendingSources_recordSourceState selected input default]
  have hreusesView : ∀ view,
      (state.recordSourceState selected input view).pendingReuses.card =
        state.pendingReuses.card + 1 := fun view =>
    state.pendingReuses_recordSourceState_card selected input view hnotSource hpending
  have hnextValid : ∀ view,
      (state.recordSourceState selected input view).valid = true := fun _ => hvalid
  simp_rw [OriginMonitorState.weightedPotential, if_pos hvalid]
  simp_rw [if_pos (hnextValid _), OriginMonitorState.completionMass,
    hsourceView, hreusesView]
  rw [← hsource]
  apply source_reuse_parametric_weighted_sum
  exact state.observation.sum_uniform_prob_completedViews_recordSource
    selected input hnotView event

theorem OriginMonitorState.sum_uniform_weightedPotential_recordFreshState {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) (selected : pattern.selected)
    (event : (pattern.selected → FewTimeView) → Prop)
    (hvalid : state.valid = true)
    (hnotView : selected ∉ state.observation.seenViews)
    (hordinal : selected.1.val = state.signerOrdinal)
    (hnotPrehit : selected ∉ configuration.prehit) :
    (∑ view, Pr[fun value : FewTimeView => value = view |
        ($ᵗ FewTimeView : ProbComp FewTimeView)] *
          (state.recordFreshState selected view).weightedPotential reuseWeight event) =
      state.weightedPotential reuseWeight event := by
  classical
  have hsources : ∀ view,
      (state.recordFreshState selected view).pendingSources.card =
        state.pendingSources.card := fun view => congrArg Finset.card
          (state.pendingSources_recordFreshState selected view)
  have hreuses : ∀ view,
      (state.recordFreshState selected view).pendingReuses.card =
        state.pendingReuses.card := fun view => congrArg Finset.card
          (state.pendingReuses_recordFreshState selected view hordinal hnotPrehit)
  have hnextValid : ∀ view,
      (state.recordFreshState selected view).valid = true := fun _ => hvalid
  simp_rw [OriginMonitorState.weightedPotential, if_pos hvalid]
  simp_rw [if_pos (hnextValid _), OriginMonitorState.completionMass, hsources, hreuses]
  apply uniform_weighted_sum
  exact state.observation.sum_uniform_prob_completedViews_recordFresh selected hnotView event

theorem OriginMonitorState.reuseWeight_mul_weightedPotential_advanceSigner {reuseWeight : ℝ≥0∞}
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) (selected : ↑configuration.prehit)
    (event : (pattern.selected → FewTimeView) → Prop)
    (hvalid : state.valid = true)
    (hseen : selected ∈ state.observation.seenSources)
    (hordinal : selected.1.1.val = state.signerOrdinal) :
    reuseWeight * state.advanceSigner.weightedPotential reuseWeight event =
      state.weightedPotential reuseWeight event := by
  classical
  have hsources : state.advanceSigner.pendingSources.card = state.pendingSources.card :=
    congrArg Finset.card state.pendingSources_advanceSigner
  have hreuses := state.pendingReuses_advanceSigner_card_add_one selected hseen hordinal
  have hnextValid : state.advanceSigner.valid = true := hvalid
  rw [OriginMonitorState.weightedPotential, if_pos hnextValid,
    OriginMonitorState.weightedPotential, if_pos hvalid,
    hsources, OriginMonitorState.completionMass, OriginMonitorState.completionMass]
  change reuseWeight *
      ((((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ * reuseWeight) ^ state.pendingSources.card *
        reuseWeight ^ state.advanceSigner.pendingReuses.card *
          Pr[event | state.observation.completedViews]) = _
  rw [← hreuses, pow_succ _ state.advanceSigner.pendingReuses.card]
  ring

end Concrete

end SphincsSecurity

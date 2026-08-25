import SphincsSecurity.Proof.FewTimeOriginMonitor
import SphincsSecurity.Proof.FewTimeOriginWP
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable

/-!
# Partial-observation potential for a few-time origin configuration

Observed selected views are fixed and every unseen selected position is completed uniformly. The
completion law below is the marginal identity used when a configured fresh source or signer records
one new view.
-/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

namespace Concrete

noncomputable def OriginObservation.completeViews {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (observation : OriginObservation configuration)
    (fallback : pattern.selected → FewTimeView) : pattern.selected → FewTimeView :=
  fun selected => if selected ∈ observation.seenViews then observation.views selected
    else fallback selected

noncomputable def OriginObservation.completedViews {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (observation : OriginObservation configuration) :
    ProbComp (pattern.selected → FewTimeView) :=
  observation.completeViews <$> ($ᵗ (pattern.selected → FewTimeView) :
    ProbComp (pattern.selected → FewTimeView))

theorem OriginObservation.completeViews_recordFresh {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (observation : OriginObservation configuration) (selected : pattern.selected)
    (view : FewTimeView) (fallback : pattern.selected → FewTimeView)
    (hnotSeen : selected ∉ observation.seenViews) :
    (observation.recordFresh selected view).completeViews fallback =
      observation.completeViews (Function.update fallback selected view) := by
  classical
  funext other
  by_cases hother : other = selected
  · subst other
    simp [OriginObservation.completeViews, OriginObservation.recordFresh, hnotSeen]
  · simp [OriginObservation.completeViews, OriginObservation.recordFresh, hother]

theorem OriginObservation.completeViews_recordSource {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (observation : OriginObservation configuration)
    (selected : ↑configuration.prehit) (input : HashInput) (view : FewTimeView)
    (fallback : pattern.selected → FewTimeView)
    (hnotSeen : selected.1 ∉ observation.seenViews) :
    (observation.recordSource selected input view).completeViews fallback =
      observation.completeViews (Function.update fallback selected.1 view) := by
  classical
  funext other
  by_cases hother : other = selected.1
  · subst other
    simp [OriginObservation.completeViews, OriginObservation.recordSource, hnotSeen]
  · simp [OriginObservation.completeViews, OriginObservation.recordSource, hother]

theorem OriginObservation.evalDist_uniform_recordFresh_completedViews
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (observation : OriginObservation configuration) (selected : pattern.selected)
    (hnotSeen : selected ∉ observation.seenViews) :
    𝒟[do
      let view ← ($ᵗ FewTimeView : ProbComp FewTimeView)
      (observation.recordFresh selected view).completedViews] =
      𝒟[observation.completedViews] := by
  classical
  simp only [OriginObservation.completedViews, map_eq_bind_pure_comp]
  have hrewrite :
      (do
        let view ← ($ᵗ FewTimeView : ProbComp FewTimeView)
        let fallback ← ($ᵗ (pattern.selected → FewTimeView) :
          ProbComp (pattern.selected → FewTimeView))
        pure ((observation.recordFresh selected view).completeViews fallback)) =
      (do
        let view ← ($ᵗ FewTimeView : ProbComp FewTimeView)
        let fallback ← ($ᵗ (pattern.selected → FewTimeView) :
          ProbComp (pattern.selected → FewTimeView))
        pure (observation.completeViews (Function.update fallback selected view))) := by
    apply bind_congr
    intro view
    apply bind_congr
    intro fallback
    rw [observation.completeViews_recordFresh selected view fallback hnotSeen]
  change 𝒟[(do
      let view ← ($ᵗ FewTimeView : ProbComp FewTimeView)
      let fallback ← ($ᵗ (pattern.selected → FewTimeView) :
        ProbComp (pattern.selected → FewTimeView))
      pure ((observation.recordFresh selected view).completeViews fallback))] =
    𝒟[(do
      let fallback ← ($ᵗ (pattern.selected → FewTimeView) :
        ProbComp (pattern.selected → FewTimeView))
      pure (observation.completeViews fallback))]
  rw [hrewrite]
  exact OracleComp.evalDist_uniformSample_bind_update_map
    (R := FewTimeView) selected observation.completeViews

theorem OriginObservation.evalDist_uniform_recordSource_completedViews
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (observation : OriginObservation configuration)
    (selected : ↑configuration.prehit) (input : HashInput)
    (hnotSeen : selected.1 ∉ observation.seenViews) :
    𝒟[do
      let view ← ($ᵗ FewTimeView : ProbComp FewTimeView)
      (observation.recordSource selected input view).completedViews] =
      𝒟[observation.completedViews] := by
  classical
  simp only [OriginObservation.completedViews, map_eq_bind_pure_comp]
  have hrewrite :
      (do
        let view ← ($ᵗ FewTimeView : ProbComp FewTimeView)
        let fallback ← ($ᵗ (pattern.selected → FewTimeView) :
          ProbComp (pattern.selected → FewTimeView))
        pure ((observation.recordSource selected input view).completeViews fallback)) =
      (do
        let view ← ($ᵗ FewTimeView : ProbComp FewTimeView)
        let fallback ← ($ᵗ (pattern.selected → FewTimeView) :
          ProbComp (pattern.selected → FewTimeView))
        pure (observation.completeViews (Function.update fallback selected.1 view))) := by
    apply bind_congr
    intro view
    apply bind_congr
    intro fallback
    rw [observation.completeViews_recordSource selected input view fallback hnotSeen]
  change 𝒟[(do
      let view ← ($ᵗ FewTimeView : ProbComp FewTimeView)
      let fallback ← ($ᵗ (pattern.selected → FewTimeView) :
        ProbComp (pattern.selected → FewTimeView))
      pure ((observation.recordSource selected input view).completeViews fallback))] =
    𝒟[(do
      let fallback ← ($ᵗ (pattern.selected → FewTimeView) :
        ProbComp (pattern.selected → FewTimeView))
      pure (observation.completeViews fallback))]
  rw [hrewrite]
  exact OracleComp.evalDist_uniformSample_bind_update_map
    (R := FewTimeView) selected.1 observation.completeViews

theorem OriginObservation.sum_uniform_prob_completedViews_recordFresh
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (observation : OriginObservation configuration) (selected : pattern.selected)
    (hnotSeen : selected ∉ observation.seenViews)
    (event : (pattern.selected → FewTimeView) → Prop) :
    (∑ view, Pr[fun value : FewTimeView => value = view |
        ($ᵗ FewTimeView : ProbComp FewTimeView)] *
      Pr[event | (observation.recordFresh selected view).completedViews]) =
      Pr[event | observation.completedViews] := by
  classical
  calc
    (∑ view, Pr[fun value : FewTimeView => value = view |
        ($ᵗ FewTimeView : ProbComp FewTimeView)] *
      Pr[event | (observation.recordFresh selected view).completedViews]) =
        ∑' view : FewTimeView, Pr[= view |
          ($ᵗ FewTimeView : ProbComp FewTimeView)] *
            Pr[event | (observation.recordFresh selected view).completedViews] := by
      simp only [tsum_fintype, probEvent_eq_eq_probOutput]
    _ = Pr[event | ($ᵗ FewTimeView : ProbComp FewTimeView) >>= fun view =>
          (observation.recordFresh selected view).completedViews] :=
      (probEvent_bind_eq_tsum _ _ _).symm
    _ = _ := probEvent_congr' (fun _ _ => Iff.rfl)
      (observation.evalDist_uniform_recordFresh_completedViews selected hnotSeen)

theorem OriginObservation.sum_uniform_prob_completedViews_recordSource
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (observation : OriginObservation configuration)
    (selected : ↑configuration.prehit) (input : HashInput)
    (hnotSeen : selected.1 ∉ observation.seenViews)
    (event : (pattern.selected → FewTimeView) → Prop) :
    (∑ view, Pr[fun value : FewTimeView => value = view |
        ($ᵗ FewTimeView : ProbComp FewTimeView)] *
      Pr[event | (observation.recordSource selected input view).completedViews]) =
      Pr[event | observation.completedViews] := by
  classical
  calc
    (∑ view, Pr[fun value : FewTimeView => value = view |
        ($ᵗ FewTimeView : ProbComp FewTimeView)] *
      Pr[event | (observation.recordSource selected input view).completedViews]) =
        ∑' view : FewTimeView, Pr[= view |
          ($ᵗ FewTimeView : ProbComp FewTimeView)] *
            Pr[event | (observation.recordSource selected input view).completedViews] := by
      simp only [tsum_fintype, probEvent_eq_eq_probOutput]
    _ = Pr[event | ($ᵗ FewTimeView : ProbComp FewTimeView) >>= fun view =>
          (observation.recordSource selected input view).completedViews] :=
      (probEvent_bind_eq_tsum _ _ _).symm
    _ = _ := probEvent_congr' (fun _ _ => Iff.rfl)
      (observation.evalDist_uniform_recordSource_completedViews selected input hnotSeen)

noncomputable def OriginMonitorState.pendingSources {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) : Finset ↑configuration.prehit := by
  classical
  exact Finset.univ.filter fun selected => selected ∉ state.observation.seenSources

noncomputable def OriginMonitorState.pendingReuses {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) : Finset ↑configuration.prehit := by
  classical
  exact Finset.univ.filter fun selected =>
    selected ∈ state.observation.seenSources ∧ state.signerOrdinal ≤ selected.1.1.val

noncomputable def OriginMonitorState.completionMass {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration)
    (event : (pattern.selected → FewTimeView) → Prop) : ℝ≥0∞ :=
  Pr[event | state.observation.completedViews]

noncomputable def OriginMonitorState.potential {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration)
    (event : (pattern.selected → FewTimeView) → Prop) : ℝ≥0∞ :=
  if state.valid then
    ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ ^ state.pendingSources.card *
      ((2 ^ 117 : Nat) : ℝ≥0∞)⁻¹ ^ state.pendingReuses.card *
        state.completionMass event
  else 0

@[simp]
theorem OriginMonitorState.pendingSources_initial {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources)
    (cache : QueryCache HashSpec) :
    (OriginMonitorState.initial configuration cache).pendingSources.card =
      configuration.prehit.card := by
  classical
  simp [OriginMonitorState.pendingSources, OriginMonitorState.initial,
    OriginObservation.empty]

@[simp]
theorem OriginMonitorState.pendingReuses_initial {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources)
    (cache : QueryCache HashSpec) :
    (OriginMonitorState.initial configuration cache).pendingReuses.card = 0 := by
  classical
  simp [OriginMonitorState.pendingReuses, OriginMonitorState.initial,
    OriginObservation.empty]

theorem OriginObservation.completedViews_empty {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) :
    (OriginObservation.empty configuration).completedViews =
      ($ᵗ (pattern.selected → FewTimeView) :
        ProbComp (pattern.selected → FewTimeView)) := by
  classical
  have hcomplete : (OriginObservation.empty configuration).completeViews = id := by
    funext fallback selected
    simp [OriginObservation.completeViews, OriginObservation.empty]
  rw [OriginObservation.completedViews, hcomplete, id_map]

theorem OriginMonitorState.potential_initial {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources)
    (cache : QueryCache HashSpec)
    (event : (pattern.selected → FewTimeView) → Prop) :
    (OriginMonitorState.initial configuration cache).potential event =
      ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ ^ configuration.prehit.card *
        Pr[event | ($ᵗ (pattern.selected → FewTimeView) :
          ProbComp (pattern.selected → FewTimeView))] := by
  classical
  rw [OriginMonitorState.potential]
  rw [if_pos (show (OriginMonitorState.initial configuration cache).valid = true from rfl),
    OriginMonitorState.pendingSources_initial,
    OriginMonitorState.pendingReuses_initial, pow_zero, mul_one]
  rw [OriginMonitorState.completionMass]
  change ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ ^ configuration.prehit.card *
      Pr[event | (OriginObservation.empty configuration).completedViews] = _
  rw [OriginObservation.completedViews_empty]

noncomputable def OriginMonitorState.recordSourceState {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) (selected : ↑configuration.prehit)
    (input : HashInput) (view : FewTimeView) : OriginMonitorState configuration :=
  { state with
    observation := state.observation.recordSource selected input view
    directOrdinal := state.directOrdinal + 1 }

noncomputable def OriginMonitorState.recordFreshState {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) (selected : pattern.selected)
    (view : FewTimeView) : OriginMonitorState configuration :=
  { state with
    observation := state.observation.recordFresh selected view
    signerOrdinal := state.signerOrdinal + 1 }

def OriginMonitorState.advanceSigner {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) : OriginMonitorState configuration :=
  { state with signerOrdinal := state.signerOrdinal + 1 }

theorem OriginMonitorState.pendingSources_recordSourceState {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) (selected : ↑configuration.prehit)
    (input : HashInput) (view : FewTimeView) :
    (state.recordSourceState selected input view).pendingSources =
      state.pendingSources.erase selected := by
  classical
  ext other
  by_cases hother : other = selected
  · subst other
    simp [OriginMonitorState.pendingSources, OriginMonitorState.recordSourceState,
      OriginObservation.recordSource]
  · simp [OriginMonitorState.pendingSources, OriginMonitorState.recordSourceState,
      OriginObservation.recordSource, hother]

theorem OriginMonitorState.pendingSources_recordSourceState_card_add_one
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) (selected : ↑configuration.prehit)
    (input : HashInput) (view : FewTimeView)
    (hnotSeen : selected ∉ state.observation.seenSources) :
    (state.recordSourceState selected input view).pendingSources.card + 1 =
      state.pendingSources.card := by
  classical
  rw [state.pendingSources_recordSourceState selected input view]
  apply Finset.card_erase_add_one
  simp [OriginMonitorState.pendingSources, hnotSeen]

theorem OriginMonitorState.pendingReuses_recordSourceState {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) (selected : ↑configuration.prehit)
    (input : HashInput) (view : FewTimeView)
    (hpending : state.signerOrdinal ≤ selected.1.1.val) :
    (state.recordSourceState selected input view).pendingReuses =
      insert selected state.pendingReuses := by
  classical
  ext other
  by_cases hother : other = selected
  · subst other
    simp [OriginMonitorState.pendingReuses, OriginMonitorState.recordSourceState,
      OriginObservation.recordSource, hpending]
  · simp [OriginMonitorState.pendingReuses, OriginMonitorState.recordSourceState,
      OriginObservation.recordSource, hother]

theorem OriginMonitorState.pendingReuses_recordSourceState_card
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) (selected : ↑configuration.prehit)
    (input : HashInput) (view : FewTimeView)
    (hnotSeen : selected ∉ state.observation.seenSources)
    (hpending : state.signerOrdinal ≤ selected.1.1.val) :
    (state.recordSourceState selected input view).pendingReuses.card =
      state.pendingReuses.card + 1 := by
  classical
  rw [state.pendingReuses_recordSourceState selected input view hpending,
    Finset.card_insert_of_notMem]
  simp [OriginMonitorState.pendingReuses, hnotSeen]

theorem OriginMonitorState.pendingSources_recordFreshState {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) (selected : pattern.selected)
    (view : FewTimeView) :
    (state.recordFreshState selected view).pendingSources = state.pendingSources := by
  rfl

theorem OriginMonitorState.pendingReuses_recordFreshState {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) (selected : pattern.selected)
    (view : FewTimeView) (hordinal : selected.1.val = state.signerOrdinal)
    (hnotPrehit : selected ∉ configuration.prehit) :
    (state.recordFreshState selected view).pendingReuses = state.pendingReuses := by
  classical
  ext candidate
  simp only [OriginMonitorState.pendingReuses, OriginMonitorState.recordFreshState,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hseen, hle⟩
    exact ⟨hseen, Nat.le_trans (Nat.le_succ _) hle⟩
  · rintro ⟨hseen, hle⟩
    refine ⟨hseen, ?_⟩
    by_contra hnot
    have hcandidate : candidate.1.1.val = state.signerOrdinal := by omega
    have heq : candidate.1 = selected := by
      apply Subtype.ext
      apply Fin.ext
      exact hcandidate.trans hordinal.symm
    exact hnotPrehit (heq ▸ candidate.2)

theorem OriginMonitorState.pendingSources_advanceSigner {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) :
    state.advanceSigner.pendingSources = state.pendingSources := by
  rfl

theorem OriginMonitorState.pendingReuses_advanceSigner {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) (selected : ↑configuration.prehit)
    (hseen : selected ∈ state.observation.seenSources)
    (hordinal : selected.1.1.val = state.signerOrdinal) :
    state.advanceSigner.pendingReuses = state.pendingReuses.erase selected := by
  classical
  ext candidate
  by_cases hcandidate : candidate = selected
  · subst candidate
    simp [OriginMonitorState.pendingReuses, OriginMonitorState.advanceSigner, hseen,
      hordinal]
  · simp only [OriginMonitorState.pendingReuses, OriginMonitorState.advanceSigner,
      Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · rintro ⟨hcandidateSeen, hle⟩
      exact ⟨hcandidate, hcandidateSeen, Nat.le_trans (Nat.le_succ _) hle⟩
    · rintro ⟨_, hcandidateSeen, hle⟩
      refine ⟨hcandidateSeen, ?_⟩
      by_contra hnot
      have hvalue : candidate.1.1.val = state.signerOrdinal := by omega
      have heq : candidate = selected := by
        apply Subtype.ext
        apply Subtype.ext
        apply Fin.ext
        exact hvalue.trans hordinal.symm
      exact hcandidate heq

theorem OriginMonitorState.pendingReuses_advanceSigner_card_add_one
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) (selected : ↑configuration.prehit)
    (hseen : selected ∈ state.observation.seenSources)
    (hordinal : selected.1.1.val = state.signerOrdinal) :
    state.advanceSigner.pendingReuses.card + 1 = state.pendingReuses.card := by
  classical
  rw [state.pendingReuses_advanceSigner selected hseen hordinal]
  apply Finset.card_erase_add_one
  simp [OriginMonitorState.pendingReuses, hseen, hordinal]

theorem source_reuse_weighted_sum
    {Index : Type} [Fintype Index] (probability mass : Index → ℝ≥0∞)
    (sourceCount reuseCount : Nat) (totalMass : ℝ≥0∞)
    (hmass : (∑ index, probability index * mass index) = totalMass) :
    ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ *
        ∑ index, probability index *
          (((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ ^ sourceCount *
            ((2 ^ 117 : Nat) : ℝ≥0∞)⁻¹ ^ (reuseCount + 1) * mass index) =
      ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ ^ (sourceCount + 1) *
        ((2 ^ 117 : Nat) : ℝ≥0∞)⁻¹ ^ reuseCount * totalMass := by
  rw [pow_succ ((2 ^ 117 : Nat) : ℝ≥0∞)⁻¹]
  have hfactor :
      (∑ index, probability index *
          (((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ ^ sourceCount *
            (((2 ^ 117 : Nat) : ℝ≥0∞)⁻¹ ^ reuseCount *
              ((2 ^ 117 : Nat) : ℝ≥0∞)⁻¹) * mass index)) =
        (((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ ^ sourceCount *
          ((2 ^ 117 : Nat) : ℝ≥0∞)⁻¹ ^ reuseCount *
            ((2 ^ 117 : Nat) : ℝ≥0∞)⁻¹) *
          ∑ index, probability index * mass index := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index _
    ring
  rw [hfactor, hmass, pow_succ _ sourceCount]
  have hweight :
      ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ *
          ((2 ^ 117 : Nat) : ℝ≥0∞)⁻¹ =
        ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ := by
    rw [mul_comm, prehit_race_source_weight]
  rw [← hweight]
  ring

theorem uniform_weighted_sum
    {Index : Type} [Fintype Index] (probability mass : Index → ℝ≥0∞)
    (factor totalMass : ℝ≥0∞)
    (hmass : (∑ index, probability index * mass index) = totalMass) :
    (∑ index, probability index * (factor * mass index)) = factor * totalMass := by
  calc
    (∑ index, probability index * (factor * mass index)) =
        ∑ index, factor * (probability index * mass index) := by
      apply Finset.sum_congr rfl
      intro index _
      ring
    _ = factor * ∑ index, probability index * mass index := by rw [Finset.mul_sum]
    _ = _ := by rw [hmass]

theorem OriginMonitorState.sum_uniform_potential_recordSourceState
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
            (state.recordSourceState selected input view).potential event =
      state.potential event := by
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
  simp_rw [OriginMonitorState.potential, if_pos hvalid]
  simp_rw [if_pos (hnextValid _), OriginMonitorState.completionMass,
    hsourceView, hreusesView]
  rw [← hsource]
  apply source_reuse_weighted_sum
  exact state.observation.sum_uniform_prob_completedViews_recordSource
    selected input hnotView event

theorem OriginMonitorState.sum_uniform_potential_recordFreshState
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
          (state.recordFreshState selected view).potential event) =
      state.potential event := by
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
  simp_rw [OriginMonitorState.potential, if_pos hvalid]
  simp_rw [if_pos (hnextValid _), OriginMonitorState.completionMass, hsources, hreuses]
  apply uniform_weighted_sum
  exact state.observation.sum_uniform_prob_completedViews_recordFresh selected hnotView event

theorem OriginMonitorState.reuseWeight_mul_potential_advanceSigner
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) (selected : ↑configuration.prehit)
    (event : (pattern.selected → FewTimeView) → Prop)
    (hvalid : state.valid = true)
    (hseen : selected ∈ state.observation.seenSources)
    (hordinal : selected.1.1.val = state.signerOrdinal) :
    ((2 ^ 117 : Nat) : ℝ≥0∞)⁻¹ * state.advanceSigner.potential event =
      state.potential event := by
  classical
  have hsources : state.advanceSigner.pendingSources.card = state.pendingSources.card :=
    congrArg Finset.card state.pendingSources_advanceSigner
  have hreuses := state.pendingReuses_advanceSigner_card_add_one selected hseen hordinal
  have hnextValid : state.advanceSigner.valid = true := hvalid
  rw [OriginMonitorState.potential, if_pos hnextValid,
    OriginMonitorState.potential, if_pos hvalid,
    hsources, OriginMonitorState.completionMass, OriginMonitorState.completionMass]
  change ((2 ^ 117 : Nat) : ℝ≥0∞)⁻¹ *
      (((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ ^ state.pendingSources.card *
        ((2 ^ 117 : Nat) : ℝ≥0∞)⁻¹ ^ state.advanceSigner.pendingReuses.card *
          Pr[event | state.observation.completedViews]) = _
  rw [← hreuses, pow_succ _ state.advanceSigner.pendingReuses.card]
  ring

def OriginMonitorState.ScheduleCoherent {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) : Prop :=
  state.valid = true →
    (∀ selected : ↑configuration.prehit,
      selected ∈ state.observation.seenSources ↔
        (configuration.source.1 selected).val < state.directOrdinal) ∧
    (∀ selected : pattern.selected,
      selected ∈ state.observation.seenViews ↔
        selected.1.val < state.signerOrdinal ∨
          ∃ hprehit : selected ∈ configuration.prehit,
            (configuration.source.1 ⟨selected, hprehit⟩).val < state.directOrdinal) ∧
    ∀ selected : pattern.selected, ∀ hprehit : selected ∈ configuration.prehit,
      selected.1.val < state.signerOrdinal →
        (configuration.source.1 ⟨selected, hprehit⟩).val < state.directOrdinal

theorem OriginMonitorState.scheduleCoherent_initial {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources)
    (cache : QueryCache HashSpec) :
    (OriginMonitorState.initial configuration cache).ScheduleCoherent := by
  classical
  intro _
  constructor
  · intro selected
    simp [OriginMonitorState.initial, OriginObservation.empty]
  constructor
  · intro selected
    simp [OriginMonitorState.initial, OriginObservation.empty]
  · intro selected hprehit hlt
    change selected.1.val < 0 at hlt
    omega

theorem OriginMonitorState.sourceAt_not_seenSource {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) (selected : ↑configuration.prehit)
    (hcoherent : state.ScheduleCoherent) (hvalid : state.valid = true)
    (hsource : configuration.sourceAt? state.directOrdinal = some selected) :
    selected ∉ state.observation.seenSources := by
  intro hseen
  have hlt := (hcoherent hvalid).1 selected |>.mp hseen
  have heq := (configuration.sourceAt?_eq_some_iff state.directOrdinal selected).mp hsource
  omega

theorem OriginMonitorState.sourceAt_signer_pending {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) (selected : ↑configuration.prehit)
    (hcoherent : state.ScheduleCoherent) (hvalid : state.valid = true)
    (hsource : configuration.sourceAt? state.directOrdinal = some selected) :
    state.signerOrdinal ≤ selected.1.1.val := by
  by_contra hnot
  have hsigned : selected.1.1.val < state.signerOrdinal := by omega
  have hlt := (hcoherent hvalid).2.2 selected.1 selected.2 hsigned
  have hsame : (⟨selected.1, selected.2⟩ : ↑configuration.prehit) = selected := by
    apply Subtype.ext
    rfl
  rw [hsame] at hlt
  have heq := (configuration.sourceAt?_eq_some_iff state.directOrdinal selected).mp hsource
  omega

theorem OriginMonitorState.sourceAt_not_seenView {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) (selected : ↑configuration.prehit)
    (hcoherent : state.ScheduleCoherent) (hvalid : state.valid = true)
    (hsource : configuration.sourceAt? state.directOrdinal = some selected) :
    selected.1 ∉ state.observation.seenViews := by
  intro hseen
  rcases (hcoherent hvalid).2.1 selected.1 |>.mp hseen with hsigned | ⟨hprehit, hlt⟩
  · exact (Nat.not_lt_of_ge
      (state.sourceAt_signer_pending selected hcoherent hvalid hsource)) hsigned
  · have heqPrehit : (⟨selected.1, hprehit⟩ : ↑configuration.prehit) = selected := by
      apply Subtype.ext
      rfl
    rw [heqPrehit] at hlt
    have heq := (configuration.sourceAt?_eq_some_iff state.directOrdinal selected).mp hsource
    omega

theorem OriginMonitorState.selectedAt_fresh_not_seenView {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) (selected : pattern.selected)
    (hcoherent : state.ScheduleCoherent) (hvalid : state.valid = true)
    (hselected : pattern.selectedAt? state.signerOrdinal = some selected)
    (hnotPrehit : selected ∉ configuration.prehit) :
    selected ∉ state.observation.seenViews := by
  intro hseen
  rcases (hcoherent hvalid).2.1 selected |>.mp hseen with hsigned | ⟨hprehit, _⟩
  · have heq := (pattern.selectedAt?_eq_some_iff state.signerOrdinal selected).mp hselected
    omega
  · exact hnotPrehit hprehit

theorem OriginMonitorState.selectedAt_prehit_seenView {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) (selected : pattern.selected)
    (hcoherent : state.ScheduleCoherent) (hvalid : state.valid = true)
    (hprehit : selected ∈ configuration.prehit)
    (hseen : (⟨selected, hprehit⟩ : ↑configuration.prehit) ∈
      state.observation.seenSources) :
    selected ∈ state.observation.seenViews := by
  apply (hcoherent hvalid).2.1 selected |>.mpr
  exact Or.inr ⟨hprehit, (hcoherent hvalid).1 ⟨selected, hprehit⟩ |>.mp hseen⟩

end Concrete

end SphincsSecurity

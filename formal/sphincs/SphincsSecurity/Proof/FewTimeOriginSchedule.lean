import SphincsSecurity.Proof.FewTimeOriginPadding

/-!
# Ordinal schedule for a padded origin configuration

The adaptive recursion addresses direct queries and signer invocations by their chronological
ordinals. Injectivity of the selected signer positions and prehit source assignment makes the
configured obligation at either kind of ordinal unique.
-/

namespace SphincsSecurity.Concrete

noncomputable def OriginConfiguration.sourceAt? {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (ordinal : Nat) :
    Option ↑configuration.prehit := by
  classical
  exact if h : ∃ selected, (configuration.source.1 selected).val = ordinal then
      some (Classical.choose h)
    else none

theorem OriginConfiguration.sourceAt?_eq_some_iff {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (ordinal : Nat)
    (selected : ↑configuration.prehit) :
    configuration.sourceAt? ordinal = some selected ↔
      (configuration.source.1 selected).val = ordinal := by
  classical
  constructor
  · intro hlookup
    by_cases hexists : ∃ candidate, (configuration.source.1 candidate).val = ordinal
    · rw [OriginConfiguration.sourceAt?, dif_pos hexists] at hlookup
      have hselected : Classical.choose hexists = selected := Option.some.inj hlookup
      rw [← hselected]
      exact Classical.choose_spec hexists
    · simp [OriginConfiguration.sourceAt?, hexists] at hlookup
  · intro hsource
    have hexists : ∃ candidate, (configuration.source.1 candidate).val = ordinal :=
      ⟨selected, hsource⟩
    rw [OriginConfiguration.sourceAt?, dif_pos hexists]
    congr 1
    apply configuration.source.2
    apply Fin.ext
    exact (Classical.choose_spec hexists).trans hsource.symm

noncomputable def FewTimePattern.selectedAt? {signatures distinct : Nat}
    (pattern : FewTimePattern signatures distinct) (ordinal : Nat) :
    Option pattern.selected := by
  classical
  exact if h : ∃ selected : pattern.selected, selected.1.val = ordinal then
      some (Classical.choose h)
    else none

theorem FewTimePattern.selectedAt?_eq_some_iff {signatures distinct : Nat}
    (pattern : FewTimePattern signatures distinct) (ordinal : Nat)
    (selected : pattern.selected) :
    pattern.selectedAt? ordinal = some selected ↔ selected.1.val = ordinal := by
  classical
  constructor
  · intro hlookup
    by_cases hexists : ∃ candidate : pattern.selected, candidate.1.val = ordinal
    · rw [FewTimePattern.selectedAt?, dif_pos hexists] at hlookup
      have hselected : Classical.choose hexists = selected := Option.some.inj hlookup
      rw [← hselected]
      exact Classical.choose_spec hexists
    · simp [FewTimePattern.selectedAt?, hexists] at hlookup
  · intro hposition
    have hexists : ∃ candidate : pattern.selected, candidate.1.val = ordinal :=
      ⟨selected, hposition⟩
    rw [FewTimePattern.selectedAt?, dif_pos hexists]
    congr 1
    apply Subtype.ext
    apply Fin.ext
    exact (Classical.choose_spec hexists).trans hposition.symm

structure OriginObservation {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) where
  views : pattern.selected → FewTimeView
  sourceInputs : ↑configuration.prehit → HashInput
  seenViews : Finset pattern.selected
  seenSources : Finset ↑configuration.prehit

noncomputable def OriginObservation.empty {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) : OriginObservation configuration := by
  classical
  exact ⟨fun _ => default, fun _ => default, ∅, ∅⟩

noncomputable def OriginObservation.recordSource {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (observation : OriginObservation configuration)
    (selected : ↑configuration.prehit) (input : HashInput) (view : FewTimeView) :
    OriginObservation configuration := by
  classical
  exact ⟨Function.update observation.views selected.1 view,
    Function.update observation.sourceInputs selected input,
    insert selected.1 observation.seenViews, insert selected observation.seenSources⟩

noncomputable def OriginObservation.recordFresh {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (observation : OriginObservation configuration)
    (selected : pattern.selected) (view : FewTimeView) : OriginObservation configuration := by
  classical
  exact ⟨Function.update observation.views selected view, observation.sourceInputs,
    insert selected observation.seenViews, observation.seenSources⟩

theorem OriginObservation.recordSource_view {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (observation : OriginObservation configuration)
    (selected : ↑configuration.prehit) (input : HashInput) (view : FewTimeView) :
    (observation.recordSource selected input view).views selected.1 = view := by
  classical
  simp [OriginObservation.recordSource]

theorem OriginObservation.recordSource_input {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (observation : OriginObservation configuration)
    (selected : ↑configuration.prehit) (input : HashInput) (view : FewTimeView) :
    (observation.recordSource selected input view).sourceInputs selected = input := by
  classical
  simp [OriginObservation.recordSource]

theorem OriginObservation.recordSource_view_of_ne {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (observation : OriginObservation configuration)
    (selected : ↑configuration.prehit) (input : HashInput) (view : FewTimeView)
    (other : pattern.selected) (hne : other ≠ selected.1) :
    (observation.recordSource selected input view).views other = observation.views other := by
  classical
  simp [OriginObservation.recordSource, hne]

theorem OriginObservation.recordSource_input_of_ne {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (observation : OriginObservation configuration)
    (selected : ↑configuration.prehit) (input : HashInput) (view : FewTimeView)
    (other : ↑configuration.prehit) (hne : other ≠ selected) :
    (observation.recordSource selected input view).sourceInputs other =
      observation.sourceInputs other := by
  classical
  simp [OriginObservation.recordSource, hne]

theorem OriginObservation.recordSource_seen {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (observation : OriginObservation configuration)
    (selected : ↑configuration.prehit) (input : HashInput) (view : FewTimeView) :
    selected.1 ∈ (observation.recordSource selected input view).seenViews ∧
      selected ∈ (observation.recordSource selected input view).seenSources := by
  classical
  simp [OriginObservation.recordSource]

theorem OriginObservation.recordFresh_view {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (observation : OriginObservation configuration)
    (selected : pattern.selected) (view : FewTimeView) :
    (observation.recordFresh selected view).views selected = view := by
  classical
  simp [OriginObservation.recordFresh]

theorem OriginObservation.recordFresh_view_of_ne {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (observation : OriginObservation configuration)
    (selected other : pattern.selected) (view : FewTimeView) (hne : other ≠ selected) :
    (observation.recordFresh selected view).views other = observation.views other := by
  classical
  simp [OriginObservation.recordFresh, hne]

theorem OriginObservation.recordFresh_seen {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (observation : OriginObservation configuration)
    (selected : pattern.selected) (view : FewTimeView) :
    selected ∈ (observation.recordFresh selected view).seenViews := by
  classical
  simp [OriginObservation.recordFresh]

end SphincsSecurity.Concrete

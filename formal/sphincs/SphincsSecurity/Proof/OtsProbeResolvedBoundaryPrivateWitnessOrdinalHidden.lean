import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRiskLift

/-!
# Hidden selected-candidate risk

A recorded plan may name a coordinate that is already published. Such a candidate cannot explain
a private witness, but the ungated candidate observer can still return true there. The hidden
observer removes that harmless over-approximation. `NoAuxiliaryPrivateValues` is the invariant of
the delayed selection schedule needed to make every hidden selected candidate fresh.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

def NoAuxiliaryPrivateValues (context : DeferredContext) : Prop :=
  ∀ position, context.state.values (.position position) = none →
    context.values position = none

def Probe.HasStructuralParent (candidate : Probe) : Prop :=
  match candidate.coordinate with
  | .chainStart _ _ _ _ => True
  | .position position => ∃ parent, Position.parentOf position = some parent

def CandidatePositionsFresh (context : DeferredContext) : Prop :=
  ∀ position parent, Position.parentOf position = some parent →
    Coordinate.position position ∉ context.state.revealed →
    context.state.values (.position position) = none ∧
      context.values position = none

theorem candidatePositionsFresh_empty :
    CandidatePositionsFresh
      { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
        values := emptyDeferredStructuralValues } := by
  intro position parent hparent hhidden
  simp [LazyRevealProbe.State.empty, emptyDeferredStructuralValues]

theorem noAuxiliaryPrivateValues_empty :
    NoAuxiliaryPrivateValues
      { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
        values := emptyDeferredStructuralValues } := by
  intro position _hstate
  simp [emptyDeferredStructuralValues]

theorem noAuxiliaryPrivateValues_directDeferredContext
    (state : LazyRevealProbe.State Coordinate) :
    NoAuxiliaryPrivateValues (directDeferredContext state) := by
  intro position hstate
  simpa [directDeferredContext, directDeferredValues] using hstate

theorem NoAuxiliaryPrivateValues.ensure
    {context : DeferredContext} (hprivate : NoAuxiliaryPrivateValues context)
    (coordinate : Coordinate) :
    NoAuxiliaryPrivateValues
      { context with state := context.state.ensure coordinate } := by
  intro position hstate
  exact hprivate position hstate

theorem NoAuxiliaryPrivateValues.addPending
    {context : DeferredContext} (hprivate : NoAuxiliaryPrivateValues context)
    (coordinate : Coordinate) (candidate : Digest) :
    NoAuxiliaryPrivateValues
      { context with state := context.state.addPending coordinate candidate } := by
  intro position hstate
  exact hprivate position hstate

theorem NoAuxiliaryPrivateValues.clearPending
    {context : DeferredContext} (hprivate : NoAuxiliaryPrivateValues context)
    (coordinate : Coordinate) :
    NoAuxiliaryPrivateValues
      { context with state := context.state.clearPending coordinate } := by
  intro position hstate
  exact hprivate position hstate

theorem NoAuxiliaryPrivateValues.publish
    {context : DeferredContext} (hprivate : NoAuxiliaryPrivateValues context)
    (coordinate : Coordinate) :
    NoAuxiliaryPrivateValues
      { context with state := context.state.publish coordinate } := by
  intro position hstate
  exact hprivate position hstate

theorem NoAuxiliaryPrivateValues.materialize_install
    {context : DeferredContext} (hprivate : NoAuxiliaryPrivateValues context)
    (coordinate : Coordinate) (position : Position) (output : HashOutput)
    (hcoordinate : coordinate = .position position) :
    NoAuxiliaryPrivateValues
      { state := context.state.materialize coordinate output
        values := context.values.install position output } := by
  subst coordinate
  intro other hstate
  by_cases heq : other = position
  · subst other
    simp [LazyRevealProbe.State.materialize] at hstate
  · change (context.values.install position output) other = none
    unfold DeferredStructuralValues.install
    rw [Function.update_of_ne heq]
    apply hprivate other
    have hcoordinate : Coordinate.position other ≠ .position position := by
      simpa using heq
    simpa [LazyRevealProbe.State.materialize, Function.update_of_ne hcoordinate] using hstate

noncomputable def hiddenPrivateCandidateFire
    (candidate : Probe) (context : DeferredContext) : ProbComp Bool :=
  if candidate.coordinate ∈ context.state.revealed then
    pure false
  else
    privateCandidateFire candidate context

theorem hiddenPrivateCandidateFire_of_not_revealed
    (candidate : Probe) (context : DeferredContext)
    (hhidden : candidate.coordinate ∉ context.state.revealed) :
    hiddenPrivateCandidateFire candidate context =
      privateCandidateFire candidate context := by
  simp [hiddenPrivateCandidateFire, hhidden]

theorem hiddenPrivateCandidateFire_of_revealed
    (candidate : Probe) (context : DeferredContext)
    (hrevealed : candidate.coordinate ∈ context.state.revealed) :
    hiddenPrivateCandidateFire candidate context = pure false := by
  simp [hiddenPrivateCandidateFire, hrevealed]

theorem probEvent_hiddenPrivateCandidateFire_le
    (candidate : Probe) (context : DeferredContext)
    (hvalid : context.state.Valid)
    (hprivate : NoAuxiliaryPrivateValues context) :
    Pr[= true | hiddenPrivateCandidateFire candidate context] ≤
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  by_cases hrevealed : candidate.coordinate ∈ context.state.revealed
  · simp [hiddenPrivateCandidateFire, hrevealed]
  · rw [hiddenPrivateCandidateFire_of_not_revealed candidate context hrevealed]
    apply probEvent_privateCandidateFire_le_of_fresh
    · intro position hcoordinate
      have hhidden : Coordinate.position position ∉ context.state.revealed := by
        rwa [← hcoordinate]
      exact hvalid.not_revealed_value_none hhidden
    · intro position hcoordinate
      have hhidden : Coordinate.position position ∉ context.state.revealed := by
        rwa [← hcoordinate]
      exact hprivate position (hvalid.not_revealed_value_none hhidden)

theorem probEvent_hiddenPrivateCandidateFire_empty_le (candidate : Probe) :
    Pr[= true | hiddenPrivateCandidateFire candidate
      { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
        values := emptyDeferredStructuralValues }] ≤
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  exact probEvent_hiddenPrivateCandidateFire_le candidate _
    LazyRevealProbe.State.valid_empty noAuxiliaryPrivateValues_empty

theorem probEvent_hiddenPrivateCandidateFire_le_of_candidatePositionsFresh
    (candidate : Probe) (context : DeferredContext)
    (hparent : candidate.HasStructuralParent)
    (hfresh : CandidatePositionsFresh context) :
    Pr[= true | hiddenPrivateCandidateFire candidate context] ≤
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  by_cases hrevealed : candidate.coordinate ∈ context.state.revealed
  · simp [hiddenPrivateCandidateFire, hrevealed]
  · rw [hiddenPrivateCandidateFire_of_not_revealed candidate context hrevealed]
    cases hcoordinate : candidate.coordinate with
    | chainStart lay tree leafIdx chainIdx =>
        simp [privateCandidateFire, hcoordinate]
    | position position =>
        simp only [Probe.HasStructuralParent, hcoordinate] at hparent
        obtain ⟨parent, hpositionParent⟩ := hparent
        have hpositionHidden : Coordinate.position position ∉ context.state.revealed := by
          simpa [hcoordinate] using hrevealed
        have hpositionFresh := hfresh position parent hpositionParent hpositionHidden
        exact probEvent_privateCandidateFire_le_of_fresh candidate context
          (by
            intro other hother
            have : position = other := by
              simpa [hcoordinate] using hother
            subst other
            exact hpositionFresh.1)
          (by
            intro other hother
            have : position = other := by
              simpa [hcoordinate] using hother
            subst other
            exact hpositionFresh.2)

theorem Probe.hasStructuralParent_of_matchesInput
    (candidate : Probe) (parameter : PublicParameter) (input : HashInput)
    (hmatch : candidate.MatchesInput parameter input) :
    candidate.HasStructuralParent := by
  rcases candidate with ⟨coordinate, digest⟩
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx => trivial
  | position position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          change ∃ parent, Position.parentOf (.chain lay tree leafIdx chainIdx step) = some parent
          by_cases hnext : step.val + 1 < chainLength - 1
          · refine ⟨.chain lay tree leafIdx chainIdx ⟨step.val + 1, hnext⟩, ?_⟩
            rw [Position.parentOf, dif_pos hnext]
          · refine ⟨.leaf lay tree leafIdx, ?_⟩
            rw [Position.parentOf, dif_neg hnext]
      | leaf lay tree leafIdx => simp [Probe.MatchesInput] at hmatch
      | node lay tree level nodeIdx => simp [Probe.MatchesInput] at hmatch
      | ftsLeaf index tree leafIdx => simp [Probe.MatchesInput] at hmatch
      | ftsNode index tree level nodeIdx => simp [Probe.MatchesInput] at hmatch
      | ftsRoots index => simp [Probe.MatchesInput] at hmatch

theorem Probe.hasStructuralParent_of_decodeProbe?_eq_some
    (candidate : Probe) (parameter : PublicParameter) (input : HashInput)
    (hdecode : decodeProbe? parameter input = some candidate) :
    candidate.HasStructuralParent := by
  exact candidate.hasStructuralParent_of_matchesInput parameter input
    ((decodeProbe?_eq_some_iff parameter input candidate).mp hdecode)

theorem firstMissingInputCoordinatePlan_some_mem
    (state : LazyRevealProbe.State Coordinate) (input : HashInput) :
    ∀ slot coordinates candidate,
      firstMissingInputCoordinatePlan state input slot coordinates = some candidate →
      candidate.coordinate ∈ coordinates := by
  intro slot coordinates
  induction coordinates generalizing slot with
  | nil => simp [firstMissingInputCoordinatePlan]
  | cons coordinate remaining ih =>
      intro candidate hplan
      rw [firstMissingInputCoordinatePlan] at hplan
      cases hvalue : state.values coordinate with
      | none =>
          simp only [hvalue] at hplan
          have hcand : candidate = ⟨coordinate, slotDigest slot input⟩ :=
            Option.some.inj hplan.symm
          subst candidate
          simp
      | some output =>
          simp only [hvalue] at hplan
          exact List.mem_cons_of_mem coordinate (ih (slot + 1) candidate hplan)

theorem hasStructuralParent_of_mem_children_coordinates
    (parent : Position) (candidate : Probe)
    (hmem : candidate.coordinate ∈ parent.children.map Coordinate.position) :
    candidate.HasStructuralParent := by
  rw [List.mem_map] at hmem
  obtain ⟨position, hposition, hcoordinate⟩ := hmem
  have hparent : Position.parentOf position = some parent :=
    Position.mem_children_iff.mp hposition
  unfold Probe.HasStructuralParent
  rw [← hcoordinate]
  exact ⟨parent, hparent⟩

theorem leafInputProbePlan_hasStructuralParent
    (state : LazyRevealProbe.State Coordinate)
    (input : HashInput) (candidate planned : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (hbase : candidate.HasStructuralParent)
    (hplan : leafInputProbePlan state input candidate lay tree leafIdx = some planned) :
    planned.HasStructuralParent := by
  unfold leafInputProbePlan at hplan
  cases hvalue : state.values candidate.coordinate with
  | none =>
      simp only [hvalue] at hplan
      exact Option.some.inj hplan.symm ▸ hbase
  | some output =>
      simp only [hvalue] at hplan
      exact hasStructuralParent_of_mem_children_coordinates (.leaf lay tree leafIdx) planned
        (firstMissingInputCoordinatePlan_some_mem state input 0
          ((Position.leaf lay tree leafIdx).children.map Coordinate.position) planned hplan)

end SphincsSecurity.Concrete.OtsProbeSimulation

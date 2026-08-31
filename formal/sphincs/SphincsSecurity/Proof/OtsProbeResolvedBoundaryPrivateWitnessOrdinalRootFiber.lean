import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootAdaptive

/-!
# Layer-root ordinal fibers

The root selected by one chronological candidate ordinal is dynamic. This module classifies a
retained witness by that root position so a weighted fiber argument can fix the target without
paying for every possible structural position.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable

abbrev RootOutputHigh := BitVec (hashOutputBits - digestBits)

noncomputable def rootOutputOfParts (root : Digest) (high : RootOutputHigh) : HashOutput :=
  (splitHashOutputEquiv digestBits (by decide)).symm (root, high)

@[simp] theorem truncateHash_rootOutputOfParts (root : Digest) (high : RootOutputHigh) :
    truncateHash (rootOutputOfParts root high) = root := by
  change (splitHashOutput digestBits
    ((splitHashOutputEquiv digestBits (by decide)).symm (root, high))).1 = root
  rw [show splitHashOutput digestBits = splitHashOutputEquiv digestBits (by decide) from rfl,
    Equiv.apply_symm_apply]

theorem evalDist_sample_rootOutputOfParts :
    evalDist (do
      let root ← ($ᵗ Digest : ProbComp Digest)
      let high ← ($ᵗ RootOutputHigh : ProbComp RootOutputHigh)
      pure (rootOutputOfParts root high)) =
      evalDist LazyRevealProbe.sampleHashOutput := by
  let split := splitHashOutputEquiv digestBits (by decide)
  let pairSample :=
    ($ᵗ (Digest × RootOutputHigh) : ProbComp (Digest × RootOutputHigh))
  have hpair : evalDist (do
      let root ← ($ᵗ Digest : ProbComp Digest)
      let high ← ($ᵗ RootOutputHigh : ProbComp RootOutputHigh)
      pure (root, high)) = evalDist pairSample := by
    exact evalDist_independent_uniform_pair
  have hleft : (do
      let root ← ($ᵗ Digest : ProbComp Digest)
      let high ← ($ᵗ RootOutputHigh : ProbComp RootOutputHigh)
      pure (rootOutputOfParts root high)) =
      split.symm <$> (do
        let root ← ($ᵗ Digest : ProbComp Digest)
        let high ← ($ᵗ RootOutputHigh : ProbComp RootOutputHigh)
        pure (root, high)) := by
    simp [rootOutputOfParts, split, map_eq_bind_pure_comp, bind_assoc]
  calc
    _ = evalDist (split.symm <$> pairSample) := by
      rw [hleft, evalDist_map, hpair, ← evalDist_map]
    _ = evalDist ($ᵗ HashOutput : ProbComp HashOutput) :=
      evalDist_map_bijective_uniform_cross _ split.symm split.symm.bijective
    _ = _ := rfl

noncomputable def freshRootResolution (target : Position) (context : DeferredContext)
    (output : HashOutput) : Option DeferredResolution :=
  if context.state.hitAt (.position target) output then none
  else some (DeferredResolution.mk
    { state := context.state.clearPending (.position target)
      values := context.values.install target output }
    output)

theorem resolveDeferredPositionValue_fresh_eq_bind_rootResolution
    (target : Position) (context : DeferredContext)
    (hstate : context.state.values (.position target) = none)
    (hvalue : context.values target = none) :
    resolveDeferredPositionValue target context = (do
      let output ← LazyRevealProbe.sampleHashOutput
      pure (freshRootResolution target context output)) := by
  rw [resolveDeferredPositionValue_fresh target context hstate hvalue]
  apply bind_congr
  intro output
  unfold freshRootResolution
  by_cases hhit : context.state.hitAt (.position target) output <;> simp [hhit]

theorem evalDist_resolveDeferredPositionValue_fresh_root_parts
    (target : Position) (context : DeferredContext)
    (hstate : context.state.values (.position target) = none)
    (hvalue : context.values target = none) :
    evalDist (resolveDeferredPositionValue target context) = evalDist (do
      let root ← ($ᵗ Digest : ProbComp Digest)
      let high ← ($ᵗ RootOutputHigh : ProbComp RootOutputHigh)
      pure (freshRootResolution target context (rootOutputOfParts root high))) := by
  rw [resolveDeferredPositionValue_fresh_eq_bind_rootResolution target context hstate hvalue]
  let parts : ProbComp HashOutput := do
    let root ← ($ᵗ Digest : ProbComp Digest)
    let high ← ($ᵗ RootOutputHigh : ProbComp RootOutputHigh)
    pure (rootOutputOfParts root high)
  calc
    evalDist (LazyRevealProbe.sampleHashOutput >>=
        fun output => pure (freshRootResolution target context output)) =
      evalDist (parts >>= fun output =>
        pure (freshRootResolution target context output)) := by
        rw [evalDist_bind, evalDist_bind, evalDist_sample_rootOutputOfParts]
    _ = _ := by simp [parts]

theorem storedLayerRoot_materializeResolvedPosition
    (context : DeferredContext) (target : Position) (result : DeferredResolution) :
    StoredLayerRoot (materializeResolvedPosition context target result).state target
      (truncateHash result.output) := by
  refine ⟨result.output, ?_, rfl⟩
  simp [materializeResolvedPosition, LazyRevealProbe.State.materialize]

theorem storedLayerRoot_materialize_freshRootResolution
    (context : DeferredContext) (target : Position) (output : HashOutput)
    (result : DeferredResolution)
    (hresult : freshRootResolution target context output = some result) :
    StoredLayerRoot (materializeResolvedPosition context target result).state target
      (truncateHash output) := by
  unfold freshRootResolution at hresult
  by_cases hhit : context.state.hitAt (.position target) output
  · simp [hhit] at hresult
  · simp [hhit] at hresult
    subst result
    exact storedLayerRoot_materializeResolvedPosition context target _

noncomputable def candidateLayerRootPosition? (candidate : Probe) : Option Position :=
  match candidate.coordinate with
  | .position position => if IsLayerRoot position then some position else none
  | .chainStart _ _ _ _ => none

theorem candidateLayerRootPosition?_eq_some_iff
    (candidate : Probe) (target : Position) :
    candidateLayerRootPosition? candidate = some target ↔
      candidate.coordinate = .position target ∧ IsLayerRoot target := by
  cases candidate with
  | mk coordinate digest =>
      cases coordinate with
      | chainStart => simp [candidateLayerRootPosition?]
      | position position =>
          simp only [candidateLayerRootPosition?]
          by_cases hroot : IsLayerRoot position
          · rw [if_pos hroot]
            simp only [Option.some.injEq, Coordinate.position.injEq]
            constructor
            · intro heq
              subst target
              exact ⟨rfl, hroot⟩
            · rintro ⟨heq, _htarget⟩
              exact heq
          · rw [if_neg hroot]
            constructor
            · simp
            · rintro ⟨heq, htarget⟩
              have hposition : position = target := Coordinate.position.inj heq
              subst target
              exact False.elim (hroot htarget)

noncomputable def selectedLayerRootPosition?
    (ordinal : Nat) (output : PrivateWitnessPlanOutput) : Option Position :=
  if hselected : ordinal < output.2.length then
    candidateLayerRootPosition? (output.2.get ⟨ordinal, hselected⟩)
  else none

def selectedPrivateWitnessDigest (output : PrivateWitnessPlanOutput) : Digest :=
  match output.1 with
  | none => 0
  | some witness => truncateHash witness.output

theorem selectedLayerRootPosition?_eq_some_of_witnessFirstUsesLayerRootOrdinal
    {ordinal : Nat} {output : PrivateWitnessPlanOutput}
    (hfirst : WitnessFirstUsesLayerRootOrdinal ordinal output) :
    ∃ target, selectedLayerRootPosition? ordinal output = some target := by
  obtain ⟨witness, sourceOrdinal, _hwitness, hordinal, _hfirst, hroot⟩ := hfirst
  obtain ⟨target, hcoordinate, htarget⟩ := hroot
  have hselected : ordinal < output.2.length := by
    rw [← hordinal]
    exact sourceOrdinal.isLt
  refine ⟨target, ?_⟩
  unfold selectedLayerRootPosition?
  rw [dif_pos hselected, candidateLayerRootPosition?_eq_some_iff]
  have hindex : (⟨ordinal, hselected⟩ : Fin output.2.length) = sourceOrdinal :=
    Fin.ext hordinal.symm
  rw [hindex]
  exact ⟨hcoordinate, htarget⟩

theorem not_witnessFirstUsesLayerRootOrdinal_of_selectedLayerRootPosition?_eq_none
    {ordinal : Nat} {output : PrivateWitnessPlanOutput}
    (hposition : selectedLayerRootPosition? ordinal output = none) :
    ¬WitnessFirstUsesLayerRootOrdinal ordinal output := by
  intro hfirst
  obtain ⟨target, htarget⟩ :=
    selectedLayerRootPosition?_eq_some_of_witnessFirstUsesLayerRootOrdinal hfirst
  rw [hposition] at htarget
  simp at htarget

theorem witnessFirstUsesLayerRootOrdinal_fiber_data
    {ordinal : Nat} {output : PrivateWitnessPlanOutput} {target : Position}
    (hfirst : WitnessFirstUsesLayerRootOrdinal ordinal output)
    (hfiber : selectedLayerRootPosition? ordinal output = some target) :
    ∃ witness sourceOrdinal,
      output.1 = some witness ∧ sourceOrdinal.val = ordinal ∧
        firstPrivateWitnessOrdinal? witness output.2 = some sourceOrdinal ∧
        witness.position = target ∧
        truncateHash witness.output = (output.2.get sourceOrdinal).candidate ∧
        IsLayerRoot target := by
  obtain ⟨witness, sourceOrdinal, hwitness, hordinal, hsourceFirst, _hroot⟩ := hfirst
  have hmatch :=
    privateWitnessAtOrdinal_of_firstPrivateWitnessOrdinal?_eq_some hsourceFirst
  have hselected : ordinal < output.2.length := by
    rw [← hordinal]
    exact sourceOrdinal.isLt
  have hindex : (⟨ordinal, hselected⟩ : Fin output.2.length) = sourceOrdinal :=
    Fin.ext hordinal.symm
  have hfiber' := hfiber
  unfold selectedLayerRootPosition? at hfiber'
  rw [dif_pos hselected, candidateLayerRootPosition?_eq_some_iff, hindex] at hfiber'
  unfold PrivateWitnessAtOrdinal at hmatch
  have hposition : witness.position = target := by
    exact Coordinate.position.inj (hmatch.1.symm.trans hfiber'.1)
  exact ⟨witness, sourceOrdinal, hwitness, hordinal, hsourceFirst, hposition,
    hmatch.2, hfiber'.2⟩

theorem selectedPrivateWitnessDigest_eq_candidate_of_witnessFirstUsesLayerRootOrdinal
    {ordinal : Nat} {output : PrivateWitnessPlanOutput}
    (hfirst : WitnessFirstUsesLayerRootOrdinal ordinal output) :
    ∃ hselected : ordinal < output.2.length,
      selectedPrivateWitnessDigest output =
        (output.2.get ⟨ordinal, hselected⟩).candidate := by
  obtain ⟨target, htarget⟩ :=
    selectedLayerRootPosition?_eq_some_of_witnessFirstUsesLayerRootOrdinal hfirst
  obtain ⟨witness, sourceOrdinal, hwitness, hordinal, hsourceFirst, _hposition,
    hroot, _htarget⟩ := witnessFirstUsesLayerRootOrdinal_fiber_data hfirst htarget
  have hselected : ordinal < output.2.length := by
    rw [← hordinal]
    exact sourceOrdinal.isLt
  refine ⟨hselected, ?_⟩
  have hindex : (⟨ordinal, hselected⟩ : Fin output.2.length) = sourceOrdinal :=
    Fin.ext hordinal.symm
  rw [hindex, selectedPrivateWitnessDigest, hwitness]
  exact hroot

theorem earlier_fiber_candidate_ne_actual_root
    {ordinal : Nat} {output : PrivateWitnessPlanOutput} {target : Position}
    (hfirst : WitnessFirstUsesLayerRootOrdinal ordinal output)
    (hfiber : selectedLayerRootPosition? ordinal output = some target)
    (earlier : Fin output.2.length) (hlt : earlier.val < ordinal)
    (hcoordinate : (output.2.get earlier).coordinate = .position target) :
    (output.2.get earlier).candidate ≠
      truncateHash (Option.get output.1 (by
        obtain ⟨witness, _sourceOrdinal, hwitness, _⟩ :=
          witnessFirstUsesLayerRootOrdinal_fiber_data hfirst hfiber
        rw [hwitness]
        simp)).output := by
  obtain ⟨witness, sourceOrdinal, hwitness, hordinal, hsourceFirst, hposition,
    _hroot, _htarget⟩ := witnessFirstUsesLayerRootOrdinal_fiber_data hfirst hfiber
  have hwitnessGet : Option.get output.1 (by rw [hwitness]; simp) = witness := by
    simp [hwitness]
  rw [hwitnessGet]
  have huses : WitnessFirstUsesOrdinal ordinal output :=
    ⟨witness, sourceOrdinal, hwitness, hordinal, hsourceFirst⟩
  apply earlier_candidate_ne_of_witnessFirstUsesOrdinal
    huses witness hwitness earlier hlt target hcoordinate hposition

theorem probEvent_witnessFirstUsesLayerRootOrdinal_le_of_position_fibers
    (run : ProbComp PrivateWitnessPlanOutput) (ordinal : Nat)
    (hfiber : ∀ target,
      Pr[fun output => WitnessFirstUsesLayerRootOrdinal ordinal output ∧
          selectedLayerRootPosition? ordinal output = some target | run] ≤
        Pr[fun output => selectedLayerRootPosition? ordinal output = some target | run] *
          ((2 ^ digestBits : Nat) : ENNReal)⁻¹) :
    Pr[WitnessFirstUsesLayerRootOrdinal ordinal | run] ≤
      ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  apply probEvent_le_of_uniform_weighted_fibers run
    (WitnessFirstUsesLayerRootOrdinal ordinal)
    (selectedLayerRootPosition? ordinal)
    (((2 ^ digestBits : Nat) : ENNReal)⁻¹)
  intro position?
  cases position? with
  | none =>
      have hzero : Pr[fun output => WitnessFirstUsesLayerRootOrdinal ordinal output ∧
          selectedLayerRootPosition? ordinal output = none | run] = 0 := by
        apply probEvent_eq_zero
        intro output _houtput hevent
        exact not_witnessFirstUsesLayerRootOrdinal_of_selectedLayerRootPosition?_eq_none
          hevent.2 hevent.1
      rw [hzero]
      exact zero_le
  | some target => exact hfiber target

end SphincsSecurity.Concrete.OtsProbeSimulation

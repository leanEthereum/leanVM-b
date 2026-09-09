import SphincsSecurity.Proof.AdaptiveHiddenLabels

namespace SphincsSecurity.Concrete.AdaptiveHiddenLabels

open _root_.OracleComp OracleSpec HiddenLabelObservation RetainedObservation
set_option backward.isDefEq.respectTransparency false

structure ProbeMemory (Coordinate Memory : Type) where
  base : Memory
  active : Finset Coordinate
  probes : Nat

variable {Coordinate Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coordinate] [DecidableEq Coordinate]

noncomputable def countedEnvironment (environment : Environment auxSpec Coordinate Memory) :
    Environment auxSpec Coordinate (ProbeMemory Coordinate Memory) where
  auxiliary state input := (environment.auxiliary ⟨state.allowed, state.memory.base⟩ input).map fun result =>
    (result.1, ⟨result.2, state.memory.active, state.memory.probes⟩)
  probeAnswer memory probe answer :=
    ⟨environment.probeAnswer memory.base probe answer, memory.active, memory.probes + 1⟩
  probeStop memory probe := ⟨environment.probeStop memory.base probe, memory.active, memory.probes + 1⟩
  disclosure memory coordinate value :=
    ⟨environment.disclosure memory.base coordinate value, memory.active.erase coordinate, memory.probes⟩

def CandidateBound (space : Nat) (state : ObservationState Coordinate (ProbeMemory Coordinate Memory)) : Prop :=
  ∀ coordinate ∈ state.memory.active, space - state.memory.probes ≤ (state.allowed coordinate).card

omit [Fintype Coordinate] in
theorem candidateBound_probe (environment : Environment auxSpec Coordinate Memory) (space : Nat)
    (state : ObservationState Coordinate (ProbeMemory Coordinate Memory)) (h : CandidateBound space state)
    (probe : Probe Coordinate) (answer : HashOutput) :
    CandidateBound space (probeState (countedEnvironment environment) state probe answer) := by
  intro coordinate hcoordinate
  have hold := h coordinate hcoordinate
  have herase := probe.card_lower state.allowed answer coordinate
  change space - (state.memory.probes + 1) ≤ (probe.restrict state.allowed answer coordinate).card
  omega

omit [Fintype Coordinate] in
theorem candidateBound_stopped (environment : Environment auxSpec Coordinate Memory) (space : Nat)
    (state : ObservationState Coordinate (ProbeMemory Coordinate Memory)) (h : CandidateBound space state)
    (probe : Probe Coordinate) : CandidateBound space (stoppedState (countedEnvironment environment) state probe) := by
  intro coordinate hcoordinate
  have hold := h coordinate hcoordinate
  change space - (state.memory.probes + 1) ≤ (state.allowed coordinate).card
  omega

omit [Fintype Coordinate] in
theorem candidateBound_disclosed (environment : Environment auxSpec Coordinate Memory) (space : Nat)
    (state : ObservationState Coordinate (ProbeMemory Coordinate Memory)) (h : CandidateBound space state)
    (coordinate : Coordinate) (value : Digest) :
    CandidateBound space (disclosedState (countedEnvironment environment) state coordinate value) := by
  intro other hother
  change other ∈ state.memory.active.erase coordinate at hother
  change space - state.memory.probes ≤ (discloseTableValue state.allowed coordinate value other).card
  rw [discloseTableValue, Function.update_of_ne (Finset.mem_erase.mp hother).1]
  exact h other (Finset.mem_erase.mp hother).2

theorem candidateBound_step (environment : Environment auxSpec Coordinate Memory) (space : Nat)
    (state : ObservationState Coordinate (ProbeMemory Coordinate Memory)) (h : CandidateBound space state)
    (input : (World auxSpec Coordinate).Domain)
    (result : Option ((World auxSpec Coordinate).Range input) × ObservationState Coordinate (ProbeMemory Coordinate Memory))
    (hresult : (lazyImpl (countedEnvironment environment) input).run.run state result ≠ 0) :
    CandidateBound space result.2 := by
  cases input with
  | inl input =>
      simp only [lazyImpl, OptionT.run_mk, StateT.run_mk] at hresult
      obtain ⟨answer, hanswer, hfinal⟩ := (bind_nonzero _ _ _).mp hresult
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hfinal
      subst result
      rw [SPMF.liftM_apply] at hanswer
      have hsupport := (PMF.mem_support_iff _ _).mpr hanswer
      change answer ∈ ((environment.auxiliary ⟨state.allowed, state.memory.base⟩ input).map
        (fun result => (result.1, ProbeMemory.mk result.2 state.memory.active state.memory.probes))).support at hsupport
      rw [PMF.support_map] at hsupport
      obtain ⟨answer, _, heq⟩ := hsupport
      cases heq
      exact h
  | inr input =>
      cases input with
      | inl probe =>
          simp only [lazyImpl, OptionT.run_mk, StateT.run_mk] at hresult
          rcases (observe_nonzero _ _ _ _).mp hresult with ⟨_, hstop⟩ | ⟨answer, _, hnext⟩
          · simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hstop
            subst result
            exact candidateBound_stopped environment space state h probe
          · simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hnext
            subst result
            exact candidateBound_probe environment space state h probe answer
      | inr coordinate =>
          simp only [lazyImpl, OptionT.run_mk, StateT.run_mk] at hresult
          obtain ⟨value, _, hnext⟩ := (bind_nonzero _ _ _).mp hresult
          simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hnext
          subst result
          exact candidateBound_disclosed environment space state h coordinate value

theorem lazyRun_candidateBound {Result : Type} (environment : Environment auxSpec Coordinate Memory) (space : Nat)
    (computation : OracleComp (World auxSpec Coordinate) Result)
    (state : ObservationState Coordinate (ProbeMemory Coordinate Memory)) (h : CandidateBound space state)
    (result : Option Result × ObservationState Coordinate (ProbeMemory Coordinate Memory))
    (hresult : lazyRun (countedEnvironment environment) computation state result ≠ 0) :
    CandidateBound space result.2 :=
  lazyRun_preserves (countedEnvironment environment) (CandidateBound space)
    (fun state h input result hresult => candidateBound_step environment space state h input result hresult)
    computation state h result hresult

end SphincsSecurity.Concrete.AdaptiveHiddenLabels

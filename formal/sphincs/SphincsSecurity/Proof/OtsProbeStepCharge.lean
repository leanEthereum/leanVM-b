import SphincsSecurity.Proof.OtsOpeningQueryReserve

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

theorem Probe.MatchesInput.atOtsPosition {parameter : PublicParameter} {input : HashInput}
    {candidate : Probe} (hmatch : candidate.MatchesInput parameter input) :
    ∃ position : Position, IsOtsPosition position ∧ AtPosition parameter input position := by
  rcases candidate with ⟨coordinate, value⟩
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      obtain ⟨step, _, hinput⟩ := hmatch
      exact ⟨.chain lay tree leafIdx chainIdx step, trivial, digestBytes value, hinput⟩
  | position position =>
      cases position <;> simp only [Probe.MatchesInput] at hmatch
      case chain lay tree leafIdx chainIdx step =>
        split_ifs at hmatch with hnext
        · obtain ⟨nextStep, _, hinput⟩ := hmatch
          exact ⟨.chain lay tree leafIdx chainIdx nextStep, trivial, digestBytes value, hinput⟩
        · obtain ⟨_, payload, hinput, _⟩ := hmatch
          exact ⟨.leaf lay tree leafIdx, trivial, payload, hinput⟩

theorem probingHashQuery_eq_split_of_not_atOtsPosition (parameter : PublicParameter) (input : HashInput)
    (hnot : ¬ ∃ position : Position, IsOtsPosition position ∧ AtPosition parameter input position) :
    probingHashQuery parameter input = splitHashQuery (.ordinary input) := by
  have hprobe : decodeProbe? parameter input = none := by
    apply (decodeProbe?_eq_none_iff parameter input).mpr
    intro candidate hmatch
    exact hnot hmatch.atOtsPosition
  rw [probingHashQuery, hprobe]
  cases hposition : decodePosition? parameter input with
  | none => rfl
  | some position =>
      have hat := (decodePosition?_eq_some_iff parameter input position).mp hposition
      cases position with
      | chain lay tree leafIdx chainIdx step => exact (hnot ⟨.chain lay tree leafIdx chainIdx step, trivial, hat⟩).elim
      | leaf lay tree leafIdx => exact (hnot ⟨.leaf lay tree leafIdx, trivial, hat⟩).elim
      | node lay tree level nodeIdx => exact (hnot ⟨.node lay tree level nodeIdx, trivial, hat⟩).elim
      | ftsLeaf => rfl
      | ftsNode => rfl
      | ftsRoots => rfl

theorem probingHashQuery_expectedCharge_le_queryReserve (secretKey : SecretKey)
    (actualCache : QueryCache HashSpec) (input : HashInput)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache) (fuel : Nat) :
    LazyRevealProbe.expectedProbeCharge ((probingHashQuery secretKey.parameter input).run cache) state fuel ≤
      otsOpeningQueryReserve secretKey actualCache input := by
  classical
  by_cases hots : ∃ position : Position, IsOtsPosition position ∧ AtPosition secretKey.parameter input position
  · obtain ⟨position, hposition, hat⟩ := hots
    have hcost := LazyRevealProbe.expectedProbeCharge_le_queryBound _ state fuel 1
      (probingHashQuery_run_isProbeBound secretKey.parameter input cache)
    rw [Nat.cast_one] at hcost
    exact hcost.trans (otsOpeningQueryReserve_ge_one_of_atOtsPosition secretKey actualCache input position hat hposition)
  · rw [probingHashQuery_eq_split_of_not_atOtsPosition secretKey.parameter input hots]
    rw [LazyRevealProbe.expectedProbeCharge_eq_zero_of_probeFree _ state fuel (splitHashQuery_probeFree _ cache)]
    exact bot_le

end SphincsSecurity.Concrete.OtsProbeSimulation

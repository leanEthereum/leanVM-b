import SphincsSecurity.Proof.OtsProbeStartHistoryTrace

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

def ChainStartHistoryOutputHit (history : List Probe) (index : OtsSecretIndex) (output : HashOutput) : Prop :=
  ∃ candidate ∈ history, candidate.coordinate = index.coordinate ∧ truncateHash output = candidate.candidate

theorem chainStartEntryHit_update_iff
    (base : OtsSecretIndex → HashOutput) (index : OtsSecretIndex) (output : HashOutput)
    (coordinate : Coordinate) (digest : Digest) :
    ChainStartEntryHit (Function.update base index output) (coordinate, digest) ↔
      (coordinate = index.coordinate ∧ truncateHash output = digest) ∨
      (coordinate ≠ index.coordinate ∧ ChainStartEntryHit base (coordinate, digest)) := by
  classical
  cases coordinate with
  | position position => simp [ChainStartEntryHit, OtsSecretIndex.coordinate]
  | chainStart lay tree leafIdx chainIdx =>
      by_cases heq : (⟨lay, tree, leafIdx, chainIdx⟩ : OtsSecretIndex) = index
      · have hcoordinate : Coordinate.chainStart lay tree leafIdx chainIdx = index.coordinate :=
          congrArg OtsSecretIndex.coordinate heq
        simp [ChainStartEntryHit, heq, hcoordinate]
      · have hcoordinate : Coordinate.chainStart lay tree leafIdx chainIdx ≠ index.coordinate :=
          fun h => heq (OtsSecretIndex.coordinate_injective h)
        simp [ChainStartEntryHit, heq, hcoordinate]

theorem chainStartHistoryHit_update_iff
    (context : DeferredContext) (history : List Probe) (base : OtsSecretIndex → HashOutput)
    (index : OtsSecretIndex) (output : HashOutput) (hmissing : context.state.values index.coordinate = none) :
    ChainStartHistoryHit context history (Function.update base index output) ↔
      ChainStartHistoryOutputHit history index output ∨
      ChainStartHistoryHit { context with state := context.state.materialize index.coordinate output } history base := by
  classical
  constructor
  · rintro ⟨candidate, hcandidate, hvalue, hhit⟩
    rcases (chainStartEntryHit_update_iff base index output candidate.coordinate candidate.candidate).mp hhit with hsame | hother
    · exact Or.inl ⟨candidate, hcandidate, hsame⟩
    · refine Or.inr ⟨candidate, hcandidate, ?_, hother.2⟩
      simpa only [LazyRevealProbe.State.materialize, Function.update_of_ne hother.1] using hvalue
  · rintro (hhit | hhit)
    · obtain ⟨candidate, hcandidate, hcoordinate, hdigest⟩ := hhit
      refine ⟨candidate, hcandidate, by rwa [hcoordinate], ?_⟩
      exact (chainStartEntryHit_update_iff base index output candidate.coordinate candidate.candidate).mpr
        (Or.inl ⟨hcoordinate, hdigest⟩)
    · obtain ⟨candidate, hcandidate, hvalue, hhit⟩ := hhit
      have hother : candidate.coordinate ≠ index.coordinate := by
        intro heq
        simp [LazyRevealProbe.State.materialize, heq] at hvalue
      refine ⟨candidate, hcandidate, ?_, ?_⟩
      · simpa only [LazyRevealProbe.State.materialize, Function.update_of_ne hother] using hvalue
      · exact (chainStartEntryHit_update_iff base index output candidate.coordinate candidate.candidate).mpr
          (Or.inr ⟨hother, hhit⟩)

theorem evalDist_history_filtered_completionTable_read
    (context : DeferredContext) (history : List Probe) (index : OtsSecretIndex)
    (hmissing : context.state.values index.coordinate = none)
    (failure : ProbComp α) (next : (OtsSecretIndex → HashOutput) → HashOutput → ProbComp α) :
    evalDist (do
      let base ← sampleOtsHashTable
      if ChainStartHistoryHit context history base then failure
      else next (completedStartTable context.state base) (base index)) =
    evalDist (do
      let output ← LazyRevealProbe.sampleHashOutput
      if ChainStartHistoryOutputHit history index output then failure
      else do
        let base ← sampleOtsHashTable
        let after := { context with state := context.state.materialize index.coordinate output }
        if ChainStartHistoryHit after history base then failure
        else next (completedStartTable after.state base) output) := by
  let cont : (OtsSecretIndex → HashOutput) → HashOutput → ProbComp α := fun base output =>
    if ChainStartHistoryHit context history base then failure else next (completedStartTable context.state base) output
  have hcell := evalDist_completionTable_bind_cell_extract index cont
  have hcell' : evalDist (do
      let base ← sampleOtsHashTable
      cont base (base index)) = evalDist (do
      let output ← LazyRevealProbe.sampleHashOutput
      let base ← sampleOtsHashTable
      cont (Function.update base index output) output) := by
    simpa only [sampleOtsHashTable, LazyRevealProbe.sampleHashOutput] using hcell
  change evalDist (do let base ← sampleOtsHashTable; cont base (base index)) = _
  rw [hcell']
  apply evalDist_bind_congr
  intro output _houtput
  by_cases hhit : ChainStartHistoryOutputHit history index output
  · simp only [cont, chainStartHistoryHit_update_iff context history _ index output hmissing, hhit, true_or, ↓reduceIte]
    exact evalDist_sampleOtsHashTable_bind_const failure
  · simp only [if_neg hhit]
    apply evalDist_bind_congr
    intro base _hbase
    have htable : completedStartTable context.state (Function.update base index output) =
        completedStartTable (context.state.materialize index.coordinate output) base := by
      rw [completedStartTable_update_base_of_missing context.state base index output hmissing,
        completedStartTable_materialize_coordinate]
    simp only [cont, chainStartHistoryHit_update_iff context history base index output hmissing,
      hhit, false_or, htable]

end SphincsSecurity.Concrete.OtsProbeSimulation

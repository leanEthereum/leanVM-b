import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryFirstFire

/-!
# Ordinary boundary failures

The fixed-table detailed interpreter is averaged by drawing each missing chain start only when it
is revealed. Structural values remain lazy. This is the sampling-order bridge needed by the
ordinary first-fire bound.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

set_option maxHeartbeats 20000

def MissingChainStartHit (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) : Prop :=
  ∃ index,
    context.state.values index.coordinate = none ∧
      context.state.hitAt index.coordinate (table index)

theorem exists_digest_not_mem_pendingAt
    (state : LazyRevealProbe.State Coordinate) (coordinate : Coordinate)
    (hcard : state.pending.card < Fintype.card Digest) :
    ∃ candidate : Digest, candidate ∉ state.pendingAt coordinate := by
  have hcoordinateCard : (state.pendingAt coordinate).card < Fintype.card Digest := by
    have hle : (state.pendingAt coordinate).card ≤ state.pending.card := by
      have := state.pendingAway_card_add_pendingAt_card_le coordinate
      omega
    exact hle.trans_lt hcard
  have hne : state.pendingAt coordinate ≠ Finset.univ :=
    (Finset.card_lt_iff_ne_univ _).mp hcoordinateCard
  by_contra hmissing
  push Not at hmissing
  exact hne (Finset.eq_univ_of_forall hmissing)

theorem deferredCompletable_of_valid_of_no_boundary_hit
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hvalid : context.Valid) (hstarts : StartTableAgrees context.state table)
    (hprivate : ¬PrivateStructuralHit context)
    (hstart : ¬MissingChainStartHit table context)
    (hcard : context.state.pending.card < Fintype.card Digest) :
    DeferredCompletable table context := by
  classical
  let missingDigest : Coordinate → Digest := fun coordinate =>
    Classical.choose (exists_digest_not_mem_pendingAt context.state coordinate hcard)
  let completion : Coordinate → HashOutput := fun coordinate =>
    match context.state.values coordinate with
    | some output => output
    | none =>
        match coordinate with
        | .chainStart lay tree leafIdx chainIdx => table ⟨lay, tree, leafIdx, chainIdx⟩
        | .position position =>
            match context.values position with
            | some output => output
            | none => hashOutputOfDigest (missingDigest (.position position))
  refine ⟨completion, ?_, ?_, ?_, ?_⟩
  · intro coordinate output hvalue
    simp [completion, hvalue]
  · intro position output hvalue
    cases hstate : context.state.values (.position position) with
    | none => simp [completion, hstate, hvalue]
    | some stateOutput =>
        have heq : stateOutput = output := by
          have := hvalid.1 position stateOutput hstate
          rw [hvalue] at this
          exact (Option.some.inj this).symm
        simp [completion, hstate, heq]
  · intro coordinate candidate hpending
    cases hstate : context.state.values coordinate with
    | some output =>
        have hclean := hvalid.2 coordinate output hstate
        have hnotEq : truncateHash output ≠ candidate := by
          intro heq
          apply hclean
          unfold LazyRevealProbe.State.hitAt
          rw [LazyRevealProbe.State.mem_pendingAt_iff]
          simpa [heq] using hpending
        simpa [completion, hstate] using hnotEq
    | none =>
        cases coordinate with
        | chainStart lay tree leafIdx chainIdx =>
            let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
            have hnotHit : ¬context.state.hitAt index.coordinate (table index) := by
              intro hhit
              apply hstart
              exact ⟨index, by simpa [index, OtsSecretIndex.coordinate] using hstate, hhit⟩
            have hnotEq : truncateHash (table index) ≠ candidate := by
              intro heq
              apply hnotHit
              unfold LazyRevealProbe.State.hitAt
              rw [LazyRevealProbe.State.mem_pendingAt_iff]
              simpa [heq, index, OtsSecretIndex.coordinate] using hpending
            simpa [completion, hstate, index, OtsSecretIndex.coordinate] using hnotEq
        | position position =>
            cases hvalue : context.values position with
            | some output =>
                have hnotHit : ¬context.state.hitAt (.position position) output := by
                  intro hhit
                  exact hprivate ⟨position, output, hstate, hvalue, hhit⟩
                have hnotEq : truncateHash output ≠ candidate := by
                  intro heq
                  apply hnotHit
                  unfold LazyRevealProbe.State.hitAt
                  rw [LazyRevealProbe.State.mem_pendingAt_iff]
                  simpa [heq] using hpending
                simpa [completion, hstate, hvalue] using hnotEq
            | none =>
                have hmissing : missingDigest (.position position) ∉
                    context.state.pendingAt (.position position) :=
                  Classical.choose_spec
                    (exists_digest_not_mem_pendingAt context.state (.position position) hcard)
                have hnotEq : missingDigest (.position position) ≠ candidate := by
                  intro heq
                  apply hmissing
                  rw [LazyRevealProbe.State.mem_pendingAt_iff]
                  simpa [heq] using hpending
                simpa [completion, hstate, hvalue, truncateHash_hashOutputOfDigest] using hnotEq
  · intro index
    cases hstate : context.state.values index.coordinate with
    | none =>
        rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
        have hstate' : context.state.values
            (.chainStart lay tree leafIdx chainIdx) = none := by
          simpa [OtsSecretIndex.coordinate] using hstate
        change completion (.chainStart lay tree leafIdx chainIdx) =
          table ⟨lay, tree, leafIdx, chainIdx⟩
        simp [completion, hstate']
    | some output =>
        have heq := hstarts index output hstate
        simp [completion, hstate, heq]

def ChainStartEntryHit (table : OtsSecretIndex → HashOutput) :
    Coordinate × Digest → Prop
  | (⟨.chainStart lay tree leafIdx chainIdx, candidate⟩) =>
      truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩) = candidate
  | _ => False

set_option maxRecDepth 100000 in
set_option maxHeartbeats 200000 in
theorem probEvent_sampleOtsHashTable_cell_truncate_eq
    (index : OtsSecretIndex) (candidate : Digest) :
    Pr[fun table : OtsSecretIndex → HashOutput =>
        truncateHash (table index) = candidate | sampleOtsHashTable] ≤
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  have hdist :
      evalDist ((fun table : OtsSecretIndex → HashOutput => truncateHash (table index)) <$>
          sampleOtsHashTable) =
        evalDist (truncateHash <$> LazyRevealProbe.sampleHashOutput) := by
    let cont : (OtsSecretIndex → HashOutput) → HashOutput → ProbComp Digest :=
      fun _table output => pure (truncateHash output)
    have hcell := evalDist_completionTable_bind_cell_extract index cont
    have hcell' :
        evalDist (do
          let table ← sampleOtsHashTable
          cont table (table index)) =
        evalDist (do
          let output ← LazyRevealProbe.sampleHashOutput
          let table ← sampleOtsHashTable
          cont (Function.update table index output) output) := by
      simpa only [sampleOtsHashTable, LazyRevealProbe.sampleHashOutput] using hcell
    calc
      _ = evalDist (do
          let table ← sampleOtsHashTable
          cont table (table index)) := by rfl
      _ = evalDist (do
          let output ← LazyRevealProbe.sampleHashOutput
          let table ← sampleOtsHashTable
          cont (Function.update table index output) output) := hcell'
      _ = evalDist (truncateHash <$> LazyRevealProbe.sampleHashOutput) := by
        apply evalDist_bind_congr
        intro output _houtput
        change evalDist (do
            let _table ← sampleOtsHashTable
            pure (truncateHash output)) =
          evalDist (pure (truncateHash output) : ProbComp Digest)
        exact evalDist_sampleOtsHashTable_bind_const
          (pure (truncateHash output) : ProbComp Digest)
  calc
    _ = Pr[fun output : Digest => output = candidate |
        (fun table : OtsSecretIndex → HashOutput => truncateHash (table index)) <$>
          sampleOtsHashTable] := by
      rw [probEvent_map]
      rfl
    _ = Pr[fun output : Digest => output = candidate |
        truncateHash <$> LazyRevealProbe.sampleHashOutput] :=
      OracleComp.probEvent_congr' (fun _ _ => Iff.rfl) hdist
    _ = Pr[= candidate | truncateHash <$> LazyRevealProbe.sampleHashOutput] :=
      probEvent_eq_eq_probOutput _ candidate
    _ ≤ _ := by
      simpa only [LazyRevealProbe.sampleHashOutput] using
        SphincsSecurity.probOutput_truncateHash_le candidate

end SphincsSecurity.Concrete.OtsProbeSimulation

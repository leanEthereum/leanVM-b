import SphincsSecurity.Proof.OtsProbeResolvedBoundaryProbability

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

theorem privateStructuralHit_or_missingChainStartHit_of_not_completable
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hvalid : context.Valid) (hstarts : StartTableAgrees context.state table)
    (hcard : context.state.pending.card < Fintype.card Digest)
    (hnotCompletable : ¬DeferredCompletable table context) :
    PrivateStructuralHit context ∨ MissingChainStartHit table context := by
  by_cases hprivate : PrivateStructuralHit context
  · exact Or.inl hprivate
  · right
    by_contra hstart
    exact hnotCompletable
      (deferredCompletable_of_valid_of_no_boundary_hit table context hvalid hstarts hprivate
        hstart hcard)

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

theorem exists_chainStartEntryHit_of_missing_completedStartTable
    (context : DeferredContext) (base : OtsSecretIndex → HashOutput)
    (hmissing : MissingChainStartHit
      (completedStartTable context.state base) context) :
    ∃ entry ∈ context.state.pending, ChainStartEntryHit base entry := by
  obtain ⟨index, hvalue, hhit⟩ := hmissing
  have hlookup : completedStartTable context.state base index = base index := by
    simp [completedStartTable, hvalue]
  have hmem : (index.coordinate, truncateHash (base index)) ∈ context.state.pending := by
    rw [← LazyRevealProbe.State.mem_pendingAt_iff]
    simpa [LazyRevealProbe.State.hitAt, hlookup] using hhit
  refine ⟨(index.coordinate, truncateHash (base index)), hmem, ?_⟩
  rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
  simp [ChainStartEntryHit, OtsSecretIndex.coordinate]

theorem probEvent_missingChainStartHit_completedStartTable_le
    (context : DeferredContext) :
    Pr[fun base : OtsSecretIndex → HashOutput =>
        MissingChainStartHit (completedStartTable context.state base) context |
      sampleOtsHashTable] ≤
      (context.state.pending.card : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  calc
    _ ≤ Pr[fun base : OtsSecretIndex → HashOutput =>
        ∃ entry ∈ context.state.pending, ChainStartEntryHit base entry |
          sampleOtsHashTable] := probEvent_mono fun base _ hmissing =>
            exists_chainStartEntryHit_of_missing_completedStartTable context base hmissing
    _ ≤ ∑ entry ∈ context.state.pending,
        Pr[fun base => ChainStartEntryHit base entry | sampleOtsHashTable] :=
      probEvent_exists_finset_le_sum context.state.pending sampleOtsHashTable
        (fun entry base => ChainStartEntryHit base entry)
    _ ≤ ∑ _entry ∈ context.state.pending,
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_le_sum
      intro entry _hentry
      rcases entry with ⟨coordinate, candidate⟩
      cases coordinate with
      | chainStart lay tree leafIdx chainIdx =>
          exact probEvent_sampleOtsHashTable_cell_truncate_eq
            ⟨lay, tree, leafIdx, chainIdx⟩ candidate
      | position position => simp [ChainStartEntryHit]
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul]

noncomputable def runDirectResolvedDetailedWithCompletionTable
    (context : DeferredContext) (fuel : Nat)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    ProbComp (DirectDetailedResult alpha) :=
  OracleComp.construct
    (C := fun _ : OracleComp (LazyRevealProbe.World Coordinate) alpha =>
      DeferredContext → Nat → ProbComp (DirectDetailedResult alpha))
    (fun value context remaining => do
      let base ← sampleOtsHashTable
      pure (.done ⟨context, remaining, value, completedStartTable context.state base⟩))
    (fun input _next recursivelyRun context fuel =>
      match input with
      | .uniform n => do
          let output ← liftM (unifSpec.query n)
          recursivelyRun output context fuel
      | .hashOutput => do
          let output ← LazyRevealProbe.sampleHashOutput
          recursivelyRun output context fuel
      | .ensure coordinate =>
          recursivelyRun () { context with state := context.state.ensure coordinate } fuel
      | .probe coordinate candidate =>
          match fuel with
          | 0 => pure (.stopped .fuelExhausted)
          | remaining + 1 =>
              if coordinate ∈ context.state.revealed then
                recursivelyRun () context remaining
              else
                recursivelyRun ()
                  { context with state := context.state.addPending coordinate candidate }
                  remaining
      | .peek coordinate =>
          recursivelyRun (context.state.values coordinate) context fuel
      | .publish coordinate =>
          recursivelyRun () { context with state := context.state.publish coordinate } fuel
      | .reveal coordinate =>
          match context.state.values coordinate with
          | some output => recursivelyRun output context fuel
          | none =>
              match coordinate with
              | .chainStart _ _ _ _ => do
                  let output ← LazyRevealProbe.sampleHashOutput
                  if context.state.hitAt coordinate output then
                    pure (.stopped .ordinaryHit)
                  else
                    recursivelyRun output
                      { state := context.state.materialize coordinate output
                        values := context.values }
                      fuel
              | .position position =>
                  match context.values position with
                  | some output =>
                      if context.state.hitAt coordinate output then
                        pure (.stopped .privateStructuralHit)
                      else
                        recursivelyRun output
                          { state := context.state.materialize coordinate output
                            values := context.values }
                          fuel
                  | none => do
                      let output ← LazyRevealProbe.sampleHashOutput
                      if context.state.hitAt coordinate output then
                        pure (.stopped .ordinaryHit)
                      else
                        recursivelyRun output
                          { state := context.state.materialize coordinate output
                            values := context.values.install position output }
                          fuel)
    computation context fuel

theorem runDirectResolvedDetailedFromTable_pure
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (value : alpha) :
    runDirectResolvedDetailedFromTable context fuel table
        (pure value : OracleComp (LazyRevealProbe.World Coordinate) alpha) =
      pure (.done ⟨context, fuel, value, table⟩) := by
  rfl

theorem runDirectResolvedDetailedWithCompletionTable_pure
    (context : DeferredContext) (fuel : Nat) (value : alpha) :
    runDirectResolvedDetailedWithCompletionTable context fuel
        (pure value : OracleComp (LazyRevealProbe.World Coordinate) alpha) = (do
      let base ← sampleOtsHashTable
      pure (.done ⟨context, fuel, value, completedStartTable context.state base⟩)) := by
  rw [runDirectResolvedDetailedWithCompletionTable, OracleComp.construct_pure]

theorem runDirectResolvedDetailedWithCompletionTable_uniform_query_bind
    (context : DeferredContext) (fuel n : Nat)
    (next : Fin (n + 1) → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectResolvedDetailedWithCompletionTable context fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) (.uniform n)) :
          OracleComp (LazyRevealProbe.World Coordinate) (Fin (n + 1))) >>= next) = (do
      let output ← liftM (unifSpec.query n)
      runDirectResolvedDetailedWithCompletionTable context fuel (next output)) := by
  rfl

theorem runDirectResolvedDetailedWithCompletionTable_hashOutput_query_bind
    (context : DeferredContext) (fuel : Nat)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectResolvedDetailedWithCompletionTable context fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) .hashOutput) :
          OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next) = (do
      let output ← LazyRevealProbe.sampleHashOutput
      runDirectResolvedDetailedWithCompletionTable context fuel (next output)) := by
  rfl

theorem runDirectResolvedDetailedWithCompletionTable_ensure_query_bind
    (context : DeferredContext) (fuel : Nat) (coordinate : Coordinate)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectResolvedDetailedWithCompletionTable context fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.ensure coordinate)) : OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      runDirectResolvedDetailedWithCompletionTable
        { context with state := context.state.ensure coordinate } fuel (next ()) := by
  rfl

theorem runDirectResolvedDetailedWithCompletionTable_probe_query_bind
    (context : DeferredContext) (fuel : Nat) (coordinate : Coordinate) (candidate : Digest)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectResolvedDetailedWithCompletionTable context fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.probe coordinate candidate)) :
            OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      match fuel with
      | 0 => pure (.stopped .fuelExhausted)
      | remaining + 1 =>
          if coordinate ∈ context.state.revealed then
            runDirectResolvedDetailedWithCompletionTable context remaining (next ())
          else
            runDirectResolvedDetailedWithCompletionTable
              { context with state := context.state.addPending coordinate candidate }
              remaining (next ()) := by
  rfl

theorem runDirectResolvedDetailedWithCompletionTable_peek_query_bind
    (context : DeferredContext) (fuel : Nat) (coordinate : Coordinate)
    (next : Option HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectResolvedDetailedWithCompletionTable context fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.peek coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) (Option HashOutput)) >>= next) =
      runDirectResolvedDetailedWithCompletionTable context fuel
        (next (context.state.values coordinate)) := by
  rfl

theorem runDirectResolvedDetailedWithCompletionTable_publish_query_bind
    (context : DeferredContext) (fuel : Nat) (coordinate : Coordinate)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectResolvedDetailedWithCompletionTable context fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.publish coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      runDirectResolvedDetailedWithCompletionTable
        { context with state := context.state.publish coordinate } fuel (next ()) := by
  rfl

theorem runDirectResolvedDetailedWithCompletionTable_reveal_query_bind
    (context : DeferredContext) (fuel : Nat) (coordinate : Coordinate)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectResolvedDetailedWithCompletionTable context fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.reveal coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next) =
      (match context.state.values coordinate with
      | some output =>
          runDirectResolvedDetailedWithCompletionTable context fuel (next output)
      | none =>
          match coordinate with
          | .chainStart _ _ _ _ => do
              let output ← LazyRevealProbe.sampleHashOutput
              if context.state.hitAt coordinate output then
                pure (.stopped .ordinaryHit)
              else
                runDirectResolvedDetailedWithCompletionTable
                  { state := context.state.materialize coordinate output
                    values := context.values }
                  fuel (next output)
          | .position position =>
              match context.values position with
              | some output =>
                  if context.state.hitAt coordinate output then
                    pure (.stopped .privateStructuralHit)
                  else
                    runDirectResolvedDetailedWithCompletionTable
                      { state := context.state.materialize coordinate output
                        values := context.values }
                      fuel (next output)
              | none => do
                  let output ← LazyRevealProbe.sampleHashOutput
                  if context.state.hitAt coordinate output then
                    pure (.stopped .ordinaryHit)
                  else
                    runDirectResolvedDetailedWithCompletionTable
                      { state := context.state.materialize coordinate output
                        values := context.values.install position output }
                      fuel (next output)) := by
  cases coordinate <;> rfl

private theorem evalDist_sampled_runDirectResolvedDetailed_reveal_chainStart_query_bind
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (ih : ∀ output context fuel,
      𝒟[do
        let base ← sampleOtsHashTable
        let table := completedStartTable context.state base
        runDirectResolvedDetailedFromTable context fuel table (next output)] =
        𝒟[runDirectResolvedDetailedWithCompletionTable context fuel (next output)])
    (context : DeferredContext) (fuel : Nat) :
    𝒟[do
      let base ← sampleOtsHashTable
      let table := completedStartTable context.state base
      runDirectResolvedDetailedFromTable context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.reveal (.chainStart lay tree leafIdx chainIdx))) :
            OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next)] =
      𝒟[runDirectResolvedDetailedWithCompletionTable context fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.reveal (.chainStart lay tree leafIdx chainIdx))) :
            OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next)] := by
  simp_rw [runDirectResolvedDetailedFromTable_reveal_query_bind]
  rw [runDirectResolvedDetailedWithCompletionTable_reveal_query_bind]
  cases hstate : context.state.values (.chainStart lay tree leafIdx chainIdx) with
  | some output => exact ih output context fuel
  | none =>
      let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
      let cont := fun base : OtsSecretIndex → HashOutput =>
        fun output : HashOutput =>
          if context.state.hitAt (.chainStart lay tree leafIdx chainIdx) output then
            pure (.stopped .ordinaryHit)
          else
            runDirectResolvedDetailedFromTable
              { state := context.state.materialize
                  (.chainStart lay tree leafIdx chainIdx) output
                values := context.values }
              fuel (completedStartTable context.state base) (next output)
      have hcell := evalDist_completionTable_bind_cell_extract index cont
      have hstate' : context.state.values index.coordinate = none := by
        simpa [index, OtsSecretIndex.coordinate] using hstate
      calc
        _ = 𝒟[do
            let base ← sampleOtsHashTable
            cont base (base index)] := by
          apply congrArg evalDist
          apply bind_congr
          intro base
          have hlookup : completedStartTable context.state base index = base index := by
            change (context.state.values index.coordinate).getD (base index) = base index
            rw [hstate']
            rfl
          simp only [cont]
          rw [hlookup]
        _ = 𝒟[do
            let output ← LazyRevealProbe.sampleHashOutput
            let base ← sampleOtsHashTable
            cont (Function.update base index output) output] := by
          simpa only [sampleOtsHashTable, LazyRevealProbe.sampleHashOutput] using hcell
        _ = _ := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro output
          by_cases hhit : context.state.hitAt
              (.chainStart lay tree leafIdx chainIdx) output
          · simp only [cont, hhit, ↓reduceIte]
            simpa using evalDist_sampleOtsHashTable_bind_const
              (pure (.stopped .ordinaryHit) : ProbComp (DirectDetailedResult alpha))
          · simp only [cont, hhit, ↓reduceIte]
            have hnext := ih output
              { state := context.state.materialize
                  (.chainStart lay tree leafIdx chainIdx) output
                values := context.values }
              fuel
            have htable (base : OtsSecretIndex → HashOutput) :
                completedStartTable context.state (Function.update base index output) =
                  completedStartTable
                    (context.state.materialize
                      (.chainStart lay tree leafIdx chainIdx) output) base := by
              rw [completedStartTable_update_base_of_missing context.state base index
                output hstate']
              simpa [index, OtsSecretIndex.coordinate] using
                (completedStartTable_materialize_coordinate context.state base index output).symm
            calc
              _ = 𝒟[do
                  let base ← sampleOtsHashTable
                  let table := completedStartTable
                    (context.state.materialize
                      (.chainStart lay tree leafIdx chainIdx) output) base
                  runDirectResolvedDetailedFromTable
                    { state := context.state.materialize
                        (.chainStart lay tree leafIdx chainIdx) output
                      values := context.values }
                    fuel table (next output)] := by
                apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                intro base
                rw [htable base]
              _ = _ := hnext

private theorem evalDist_sampled_runDirectResolvedDetailed_reveal_position_query_bind
    (position : Position)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (ih : ∀ output context fuel,
      𝒟[do
        let base ← sampleOtsHashTable
        let table := completedStartTable context.state base
        runDirectResolvedDetailedFromTable context fuel table (next output)] =
        𝒟[runDirectResolvedDetailedWithCompletionTable context fuel (next output)])
    (context : DeferredContext) (fuel : Nat) :
    𝒟[do
      let base ← sampleOtsHashTable
      let table := completedStartTable context.state base
      runDirectResolvedDetailedFromTable context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.reveal (.position position))) :
            OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next)] =
      𝒟[runDirectResolvedDetailedWithCompletionTable context fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.reveal (.position position))) :
            OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next)] := by
  simp_rw [runDirectResolvedDetailedFromTable_reveal_query_bind]
  rw [runDirectResolvedDetailedWithCompletionTable_reveal_query_bind]
  cases hstate : context.state.values (.position position) with
  | some output => exact ih output context fuel
  | none =>
      cases hprivate : context.values position with
      | some output =>
          by_cases hhit : context.state.hitAt (.position position) output
          · simp only [hprivate, hhit, ↓reduceIte]
            simpa using evalDist_sampleOtsHashTable_bind_const
              (pure (.stopped .privateStructuralHit) :
                ProbComp (DirectDetailedResult alpha))
          · simp only [hprivate, hhit, ↓reduceIte]
            have hnext := ih output
              { state := context.state.materialize (.position position) output
                values := context.values }
              fuel
            calc
              _ = 𝒟[do
                  let base ← sampleOtsHashTable
                  runDirectResolvedDetailedFromTable
                    { state := context.state.materialize (.position position) output
                      values := context.values }
                    fuel
                    (completedStartTable
                      (context.state.materialize (.position position) output) base)
                    (next output)] := by
                apply congrArg evalDist
                apply bind_congr
                intro base
                rw [completedStartTable_materialize_position]
              _ = _ := hnext
      | none =>
          simp only [hprivate]
          calc
            _ = 𝒟[LazyRevealProbe.sampleHashOutput >>= fun output =>
                sampleOtsHashTable >>= fun base =>
                  if context.state.hitAt (.position position) output then
                    pure (.stopped .ordinaryHit)
                  else
                    runDirectResolvedDetailedFromTable
                      { state := context.state.materialize (.position position) output
                        values := context.values.install position output }
                      fuel (completedStartTable context.state base) (next output)] :=
              OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
            _ = _ := by
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro output
              by_cases hhit : context.state.hitAt (.position position) output
              · simp only [hhit, ↓reduceIte]
                simpa using evalDist_sampleOtsHashTable_bind_const
                  (pure (.stopped .ordinaryHit) : ProbComp (DirectDetailedResult alpha))
              · simp only [hhit, ↓reduceIte]
                have hnext := ih output
                  { state := context.state.materialize (.position position) output
                    values := context.values.install position output }
                  fuel
                calc
                  _ = 𝒟[do
                      let base ← sampleOtsHashTable
                      runDirectResolvedDetailedFromTable
                        { state := context.state.materialize (.position position) output
                          values := context.values.install position output }
                        fuel
                        (completedStartTable
                          (context.state.materialize (.position position) output) base)
                        (next output)] := by
                    apply congrArg evalDist
                    apply bind_congr
                    intro base
                    rw [completedStartTable_materialize_position]
                  _ = _ := hnext

private theorem evalDist_sampled_runDirectResolvedDetailed_reveal_query_bind
    (coordinate : Coordinate)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (ih : ∀ output context fuel,
      𝒟[do
        let base ← sampleOtsHashTable
        let table := completedStartTable context.state base
        runDirectResolvedDetailedFromTable context fuel table (next output)] =
        𝒟[runDirectResolvedDetailedWithCompletionTable context fuel (next output)])
    (context : DeferredContext) (fuel : Nat) :
    𝒟[do
      let base ← sampleOtsHashTable
      let table := completedStartTable context.state base
      runDirectResolvedDetailedFromTable context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.reveal coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next)] =
      𝒟[runDirectResolvedDetailedWithCompletionTable context fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.reveal coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next)] := by
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      exact evalDist_sampled_runDirectResolvedDetailed_reveal_chainStart_query_bind
        lay tree leafIdx chainIdx next ih context fuel
  | position position =>
      exact evalDist_sampled_runDirectResolvedDetailed_reveal_position_query_bind
        position next ih context fuel

private def DirectDetailedSamplingEq
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (context : DeferredContext) (fuel : Nat) : Prop :=
  𝒟[do
    let base ← sampleOtsHashTable
    let table := completedStartTable context.state base
    runDirectResolvedDetailedFromTable context fuel table computation] =
    𝒟[runDirectResolvedDetailedWithCompletionTable context fuel computation]

private theorem directDetailedSamplingEq_pure
    (value : alpha) (context : DeferredContext) (fuel : Nat) :
    DirectDetailedSamplingEq
      (pure value : OracleComp (LazyRevealProbe.World Coordinate) alpha) context fuel := by
  unfold DirectDetailedSamplingEq
  simp_rw [runDirectResolvedDetailedFromTable_pure]
  rw [runDirectResolvedDetailedWithCompletionTable_pure]

private theorem directDetailedSamplingEq_uniform_query_bind
    (n : Nat)
    (next : Fin (n + 1) → OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (ih : ∀ output context fuel, DirectDetailedSamplingEq (next output) context fuel)
    (context : DeferredContext) (fuel : Nat) :
    DirectDetailedSamplingEq
      ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) (.uniform n)) :
        OracleComp (LazyRevealProbe.World Coordinate) (Fin (n + 1))) >>= next)
      context fuel := by
  unfold DirectDetailedSamplingEq at ih ⊢
  simp_rw [runDirectResolvedDetailedFromTable_uniform_query_bind]
  rw [runDirectResolvedDetailedWithCompletionTable_uniform_query_bind]
  calc
    _ = 𝒟[(liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>= fun output =>
        sampleOtsHashTable >>= fun base =>
          runDirectResolvedDetailedFromTable context fuel
            (completedStartTable context.state base) (next output)] :=
      OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
    _ = _ := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro output
      exact ih output context fuel

private theorem directDetailedSamplingEq_hashOutput_query_bind
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (ih : ∀ output context fuel, DirectDetailedSamplingEq (next output) context fuel)
    (context : DeferredContext) (fuel : Nat) :
    DirectDetailedSamplingEq
      ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) .hashOutput) :
        OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next)
      context fuel := by
  unfold DirectDetailedSamplingEq at ih ⊢
  simp_rw [runDirectResolvedDetailedFromTable_hashOutput_query_bind]
  rw [runDirectResolvedDetailedWithCompletionTable_hashOutput_query_bind]
  calc
    _ = 𝒟[LazyRevealProbe.sampleHashOutput >>= fun output =>
        sampleOtsHashTable >>= fun base =>
          runDirectResolvedDetailedFromTable context fuel
            (completedStartTable context.state base) (next output)] :=
      OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
    _ = _ := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro output
      exact ih output context fuel

private theorem directDetailedSamplingEq_ensure_query_bind
    (coordinate : Coordinate)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (ih : ∀ output context fuel, DirectDetailedSamplingEq (next output) context fuel)
    (context : DeferredContext) (fuel : Nat) :
    DirectDetailedSamplingEq
      ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
        (.ensure coordinate)) : OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next)
      context fuel := by
  unfold DirectDetailedSamplingEq at ih ⊢
  simp_rw [runDirectResolvedDetailedFromTable_ensure_query_bind]
  rw [runDirectResolvedDetailedWithCompletionTable_ensure_query_bind]
  have hnext := ih () { context with state := context.state.ensure coordinate } fuel
  calc
    _ = 𝒟[do
        let base ← sampleOtsHashTable
        runDirectResolvedDetailedFromTable
          { context with state := context.state.ensure coordinate } fuel
          (completedStartTable (context.state.ensure coordinate) base) (next ())] := by
      apply congrArg evalDist
      apply bind_congr
      intro base
      rw [completedStartTable_ensure]
    _ = _ := hnext

private theorem directDetailedSamplingEq_probe_query_bind
    (coordinate : Coordinate) (candidate : Digest)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (ih : ∀ output context fuel, DirectDetailedSamplingEq (next output) context fuel)
    (context : DeferredContext) (fuel : Nat) :
    DirectDetailedSamplingEq
      ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
        (.probe coordinate candidate)) :
          OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next)
      context fuel := by
  unfold DirectDetailedSamplingEq at ih ⊢
  simp_rw [runDirectResolvedDetailedFromTable_probe_query_bind]
  rw [runDirectResolvedDetailedWithCompletionTable_probe_query_bind]
  cases fuel with
  | zero =>
      simpa using evalDist_sampleOtsHashTable_bind_const
        (pure (.stopped .fuelExhausted) : ProbComp (DirectDetailedResult alpha))
  | succ remaining =>
      by_cases hrevealed : coordinate ∈ context.state.revealed
      · simp only [hrevealed, ↓reduceIte]
        exact ih () context remaining
      · simp only [hrevealed, ↓reduceIte]
        have hnext := ih ()
          { context with state := context.state.addPending coordinate candidate } remaining
        calc
          _ = 𝒟[do
              let base ← sampleOtsHashTable
              runDirectResolvedDetailedFromTable
                { context with state := context.state.addPending coordinate candidate }
                remaining
                (completedStartTable
                  (context.state.addPending coordinate candidate) base) (next ())] := by
            apply congrArg evalDist
            apply bind_congr
            intro base
            rw [completedStartTable_addPending]
          _ = _ := hnext

private theorem directDetailedSamplingEq_peek_query_bind
    (coordinate : Coordinate)
    (next : Option HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (ih : ∀ output context fuel, DirectDetailedSamplingEq (next output) context fuel)
    (context : DeferredContext) (fuel : Nat) :
    DirectDetailedSamplingEq
      ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
        (.peek coordinate)) :
          OracleComp (LazyRevealProbe.World Coordinate) (Option HashOutput)) >>= next)
      context fuel := by
  unfold DirectDetailedSamplingEq at ih ⊢
  simp_rw [runDirectResolvedDetailedFromTable_peek_query_bind]
  rw [runDirectResolvedDetailedWithCompletionTable_peek_query_bind]
  exact ih (context.state.values coordinate) context fuel

private theorem directDetailedSamplingEq_publish_query_bind
    (coordinate : Coordinate)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (ih : ∀ output context fuel, DirectDetailedSamplingEq (next output) context fuel)
    (context : DeferredContext) (fuel : Nat) :
    DirectDetailedSamplingEq
      ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
        (.publish coordinate)) :
          OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next)
      context fuel := by
  unfold DirectDetailedSamplingEq at ih ⊢
  simp_rw [runDirectResolvedDetailedFromTable_publish_query_bind]
  rw [runDirectResolvedDetailedWithCompletionTable_publish_query_bind]
  have hnext := ih () { context with state := context.state.publish coordinate } fuel
  calc
    _ = 𝒟[do
        let base ← sampleOtsHashTable
        runDirectResolvedDetailedFromTable
          { context with state := context.state.publish coordinate } fuel
          (completedStartTable (context.state.publish coordinate) base) (next ())] := by
      apply congrArg evalDist
      apply bind_congr
      intro base
      rw [completedStartTable_publish]
    _ = _ := hnext

private theorem directDetailedSamplingEq_reveal_query_bind
    (coordinate : Coordinate)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (ih : ∀ output context fuel, DirectDetailedSamplingEq (next output) context fuel)
    (context : DeferredContext) (fuel : Nat) :
    DirectDetailedSamplingEq
      ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
        (.reveal coordinate)) :
          OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next)
      context fuel := by
  unfold DirectDetailedSamplingEq at ih ⊢
  exact evalDist_sampled_runDirectResolvedDetailed_reveal_query_bind
    coordinate next ih context fuel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000 in
theorem evalDist_sampled_runDirectResolvedDetailed_eq_completionTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (context : DeferredContext) (fuel : Nat) :
    𝒟[do
      let base ← sampleOtsHashTable
      let table := completedStartTable context.state base
      runDirectResolvedDetailedFromTable context fuel table computation] =
      𝒟[runDirectResolvedDetailedWithCompletionTable context fuel computation] := by
  change DirectDetailedSamplingEq computation context fuel
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value => exact directDetailedSamplingEq_pure value context fuel
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          exact directDetailedSamplingEq_uniform_query_bind n next ih context fuel
      | hashOutput =>
          exact directDetailedSamplingEq_hashOutput_query_bind next ih context fuel
      | ensure coordinate =>
          exact directDetailedSamplingEq_ensure_query_bind coordinate next ih context fuel
      | probe coordinate candidate =>
          exact directDetailedSamplingEq_probe_query_bind coordinate candidate next ih context fuel
      | peek coordinate =>
          exact directDetailedSamplingEq_peek_query_bind coordinate next ih context fuel
      | publish coordinate =>
          exact directDetailedSamplingEq_publish_query_bind coordinate next ih context fuel
      | reveal coordinate =>
          exact directDetailedSamplingEq_reveal_query_bind coordinate next ih context fuel

noncomputable def finishDirectDetailedSafeOrdinaryObserve
    (observe : (OtsSecretIndex → HashOutput) →
      DeferredContext → Nat → alpha → ProbComp Bool) :
    DirectDetailedResult alpha → ProbComp Bool
  | .stopped .ordinaryHit => pure true
  | .stopped _ => pure false
  | .done result => observe result.table result.context result.remaining result.value

noncomputable def runDirectDetailedSafeOrdinaryWithCompletionTable
    (observe : (OtsSecretIndex → HashOutput) →
      DeferredContext → Nat → alpha → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha) : ProbComp Bool :=
  runDirectResolvedDetailedWithCompletionTable context fuel computation >>=
    finishDirectDetailedSafeOrdinaryObserve observe

theorem evalDist_sampled_runDirectDetailedSafeOrdinary_eq_completionTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (observe : (OtsSecretIndex → HashOutput) →
      DeferredContext → Nat → alpha → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) :
    𝒟[(do
        let base ← sampleOtsHashTable
        let table := completedStartTable context.state base
        runDirectResolvedDetailedFromTable context fuel table computation) >>=
          finishDirectDetailedSafeOrdinaryObserve observe] =
      𝒟[runDirectDetailedSafeOrdinaryWithCompletionTable observe context fuel computation] := by
  unfold runDirectDetailedSafeOrdinaryWithCompletionTable
  exact evalDist_bind_eq_of_evalDist_eq
    (evalDist_sampled_runDirectResolvedDetailed_eq_completionTable computation context fuel)
    (finishDirectDetailedSafeOrdinaryObserve observe)

theorem runDirectDetailedSafeOrdinaryWithCompletionTable_pure
    (observe : (OtsSecretIndex → HashOutput) →
      DeferredContext → Nat → alpha → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (value : alpha) :
    runDirectDetailedSafeOrdinaryWithCompletionTable observe context fuel
        (pure value : OracleComp (LazyRevealProbe.World Coordinate) alpha) = (do
      let base ← sampleOtsHashTable
      observe (completedStartTable context.state base) context fuel value) := by
  rw [runDirectDetailedSafeOrdinaryWithCompletionTable,
    runDirectResolvedDetailedWithCompletionTable_pure]
  simp only [bind_assoc, pure_bind, finishDirectDetailedSafeOrdinaryObserve]

theorem runDirectDetailedSafeOrdinaryWithCompletionTable_uniform_query_bind
    (observe : (OtsSecretIndex → HashOutput) →
      DeferredContext → Nat → alpha → ProbComp Bool)
    (context : DeferredContext) (fuel n : Nat)
    (next : Fin (n + 1) → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectDetailedSafeOrdinaryWithCompletionTable observe context fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) (.uniform n)) :
          OracleComp (LazyRevealProbe.World Coordinate) (Fin (n + 1))) >>= next) = (do
      let output ← liftM (unifSpec.query n)
      runDirectDetailedSafeOrdinaryWithCompletionTable observe context fuel (next output)) := by
  rw [runDirectDetailedSafeOrdinaryWithCompletionTable,
    runDirectResolvedDetailedWithCompletionTable_uniform_query_bind, bind_assoc]
  rfl

theorem runDirectDetailedSafeOrdinaryWithCompletionTable_hashOutput_query_bind
    (observe : (OtsSecretIndex → HashOutput) →
      DeferredContext → Nat → alpha → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectDetailedSafeOrdinaryWithCompletionTable observe context fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) .hashOutput) :
          OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next) = (do
      let output ← LazyRevealProbe.sampleHashOutput
      runDirectDetailedSafeOrdinaryWithCompletionTable observe context fuel (next output)) := by
  rw [runDirectDetailedSafeOrdinaryWithCompletionTable,
    runDirectResolvedDetailedWithCompletionTable_hashOutput_query_bind, bind_assoc]
  rfl

theorem runDirectDetailedSafeOrdinaryWithCompletionTable_ensure_query_bind
    (observe : (OtsSecretIndex → HashOutput) →
      DeferredContext → Nat → alpha → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (coordinate : Coordinate)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectDetailedSafeOrdinaryWithCompletionTable observe context fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.ensure coordinate)) : OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      runDirectDetailedSafeOrdinaryWithCompletionTable observe
        { context with state := context.state.ensure coordinate } fuel (next ()) := by
  rw [runDirectDetailedSafeOrdinaryWithCompletionTable,
    runDirectResolvedDetailedWithCompletionTable_ensure_query_bind]
  rfl

theorem runDirectDetailedSafeOrdinaryWithCompletionTable_probe_query_bind
    (observe : (OtsSecretIndex → HashOutput) →
      DeferredContext → Nat → alpha → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (coordinate : Coordinate) (candidate : Digest)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectDetailedSafeOrdinaryWithCompletionTable observe context fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.probe coordinate candidate)) :
            OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      match fuel with
      | 0 => pure false
      | remaining + 1 =>
          if coordinate ∈ context.state.revealed then
            runDirectDetailedSafeOrdinaryWithCompletionTable observe context remaining (next ())
          else
            runDirectDetailedSafeOrdinaryWithCompletionTable observe
              { context with state := context.state.addPending coordinate candidate }
              remaining (next ()) := by
  rw [runDirectDetailedSafeOrdinaryWithCompletionTable,
    runDirectResolvedDetailedWithCompletionTable_probe_query_bind]
  cases fuel with
  | zero => rfl
  | succ remaining =>
      by_cases hrevealed : coordinate ∈ context.state.revealed <;>
        simp only [hrevealed, ↓reduceIte] <;> rfl

theorem runDirectDetailedSafeOrdinaryWithCompletionTable_peek_query_bind
    (observe : (OtsSecretIndex → HashOutput) →
      DeferredContext → Nat → alpha → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (coordinate : Coordinate)
    (next : Option HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectDetailedSafeOrdinaryWithCompletionTable observe context fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.peek coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) (Option HashOutput)) >>= next) =
      runDirectDetailedSafeOrdinaryWithCompletionTable observe context fuel
        (next (context.state.values coordinate)) := by
  rw [runDirectDetailedSafeOrdinaryWithCompletionTable,
    runDirectResolvedDetailedWithCompletionTable_peek_query_bind]
  rfl

theorem runDirectDetailedSafeOrdinaryWithCompletionTable_publish_query_bind
    (observe : (OtsSecretIndex → HashOutput) →
      DeferredContext → Nat → alpha → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (coordinate : Coordinate)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectDetailedSafeOrdinaryWithCompletionTable observe context fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.publish coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      runDirectDetailedSafeOrdinaryWithCompletionTable observe
        { context with state := context.state.publish coordinate } fuel (next ()) := by
  rw [runDirectDetailedSafeOrdinaryWithCompletionTable,
    runDirectResolvedDetailedWithCompletionTable_publish_query_bind]
  rfl

theorem runDirectDetailedSafeOrdinaryWithCompletionTable_reveal_query_bind
    (observe : (OtsSecretIndex → HashOutput) →
      DeferredContext → Nat → alpha → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (coordinate : Coordinate)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectDetailedSafeOrdinaryWithCompletionTable observe context fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.reveal coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next) =
      (match context.state.values coordinate with
      | some output =>
          runDirectDetailedSafeOrdinaryWithCompletionTable observe context fuel (next output)
      | none =>
          match coordinate with
          | .chainStart _ _ _ _ => do
              let output ← LazyRevealProbe.sampleHashOutput
              if context.state.hitAt coordinate output then pure true
              else
                runDirectDetailedSafeOrdinaryWithCompletionTable observe
                  { state := context.state.materialize coordinate output
                    values := context.values }
                  fuel (next output)
          | .position position =>
              match context.values position with
              | some output =>
                  if context.state.hitAt coordinate output then pure false
                  else
                    runDirectDetailedSafeOrdinaryWithCompletionTable observe
                      { state := context.state.materialize coordinate output
                        values := context.values }
                      fuel (next output)
              | none => do
                  let output ← LazyRevealProbe.sampleHashOutput
                  if context.state.hitAt coordinate output then pure true
                  else
                    runDirectDetailedSafeOrdinaryWithCompletionTable observe
                      { state := context.state.materialize coordinate output
                        values := context.values.install position output }
                      fuel (next output)) := by
  rw [runDirectDetailedSafeOrdinaryWithCompletionTable,
    runDirectResolvedDetailedWithCompletionTable_reveal_query_bind]
  cases hstate : context.state.values coordinate with
  | some output => rfl
  | none =>
      cases coordinate with
      | chainStart lay tree leafIdx chainIdx =>
          simp only [bind_assoc]
          apply bind_congr
          intro output
          by_cases hhit : context.state.hitAt
              (.chainStart lay tree leafIdx chainIdx) output <;>
            simp only [hhit, ↓reduceIte] <;> rfl
      | position position =>
          cases hprivate : context.values position with
          | some output =>
              by_cases hhit : context.state.hitAt (.position position) output <;>
                simp only [hprivate, hhit, ↓reduceIte] <;> rfl
          | none =>
              simp only [hprivate, bind_assoc]
              apply bind_congr
              intro output
              by_cases hhit : context.state.hitAt (.position position) output <;>
                simp only [hhit, ↓reduceIte] <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 200000 in
set_option linter.constructorNameAsVariable false in
theorem probEvent_runDirectDetailedSafeOrdinaryWithCompletionTable_le
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (observe : (OtsSecretIndex → HashOutput) →
      DeferredContext → Nat → alpha → ProbComp Bool)
    (hobserve : ∀ (context : DeferredContext) (fuel : Nat) (value : alpha),
      Pr[fun hit : Bool => hit = true | do
        let base ← sampleOtsHashTable
        observe (completedStartTable context.state base) context fuel value] ≤
        ((fuel + context.state.pending.card : Nat) : ℝ≥0∞) *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹)
    (context : DeferredContext) (fuel : Nat) :
    Pr[fun hit : Bool => hit = true |
        runDirectDetailedSafeOrdinaryWithCompletionTable observe context fuel computation] ≤
      ((fuel + context.state.pending.card : Nat) : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      rw [runDirectDetailedSafeOrdinaryWithCompletionTable_pure]
      exact hobserve context fuel value
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runDirectDetailedSafeOrdinaryWithCompletionTable_uniform_query_bind]
          exact probEvent_bind_le_of_forall_le fun output _ => ih output context fuel
      | hashOutput =>
          rw [runDirectDetailedSafeOrdinaryWithCompletionTable_hashOutput_query_bind]
          exact probEvent_bind_le_of_forall_le fun output _ => ih output context fuel
      | ensure coordinate =>
          rw [runDirectDetailedSafeOrdinaryWithCompletionTable_ensure_query_bind]
          simpa only [LazyRevealProbe.State.pending_card_ensure] using
            ih () { context with state := context.state.ensure coordinate } fuel
      | probe coordinate candidate =>
          rw [runDirectDetailedSafeOrdinaryWithCompletionTable_probe_query_bind]
          cases fuel with
          | zero => simp
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · simp only [hrevealed, ↓reduceIte]
                refine (ih () context remaining).trans ?_
                have hnat : remaining + context.state.pending.card ≤
                    remaining + 1 + context.state.pending.card := by omega
                exact mul_le_mul_of_nonneg_right (by exact_mod_cast hnat) zero_le
              · simp only [hrevealed, ↓reduceIte]
                refine (ih ()
                  { context with state := context.state.addPending coordinate candidate }
                  remaining).trans ?_
                have hnat : remaining +
                    (context.state.addPending coordinate candidate).pending.card ≤
                    remaining + 1 + context.state.pending.card := by
                  have := context.state.pending_card_addPending_le coordinate candidate
                  omega
                exact mul_le_mul_of_nonneg_right (by exact_mod_cast hnat) zero_le
      | peek coordinate =>
          rw [runDirectDetailedSafeOrdinaryWithCompletionTable_peek_query_bind]
          exact ih (context.state.values coordinate) context fuel
      | publish coordinate =>
          rw [runDirectDetailedSafeOrdinaryWithCompletionTable_publish_query_bind]
          exact ih () { context with state := context.state.publish coordinate } fuel
      | reveal coordinate =>
          rw [runDirectDetailedSafeOrdinaryWithCompletionTable_reveal_query_bind]
          cases hstate : context.state.values coordinate with
          | some output => exact ih output context fuel
          | none =>
              simp only
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  refine (probEvent_bind_le_probEvent_add
                    (mx := LazyRevealProbe.sampleHashOutput)
                    (my := fun output =>
                      if context.state.hitAt
                          (.chainStart lay tree leafIdx chainIdx) output then
                        pure true
                      else
                        runDirectDetailedSafeOrdinaryWithCompletionTable observe
                          { state := context.state.materialize
                              (.chainStart lay tree leafIdx chainIdx) output
                            values := context.values }
                          fuel (next output))
                    (q := fun hit : Bool => hit = true)
                    (p := context.state.hitAt (.chainStart lay tree leafIdx chainIdx))
                    (ε := ((fuel + (context.state.pendingAway
                      (.chainStart lay tree leafIdx chainIdx)).card : Nat) : ℝ≥0∞) *
                        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ?_).trans ?_
                  · intro output _houtput hmiss
                    simp only [hmiss, ↓reduceIte]
                    simpa only [LazyRevealProbe.State.pending_card_materialize] using
                      ih output
                        { state := context.state.materialize
                            (.chainStart lay tree leafIdx chainIdx) output
                          values := context.values }
                        fuel
                  · refine add_le_add
                      (LazyRevealProbe.probEvent_sampleHashOutput_hitAt_le context.state
                        (.chainStart lay tree leafIdx chainIdx)) le_rfl |>.trans ?_
                    calc
                      ((context.state.pendingAt
                            (.chainStart lay tree leafIdx chainIdx)).card : ℝ≥0∞) *
                            ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
                          ((fuel + (context.state.pendingAway
                            (.chainStart lay tree leafIdx chainIdx)).card : Nat) : ℝ≥0∞) *
                            ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ =
                        (((context.state.pendingAt
                            (.chainStart lay tree leafIdx chainIdx)).card + fuel +
                            (context.state.pendingAway
                              (.chainStart lay tree leafIdx chainIdx)).card : Nat) : ℝ≥0∞) *
                            ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
                              push_cast
                              ring
                      _ ≤ ((fuel + context.state.pending.card : Nat) : ℝ≥0∞) *
                            ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
                        have hsplit := context.state.pendingAway_card_add_pendingAt_card_le
                          (.chainStart lay tree leafIdx chainIdx)
                        have hnat :
                            (context.state.pendingAt
                              (.chainStart lay tree leafIdx chainIdx)).card + fuel +
                                (context.state.pendingAway
                                  (.chainStart lay tree leafIdx chainIdx)).card ≤
                              fuel + context.state.pending.card := by omega
                        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hnat) zero_le
              | position position =>
                  simp only
                  cases hprivate : context.values position with
                  | some output =>
                      by_cases hhit : context.state.hitAt (.position position) output
                      · simp [hhit]
                      · simp only [hhit, ↓reduceIte]
                        refine (ih output
                          { state := context.state.materialize (.position position) output
                            values := context.values }
                          fuel).trans ?_
                        have hsplit := context.state.pendingAway_card_add_pendingAt_card_le
                          (.position position)
                        have hnat : fuel +
                            (context.state.pendingAway (.position position)).card ≤
                              fuel + context.state.pending.card := by omega
                        simpa only [LazyRevealProbe.State.pending_card_materialize] using
                          mul_le_mul_of_nonneg_right (by exact_mod_cast hnat) zero_le
                  | none =>
                      refine (probEvent_bind_le_probEvent_add
                        (mx := LazyRevealProbe.sampleHashOutput)
                        (my := fun output =>
                          if context.state.hitAt (.position position) output then
                            pure true
                          else
                            runDirectDetailedSafeOrdinaryWithCompletionTable observe
                              { state := context.state.materialize
                                  (.position position) output
                                values := context.values.install position output }
                              fuel (next output))
                        (q := fun hit : Bool => hit = true)
                        (p := context.state.hitAt (.position position))
                        (ε := ((fuel + (context.state.pendingAway
                          (.position position)).card : Nat) : ℝ≥0∞) *
                            ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ?_).trans ?_
                      · intro output _houtput hmiss
                        simp only [hmiss, ↓reduceIte]
                        simpa only [LazyRevealProbe.State.pending_card_materialize] using
                          ih output
                            { state := context.state.materialize
                                (.position position) output
                              values := context.values.install position output }
                            fuel
                      · refine add_le_add
                          (LazyRevealProbe.probEvent_sampleHashOutput_hitAt_le context.state
                            (.position position)) le_rfl |>.trans ?_
                        calc
                          ((context.state.pendingAt (.position position)).card : ℝ≥0∞) *
                                ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
                              ((fuel + (context.state.pendingAway
                                (.position position)).card : Nat) : ℝ≥0∞) *
                                ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ =
                            (((context.state.pendingAt (.position position)).card + fuel +
                                (context.state.pendingAway
                                  (.position position)).card : Nat) : ℝ≥0∞) *
                                ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
                                  push_cast
                                  ring
                          _ ≤ ((fuel + context.state.pending.card : Nat) : ℝ≥0∞) *
                                ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
                            have hsplit := context.state.pendingAway_card_add_pendingAt_card_le
                              (.position position)
                            have hnat :
                                (context.state.pendingAt (.position position)).card + fuel +
                                    (context.state.pendingAway
                                      (.position position)).card ≤
                                  fuel + context.state.pending.card := by omega
                            exact mul_le_mul_of_nonneg_right
                              (by exact_mod_cast hnat) zero_le

theorem probEvent_runDirectDetailedSafeOrdinaryFinalize_le
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (context : DeferredContext) (fuel : Nat) :
    Pr[fun hit : Bool => hit = true |
        runDirectDetailedSafeOrdinaryWithCompletionTable
          (fun _ nextContext _ _ => LazyRevealProbe.finalize nextContext.state)
          context fuel computation] ≤
      ((fuel + context.state.pending.card : Nat) : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  apply probEvent_runDirectDetailedSafeOrdinaryWithCompletionTable_le
  intro nextContext remaining value
  have hdist :
      𝒟[do
        let _base ← sampleOtsHashTable
        LazyRevealProbe.finalize nextContext.state] =
        𝒟[LazyRevealProbe.finalize nextContext.state] :=
    evalDist_sampleOtsHashTable_bind_const _
  refine (OracleComp.probEvent_congr' (fun _ _ => Iff.rfl) hdist).le.trans ?_
  refine (LazyRevealProbe.finalize_probability_le nextContext.state).trans ?_
  have hnat : nextContext.state.pending.card ≤
      remaining + nextContext.state.pending.card := by omega
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hnat) zero_le

def DirectDetailedResult.toRawResult :
    DirectDetailedResult alpha → LazyRevealProbe.RawResult Coordinate alpha
  | .stopped .ordinaryHit => .stopped true
  | .stopped _ => .stopped false
  | .done result => .done result.context.state result.remaining result.value

set_option maxRecDepth 100000 in
set_option maxHeartbeats 200000 in
theorem evalDist_toRawResult_runDirectResolvedDetailedWithCompletionTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat) :
    𝒟[DirectDetailedResult.toRawResult <$>
        runDirectResolvedDetailedWithCompletionTable
          (directDeferredContext state) fuel computation] =
      𝒟[LazyRevealProbe.runRaw state fuel computation] := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure value =>
      rw [runDirectResolvedDetailedWithCompletionTable_pure]
      calc
        _ = 𝒟[sampleOtsHashTable >>= fun _ =>
            (pure (.done state fuel value) :
              ProbComp (LazyRevealProbe.RawResult Coordinate alpha))] := by
          apply congrArg evalDist
          rw [map_bind]
          apply bind_congr
          intro base
          rfl
        _ = 𝒟[pure (.done state fuel value)] :=
          evalDist_sampleOtsHashTable_bind_const _
        _ = _ := rfl
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runDirectResolvedDetailedWithCompletionTable_uniform_query_bind,
            LazyRevealProbe.runRaw_uniform_query_bind, map_bind]
          apply evalDist_bind_congr
          intro output _houtput
          exact ih output state fuel
      | hashOutput =>
          rw [runDirectResolvedDetailedWithCompletionTable_hashOutput_query_bind,
            LazyRevealProbe.runRaw_hashOutput_query_bind, map_bind]
          apply evalDist_bind_congr
          intro output _houtput
          exact ih output state fuel
      | ensure coordinate =>
          rw [runDirectResolvedDetailedWithCompletionTable_ensure_query_bind,
            LazyRevealProbe.runRaw_ensure_query_bind]
          simpa [directDeferredContext, directDeferredValues_ensure] using
            ih () (state.ensure coordinate) fuel
      | probe coordinate candidate =>
          rw [runDirectResolvedDetailedWithCompletionTable_probe_query_bind,
            LazyRevealProbe.runRaw_probe_query_bind]
          cases fuel with
          | zero => simp [DirectDetailedResult.toRawResult]
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ state.revealed
              · simp only [directDeferredContext, hrevealed, ↓reduceIte]
                exact ih () state remaining
              · simp only [directDeferredContext, hrevealed, ↓reduceIte]
                simpa [directDeferredContext, directDeferredValues_addPending] using
                  ih () (state.addPending coordinate candidate) remaining
      | peek coordinate =>
          rw [runDirectResolvedDetailedWithCompletionTable_peek_query_bind,
            LazyRevealProbe.runRaw_peek_query_bind]
          exact ih (state.values coordinate) state fuel
      | publish coordinate =>
          rw [runDirectResolvedDetailedWithCompletionTable_publish_query_bind,
            LazyRevealProbe.runRaw_publish_query_bind]
          simpa [directDeferredContext, directDeferredValues_publish] using
            ih () (state.publish coordinate) fuel
      | reveal coordinate =>
          rw [runDirectResolvedDetailedWithCompletionTable_reveal_query_bind,
            LazyRevealProbe.runRaw_reveal_query_bind]
          cases hstate : state.values coordinate with
          | some output =>
              simp only [directDeferredContext, hstate]
              exact ih output state fuel
          | none =>
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  simp only [directDeferredContext, hstate, map_bind]
                  apply evalDist_bind_congr
                  intro output _houtput
                  by_cases hhit : state.hitAt
                      (.chainStart lay tree leafIdx chainIdx) output
                  · simp [hhit, DirectDetailedResult.toRawResult]
                  · simp only [hhit, ↓reduceIte]
                    have hcontext :
                        { state := state.materialize
                            (.chainStart lay tree leafIdx chainIdx) output
                          values := directDeferredValues state } =
                          directDeferredContext
                            (state.materialize
                              (.chainStart lay tree leafIdx chainIdx) output) := by
                      congr 1
                    rw [hcontext]
                    exact ih output
                      (state.materialize
                        (.chainStart lay tree leafIdx chainIdx) output) fuel
              | position position =>
                  simp only [directDeferredContext, directDeferredValues, hstate,
                    map_bind]
                  apply evalDist_bind_congr
                  intro output _houtput
                  by_cases hhit : state.hitAt (.position position) output
                  · simp [hhit, DirectDetailedResult.toRawResult]
                  · simp only [hhit, ↓reduceIte]
                    have hcontext :
                        { state := state.materialize (.position position) output
                          values := (directDeferredValues state).install position output } =
                          directDeferredContext
                            (state.materialize (.position position) output) := by
                      simp [directDeferredContext,
                        directDeferredValues_materialize_position]
                    rw [hcontext]
                    exact ih output (state.materialize (.position position) output) fuel

theorem finishDirectDetailedSafeOrdinaryFinalize_eq_rawFinish
    (result : DirectDetailedResult alpha) :
    finishDirectDetailedSafeOrdinaryObserve
        (fun _ context _ _ => LazyRevealProbe.finalize context.state) result =
      result.toRawResult.finish := by
  cases result with
  | stopped reason => cases reason <;> rfl
  | done result => rfl

theorem evalDist_runDirectDetailedSafeOrdinaryFinalize_eq_runRawFinish
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat) :
    𝒟[runDirectDetailedSafeOrdinaryWithCompletionTable
        (fun _ context _ _ => LazyRevealProbe.finalize context.state)
        (directDeferredContext state) fuel computation] =
      𝒟[LazyRevealProbe.runRaw state fuel computation >>=
        LazyRevealProbe.RawResult.finish] := by
  unfold runDirectDetailedSafeOrdinaryWithCompletionTable
  calc
    _ = 𝒟[(DirectDetailedResult.toRawResult <$>
          runDirectResolvedDetailedWithCompletionTable
            (directDeferredContext state) fuel computation) >>=
        LazyRevealProbe.RawResult.finish] := by
      apply congrArg evalDist
      rw [map_eq_bind_pure_comp, bind_assoc]
      apply bind_congr
      intro result
      exact finishDirectDetailedSafeOrdinaryFinalize_eq_rawFinish result
    _ = _ := evalDist_bind_eq_of_evalDist_eq
      (evalDist_toRawResult_runDirectResolvedDetailedWithCompletionTable computation state fuel)
      LazyRevealProbe.RawResult.finish

theorem evalDist_runDirectDetailedSafeOrdinaryFinalize_eq_experiment
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (hnotStopped : LazyRevealProbe.RawResult.stopped false ∉ support
      (LazyRevealProbe.runRaw state fuel computation)) :
    𝒟[runDirectDetailedSafeOrdinaryWithCompletionTable
        (fun _ context _ _ => LazyRevealProbe.finalize context.state)
        (directDeferredContext state) fuel computation] =
      𝒟[LazyRevealProbe.experiment state fuel computation] := by
  calc
    _ = 𝒟[LazyRevealProbe.runRaw state fuel computation >>=
        LazyRevealProbe.RawResult.finish] :=
      evalDist_runDirectDetailedSafeOrdinaryFinalize_eq_runRawFinish computation state fuel
    _ = _ :=
      (LazyRevealProbe.evalDist_experiment_eq_runRaw_finish_of_not_stopped_false
        state fuel computation hnotStopped).symm

theorem probEvent_runDirectDetailedSafeOrdinaryFinalize_empty_le
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha) (fuel : Nat) :
    Pr[= true |
        runDirectDetailedSafeOrdinaryWithCompletionTable
          (fun _ context _ _ => LazyRevealProbe.finalize context.state)
          (directDeferredContext
            (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate))
          fuel computation] ≤
      (fuel : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  simpa [directDeferredContext, LazyRevealProbe.State.empty] using
    (probEvent_runDirectDetailedSafeOrdinaryFinalize_le computation
      (directDeferredContext
        (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)) fuel)

theorem fuelExhausted_not_mem_support_runDirectResolvedDetailedFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe fuel) :
    DirectDetailedResult.stopped .fuelExhausted ∉ support
      (runDirectResolvedDetailedFromTable context fuel table computation) := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      simp [runDirectResolvedDetailedFromTable_pure]
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      cases input with
      | uniform n =>
          rw [runDirectResolvedDetailedFromTable_uniform_query_bind, mem_support_bind_iff]
          rintro ⟨output, _houtput, hrest⟩
          exact ih output context fuel
            (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output) hrest
      | hashOutput =>
          rw [runDirectResolvedDetailedFromTable_hashOutput_query_bind, mem_support_bind_iff]
          rintro ⟨output, _houtput, hrest⟩
          exact ih output context fuel
            (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output) hrest
      | ensure coordinate =>
          rw [runDirectResolvedDetailedFromTable_ensure_query_bind]
          exact ih () { context with state := context.state.ensure coordinate } fuel
            (by simpa [LazyRevealProbe.IsProbe] using hbound.2 ())
      | probe coordinate candidate =>
          have hpositive : 0 < fuel := by
            simpa [LazyRevealProbe.IsProbe] using hbound.1
          cases fuel with
          | zero => omega
          | succ remaining =>
              rw [runDirectResolvedDetailedFromTable_probe_query_bind]
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · simp only [hrevealed, ↓reduceIte]
                exact ih () context remaining
                  (by simpa [LazyRevealProbe.IsProbe] using hbound.2 ())
              · simp only [hrevealed, ↓reduceIte]
                exact ih ()
                  { context with
                    state := context.state.addPending coordinate candidate }
                  remaining
                  (by simpa [LazyRevealProbe.IsProbe] using hbound.2 ())
      | peek coordinate =>
          rw [runDirectResolvedDetailedFromTable_peek_query_bind]
          exact ih (context.state.values coordinate) context fuel
            (by simpa [LazyRevealProbe.IsProbe] using
              hbound.2 (context.state.values coordinate))
      | publish coordinate =>
          rw [runDirectResolvedDetailedFromTable_publish_query_bind]
          exact ih () { context with state := context.state.publish coordinate } fuel
            (by simpa [LazyRevealProbe.IsProbe] using hbound.2 ())
      | reveal coordinate =>
          rw [runDirectResolvedDetailedFromTable_reveal_query_bind]
          cases hstate : context.state.values coordinate with
          | some output =>
              exact ih output context fuel
                (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output)
          | none =>
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let output := table ⟨lay, tree, leafIdx, chainIdx⟩
                  by_cases hhit : context.state.hitAt
                      (.chainStart lay tree leafIdx chainIdx) output
                  · simp [output, hhit]
                  · simp only [output, hhit, ↓reduceIte]
                    exact ih output
                      { state := context.state.materialize
                          (.chainStart lay tree leafIdx chainIdx) output
                        values := context.values }
                      fuel
                      (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output)
              | position position =>
                  cases hprivate : context.values position with
                  | some output =>
                      by_cases hhit : context.state.hitAt (.position position) output
                      · simp [hprivate, hhit]
                      · simp only [hprivate, hhit, ↓reduceIte]
                        exact ih output
                          { state := context.state.materialize (.position position) output
                            values := context.values }
                          fuel
                          (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output)
                  | none =>
                      simp only [hprivate, mem_support_bind_iff]
                      rintro ⟨output, _houtput, hrest⟩
                      by_cases hhit : context.state.hitAt (.position position) output
                      · simp [hhit] at hrest
                      · simp only [hhit, ↓reduceIte] at hrest
                        exact ih output
                          { state := context.state.materialize (.position position) output
                            values := context.values.install position output }
                          fuel
                          (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output) hrest

theorem stopped_false_mem_support_runRaw_of_fuelExhausted_detailed
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (hresult : DirectDetailedResult.stopped .fuelExhausted ∈ support
      (runDirectResolvedDetailedWithCompletionTable
        (directDeferredContext state) fuel computation)) :
    LazyRevealProbe.RawResult.stopped false ∈ support
      (LazyRevealProbe.runRaw state fuel computation) := by
  have hmapped : LazyRevealProbe.RawResult.stopped false ∈ support
      (DirectDetailedResult.toRawResult <$>
        runDirectResolvedDetailedWithCompletionTable
          (directDeferredContext state) fuel computation) := by
    rw [support_map]
    exact ⟨.stopped .fuelExhausted, hresult, rfl⟩
  exact (mem_support_iff_of_evalDist_eq
    (evalDist_toRawResult_runDirectResolvedDetailedWithCompletionTable computation state fuel)
    (.stopped false)).mp hmapped

theorem fuelExhausted_not_mem_support_detailed_of_runRaw
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (hnotStopped : LazyRevealProbe.RawResult.stopped false ∉ support
      (LazyRevealProbe.runRaw state fuel computation)) :
    DirectDetailedResult.stopped .fuelExhausted ∉ support
      (runDirectResolvedDetailedWithCompletionTable
        (directDeferredContext state) fuel computation) := by
  intro hresult
  exact hnotStopped
    (stopped_false_mem_support_runRaw_of_fuelExhausted_detailed computation state fuel hresult)

theorem remaining_add_pending_card_le_of_done_runDirectResolvedDetailedFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult alpha)
    (hresult : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable context fuel table computation)) :
    result.remaining + result.context.state.pending.card ≤
      fuel + context.state.pending.card := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      simp [runDirectResolvedDetailedFromTable] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      simp
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runDirectResolvedDetailedFromTable_uniform_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, htail⟩ := hresult
          exact ih output context fuel htail
      | hashOutput =>
          rw [runDirectResolvedDetailedFromTable_hashOutput_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, htail⟩ := hresult
          exact ih output context fuel htail
      | ensure coordinate =>
          rw [runDirectResolvedDetailedFromTable_ensure_query_bind] at hresult
          simpa only [LazyRevealProbe.State.pending_card_ensure] using
            ih () { context with state := context.state.ensure coordinate } fuel hresult
      | probe coordinate candidate =>
          cases fuel with
          | zero => simp [runDirectResolvedDetailedFromTable_probe_query_bind] at hresult
          | succ remaining =>
              rw [runDirectResolvedDetailedFromTable_probe_query_bind] at hresult
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · simp only [hrevealed, ↓reduceIte] at hresult
                have htail := ih () context remaining hresult
                omega
              · simp only [hrevealed, ↓reduceIte] at hresult
                have htail := ih ()
                  { context with
                    state := context.state.addPending coordinate candidate }
                  remaining hresult
                change result.remaining + result.context.state.pending.card ≤
                  remaining + (context.state.addPending coordinate candidate).pending.card at htail
                have hadd := context.state.pending_card_addPending_le coordinate candidate
                omega
      | peek coordinate =>
          rw [runDirectResolvedDetailedFromTable_peek_query_bind] at hresult
          exact ih (context.state.values coordinate) context fuel hresult
      | publish coordinate =>
          rw [runDirectResolvedDetailedFromTable_publish_query_bind] at hresult
          exact ih () { context with state := context.state.publish coordinate } fuel hresult
      | reveal coordinate =>
          rw [runDirectResolvedDetailedFromTable_reveal_query_bind] at hresult
          cases hstate : context.state.values coordinate with
          | some output =>
              simp only [hstate] at hresult
              exact ih output context fuel hresult
          | none =>
              simp only [hstate] at hresult
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let output := table ⟨lay, tree, leafIdx, chainIdx⟩
                  by_cases hhit : context.state.hitAt
                      (.chainStart lay tree leafIdx chainIdx) output
                  · simp [output, hhit] at hresult
                  · simp only [output, hhit, ↓reduceIte] at hresult
                    have htail := ih output
                      { state := context.state.materialize
                          (.chainStart lay tree leafIdx chainIdx) output
                        values := context.values }
                      fuel hresult
                    have haway := context.state.pendingAway_card_add_pendingAt_card_le
                      (.chainStart lay tree leafIdx chainIdx)
                    simp only [LazyRevealProbe.State.pending_card_materialize] at htail
                    omega
              | position position =>
                  cases hprivate : context.values position with
                  | some output =>
                      by_cases hhit : context.state.hitAt (.position position) output
                      · simp [hprivate, hhit] at hresult
                      · simp only [hprivate, hhit, ↓reduceIte] at hresult
                        have htail := ih output
                          { state := context.state.materialize (.position position) output
                            values := context.values }
                          fuel hresult
                        have haway := context.state.pendingAway_card_add_pendingAt_card_le
                          (.position position)
                        simp only [LazyRevealProbe.State.pending_card_materialize] at htail
                        omega
                  | none =>
                      simp only [hprivate, mem_support_bind_iff] at hresult
                      obtain ⟨output, _houtput, htailResult⟩ := hresult
                      by_cases hhit : context.state.hitAt (.position position) output
                      · simp [hhit] at htailResult
                      · simp only [hhit, ↓reduceIte] at htailResult
                        have htail := ih output
                          { state := context.state.materialize (.position position) output
                            values := context.values.install position output }
                          fuel htailResult
                        have haway := context.state.pendingAway_card_add_pendingAt_card_le
                          (.position position)
                        simp only [LazyRevealProbe.State.pending_card_materialize] at htail
                        omega

theorem pending_card_lt_digest_card_of_remaining_add_le
    (context : DeferredContext) (fuel q : Nat)
    (hbudget : fuel + context.state.pending.card ≤ q)
    (hq : q ≤ 2 ^ securityBits) :
    context.state.pending.card < Fintype.card Digest := by
  have hpending : context.state.pending.card ≤ q := by omega
  have hspace : 2 ^ securityBits < Fintype.card Digest := by
    norm_num [securityBits, digestBits]
  exact hpending.trans_lt (hq.trans_lt hspace)

noncomputable def directDetailedSafeOrdinaryTerminalObserve
    (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (fuel : Nat) (value : alpha) : ProbComp Bool :=
  classifyDirectDetailedOrdinaryObserve table (fun _ _ _ => pure false)
    context fuel value

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
theorem probEvent_sampled_directDetailedSafeOrdinaryTerminalObserve_le
    (context : DeferredContext) (fuel : Nat) (value : alpha)
    (hvalid : context.Valid)
    (hcard : context.state.pending.card < Fintype.card Digest) :
    Pr[= true | do
      let base ← sampleOtsHashTable
      directDetailedSafeOrdinaryTerminalObserve
        (completedStartTable context.state base) context fuel value] ≤
      ((fuel + context.state.pending.card : Nat) : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  by_cases hprivate : PrivateStructuralHit context
  · simp [directDetailedSafeOrdinaryTerminalObserve,
      classifyDirectDetailedOrdinaryObserve, hprivate]
  · calc
      _ ≤ Pr[fun base : OtsSecretIndex → HashOutput =>
          MissingChainStartHit (completedStartTable context.state base) context |
            sampleOtsHashTable] := by
        calc
          _ ≤ Pr[= true | sampleOtsHashTable >>= fun base =>
              pure (decide (MissingChainStartHit
                (completedStartTable context.state base) context))] := by
            rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
            apply probEvent_bind_mono
            intro base _hbase
            unfold directDetailedSafeOrdinaryTerminalObserve
            by_cases hcompletable : DeferredCompletable
                (completedStartTable context.state base) context
            · simp [classifyDirectDetailedOrdinaryObserve, hprivate, hcompletable]
            · have hmissing :=
                  privateStructuralHit_or_missingChainStartHit_of_not_completable
                    (completedStartTable context.state base) context hvalid
                    (startTableAgrees_completedStartTable context.state base) hcard
                    hcompletable
              have hmissing' : MissingChainStartHit
                  (completedStartTable context.state base) context :=
                hmissing.resolve_left hprivate
              simp [classifyDirectDetailedOrdinaryObserve, hprivate, hcompletable,
                hmissing']
          _ = _ := by
            rw [show (fun base : OtsSecretIndex → HashOutput =>
                pure (decide (MissingChainStartHit
                  (completedStartTable context.state base) context))) =
                pure ∘ (fun base => decide (MissingChainStartHit
                  (completedStartTable context.state base) context)) by rfl]
            rw [← probEvent_eq_eq_probOutput, probEvent_bind_pure_comp]
            apply OracleComp.probEvent_congr'
            · intro base _hbase
              simp
            · rfl
      _ ≤ (context.state.pending.card : ℝ≥0∞) *
            ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ :=
        probEvent_missingChainStartHit_completedStartTable_le context
      _ ≤ ((fuel + context.state.pending.card : Nat) : ℝ≥0∞) *
            ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
        apply mul_le_mul_of_nonneg_right
        exact_mod_cast Nat.le_add_left context.state.pending.card fuel
        positivity

noncomputable def guardedDirectDetailedSafeOrdinaryTerminalObserve
    (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (fuel : Nat) (value : alpha) : ProbComp Bool := by
  classical
  exact if context.Valid ∧ context.state.pending.card < Fintype.card Digest then
      directDetailedSafeOrdinaryTerminalObserve table context fuel value
    else
      pure false

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
theorem probEvent_sampled_guardedDirectDetailedSafeOrdinaryTerminalObserve_le
    (context : DeferredContext) (fuel : Nat) (value : alpha) :
    Pr[= true | do
      let base ← sampleOtsHashTable
      guardedDirectDetailedSafeOrdinaryTerminalObserve
        (completedStartTable context.state base) context fuel value] ≤
      ((fuel + context.state.pending.card : Nat) : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  by_cases hguard : context.Valid ∧
      context.state.pending.card < Fintype.card Digest
  · simp only [guardedDirectDetailedSafeOrdinaryTerminalObserve, hguard]
    exact probEvent_sampled_directDetailedSafeOrdinaryTerminalObserve_le
      context fuel value hguard.1 hguard.2
  · have hguard' : ¬(context.Valid ∧
        context.state.pending.card < 2 ^ digestBits) := by
      simpa using hguard
    simp [guardedDirectDetailedSafeOrdinaryTerminalObserve, hguard']

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
theorem probEvent_runDirectDetailedSafeOrdinaryGuardedTerminal_le
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (context : DeferredContext) (fuel : Nat) :
    Pr[= true |
        runDirectDetailedSafeOrdinaryWithCompletionTable
          guardedDirectDetailedSafeOrdinaryTerminalObserve
          context fuel computation] ≤
      ((fuel + context.state.pending.card : Nat) : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  rw [← probEvent_eq_eq_probOutput]
  apply probEvent_runDirectDetailedSafeOrdinaryWithCompletionTable_le
  intro nextContext remaining value
  rw [probEvent_eq_eq_probOutput]
  exact probEvent_sampled_guardedDirectDetailedSafeOrdinaryTerminalObserve_le
    nextContext remaining value

end SphincsSecurity.Concrete.OtsProbeSimulation

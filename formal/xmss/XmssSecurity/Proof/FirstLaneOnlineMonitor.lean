import XmssSecurity.Proof.FirstLaneEagerBound
import VCVio.EvalDist.Instances.ErrorT

open OracleComp OracleSpec

namespace XmssSecurity.FirstLaneOracleSimulation

variable {Index : Type} [Fintype Index] [DecidableEq Index]

structure OnlineState (Index : Type) where
  encoding : Option EncodingMonitor.State
  chain : AdaptiveRevealMonitor.State Index
  fuel : Nat

abbrev OnlineM (Index : Type) :=
  StateT (OnlineState Index) (ExceptT Bool ProbComp)

def OnlineState.empty (fuel : Nat) : OnlineState Index :=
  ⟨some EncodingMonitor.State.empty, AdaptiveRevealMonitor.State.empty, fuel⟩

noncomputable def onlineImpl (table : Index → Digest) :
    QueryImpl (World Index) (OnlineM Index) := fun input => StateT.mk fun state =>
  match input with
  | .uniform n => do
      let output ← (liftM (unifSpec.query n) : ExceptT Bool ProbComp _)
      pure (output, state)
  | .encodingQuery epoch =>
      match state.fuel with
      | 0 => throw (RevealProbeOracleSimulation.tableHits state.chain table)
      | remaining + 1 => do
          let output ← (liftM uniformHashOutput : ExceptT Bool ProbComp _)
          match state.encoding with
          | none => pure (output, { state with fuel := remaining })
          | some encoding =>
              match CappedEncodingMonitor.State.applyObserved encoding
                  (.query epoch output) with
              | none => pure (output, { state with encoding := none, fuel := remaining })
              | some (next, hit) =>
                  if hit then throw true
                  else pure (output, { state with encoding := some next, fuel := remaining })
  | .encodingSignAttempt epoch => do
      let output ← (liftM uniformHashOutput : ExceptT Bool ProbComp _)
      match state.encoding with
      | none => pure (output, state)
      | some encoding =>
          match CappedEncodingMonitor.State.applyObserved encoding
              (.sign epoch output) with
          | none => pure (output, { state with encoding := none })
          | some (next, hit) =>
              if hit then throw true
              else pure (output, { state with encoding := some next })
  | .probe index target =>
      match state.fuel with
      | 0 => throw (RevealProbeOracleSimulation.tableHits state.chain table)
      | remaining + 1 =>
          match state.chain.revealed index with
          | some _ => pure ((), { state with fuel := remaining })
          | none => pure ((), { state with
              chain := state.chain.addPending index target
              fuel := remaining })
  | .reveal index =>
      match state.chain.revealed index with
      | some value => pure (value, state)
      | none =>
          let value := table index
          if value ∈ state.chain.pending index then throw true
          else pure (value, { state with chain := state.chain.install index value })

@[simp] theorem onlineImpl_uniform_run (table : Index → Digest) (n : Nat)
    (state : OnlineState Index) :
    ((onlineImpl table (.uniform n)).run state).run =
      (fun output => Except.ok (output, state)) <$>
        (liftM (unifSpec.query n) : ProbComp _) := by
  rfl

@[simp] theorem onlineImpl_encodingQuery_zero_run
    (table : Index → Digest) (epoch : Epoch)
    (encoding : Option EncodingMonitor.State)
    (chain : AdaptiveRevealMonitor.State Index) :
    ((onlineImpl table (.encodingQuery epoch)).run
      ⟨encoding, chain, 0⟩).run =
        pure (.error (RevealProbeOracleSimulation.tableHits chain table)) := by
  rfl

@[simp] theorem onlineImpl_encodingQuery_succ_none_run
    (table : Index → Digest) (epoch : Epoch)
    (chain : AdaptiveRevealMonitor.State Index) (fuel : Nat) :
    ((onlineImpl table (.encodingQuery epoch)).run
      ⟨none, chain, fuel + 1⟩).run =
        (fun output => Except.ok (output, ⟨none, chain, fuel⟩)) <$>
          uniformHashOutput := by
  rfl

@[simp] theorem onlineImpl_encodingQuery_succ_some_run
    (table : Index → Digest) (epoch : Epoch)
    (encoding : EncodingMonitor.State)
    (chain : AdaptiveRevealMonitor.State Index) (fuel : Nat) :
    ((onlineImpl table (.encodingQuery epoch)).run
      ⟨some encoding, chain, fuel + 1⟩).run = (do
        let output ← uniformHashOutput
        pure (match CappedEncodingMonitor.State.applyObserved encoding
            (.query epoch output) with
          | none => Except.ok (output, ⟨none, chain, fuel⟩)
          | some (next, hit) => if hit then Except.error true
              else Except.ok (output, ⟨some next, chain, fuel⟩))) := by
  unfold onlineImpl
  simp only [StateT.run_mk, ExceptT.run_bind,
    ExceptT.run_liftM_eq_map_ok]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  apply bind_congr
  intro output
  cases happly : CappedEncodingMonitor.State.applyObserved encoding
      (.query epoch output) with
  | none => simp
  | some result =>
      rcases result with ⟨next, hit⟩
      cases hit <;> simp [ExceptT.run_throw]

@[simp] theorem onlineImpl_encodingSignAttempt_none_run
    (table : Index → Digest) (epoch : Epoch)
    (chain : AdaptiveRevealMonitor.State Index) (fuel : Nat) :
    ((onlineImpl table (.encodingSignAttempt epoch)).run
      ⟨none, chain, fuel⟩).run =
        (fun output => Except.ok (output, ⟨none, chain, fuel⟩)) <$>
          uniformHashOutput := by
  rfl

@[simp] theorem onlineImpl_encodingSignAttempt_some_run
    (table : Index → Digest) (epoch : Epoch)
    (encoding : EncodingMonitor.State)
    (chain : AdaptiveRevealMonitor.State Index) (fuel : Nat) :
    ((onlineImpl table (.encodingSignAttempt epoch)).run
      ⟨some encoding, chain, fuel⟩).run = (do
        let output ← uniformHashOutput
        pure (match CappedEncodingMonitor.State.applyObserved encoding
            (.sign epoch output) with
          | none => Except.ok (output, ⟨none, chain, fuel⟩)
          | some (next, hit) => if hit then Except.error true
              else Except.ok (output, ⟨some next, chain, fuel⟩))) := by
  unfold onlineImpl
  simp only [StateT.run_mk, ExceptT.run_bind,
    ExceptT.run_liftM_eq_map_ok]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  apply bind_congr
  intro output
  cases happly : CappedEncodingMonitor.State.applyObserved encoding
      (.sign epoch output) with
  | none => simp
  | some result =>
      rcases result with ⟨next, hit⟩
      cases hit <;> simp [ExceptT.run_throw]

@[simp] theorem onlineImpl_probe_zero_run
    (table : Index → Digest) (index : Index) (target : Digest)
    (encoding : Option EncodingMonitor.State)
    (chain : AdaptiveRevealMonitor.State Index) :
    ((onlineImpl table (.probe index target)).run
      ⟨encoding, chain, 0⟩).run =
        pure (.error (RevealProbeOracleSimulation.tableHits chain table)) := by
  rfl

@[simp] theorem onlineImpl_probe_succ_run
    (table : Index → Digest) (index : Index) (target : Digest)
    (encoding : Option EncodingMonitor.State)
    (chain : AdaptiveRevealMonitor.State Index) (fuel : Nat) :
    ((onlineImpl table (.probe index target)).run
      ⟨encoding, chain, fuel + 1⟩).run =
        match chain.revealed index with
        | some _ => pure (.ok ((), ⟨encoding, chain, fuel⟩))
        | none => pure (.ok ((),
            ⟨encoding, chain.addPending index target, fuel⟩)) := by
  rfl

@[simp] theorem onlineImpl_reveal_run
    (table : Index → Digest) (index : Index)
    (encoding : Option EncodingMonitor.State)
    (chain : AdaptiveRevealMonitor.State Index) (fuel : Nat) :
    ((onlineImpl table (.reveal index)).run
      ⟨encoding, chain, fuel⟩).run =
        match chain.revealed index with
        | some value => pure (.ok (value, ⟨encoding, chain, fuel⟩))
        | none => if table index ∈ chain.pending index then pure (.error true)
            else pure (.ok (table index,
              ⟨encoding, chain.install index (table index), fuel⟩)) := by
  rfl

def onlineResultHit (table : Index → Digest) :
    Except Bool (α × OnlineState Index) → Bool
  | .error hit => hit
  | .ok result => RevealProbeOracleSimulation.tableHits result.2.chain table

theorem online_eq_runStructural
    (table : Index → Digest)
    (encodingState : Option EncodingMonitor.State)
    (chainState : AdaptiveRevealMonitor.State Index)
    (fuel : Nat) (computation : OracleComp (World Index) α) :
    onlineResultHit table <$>
        ((simulateQ (onlineImpl table) computation).run
          ⟨encodingState, chainState, fuel⟩).run =
      runStructural table encodingState chainState fuel computation := by
  induction computation using OracleComp.inductionOn generalizing
      encodingState chainState fuel with
  | pure result =>
      simp [onlineResultHit, runStructural]
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
          simp only [ExceptT.run_bind, map_bind]
          rw [onlineImpl_uniform_run]
          simp [runStructural, runEagerQuery, ih]
      | encodingQuery epoch =>
          cases fuel with
          | zero =>
              rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
              simp only [ExceptT.run_bind, map_bind]
              rw [onlineImpl_encodingQuery_zero_run]
              simp [runStructural, runEagerQuery, onlineResultHit]
          | succ remaining =>
              cases encodingState with
              | none =>
                  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
                  simp only [ExceptT.run_bind, map_bind]
                  rw [onlineImpl_encodingQuery_succ_none_run]
                  simp [runStructural, runEagerQuery, ih]
              | some state =>
                  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
                  simp only [ExceptT.run_bind, map_bind]
                  rw [onlineImpl_encodingQuery_succ_some_run]
                  simp only [bind_assoc, pure_bind, runStructural, runEagerQuery,
                    OracleComp.construct_query_bind]
                  apply bind_congr
                  intro output
                  cases happly : CappedEncodingMonitor.State.applyObserved state
                      (.query epoch output) with
                  | none => simp [ih]; rfl
                  | some result =>
                      rcases result with ⟨nextState, hit⟩
                      cases hit with
                      | false => simp [ih]; rfl
                      | true => simp [onlineResultHit]
      | encodingSignAttempt epoch =>
          cases encodingState with
          | none =>
              rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
              simp only [ExceptT.run_bind, map_bind]
              rw [onlineImpl_encodingSignAttempt_none_run]
              simp [runStructural, runEagerQuery, ih]
          | some state =>
              rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
              simp only [ExceptT.run_bind, map_bind]
              rw [onlineImpl_encodingSignAttempt_some_run]
              simp only [bind_assoc, pure_bind, runStructural, runEagerQuery,
                OracleComp.construct_query_bind]
              apply bind_congr
              intro output
              cases happly : CappedEncodingMonitor.State.applyObserved state
                  (.sign epoch output) with
              | none => simp [ih]; rfl
              | some result =>
                  rcases result with ⟨nextState, hit⟩
                  cases hit with
                  | false => simp [ih]; rfl
                  | true => simp [onlineResultHit]
      | probe index target =>
          cases fuel with
          | zero =>
              rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
              simp only [ExceptT.run_bind, map_bind]
              rw [onlineImpl_probe_zero_run]
              simp [runStructural, runEagerQuery, onlineResultHit]
          | succ remaining =>
              cases hrevealed : chainState.revealed index with
              | none =>
                  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
                  simp only [ExceptT.run_bind, map_bind]
                  rw [onlineImpl_probe_succ_run]
                  simp [runStructural, runEagerQuery, hrevealed, ih]
              | some value =>
                  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
                  simp only [ExceptT.run_bind, map_bind]
                  rw [onlineImpl_probe_succ_run]
                  simp [runStructural, runEagerQuery, hrevealed, ih]
      | reveal index =>
          cases hrevealed : chainState.revealed index with
          | some value =>
              rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
              simp only [ExceptT.run_bind, map_bind]
              rw [onlineImpl_reveal_run]
              simp [runStructural, runEagerQuery, hrevealed, ih]
          | none =>
              by_cases hhit : table index ∈ chainState.pending index
              · rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
                simp only [ExceptT.run_bind, map_bind]
                rw [onlineImpl_reveal_run]
                simp [runStructural, runEagerQuery, hrevealed, hhit,
                  onlineResultHit]
              · rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
                simp only [ExceptT.run_bind, map_bind]
                rw [onlineImpl_reveal_run]
                simp [runStructural, runEagerQuery, hrevealed, hhit, ih]

noncomputable def onlineExperiment
    (fuel : Nat) (computation : OracleComp (World Index) α) : ProbComp Bool := do
  let table ← RevealProbeOracleSimulation.eagerTableSample
  onlineResultHit table <$>
    ((simulateQ (onlineImpl table) computation).run
      (OnlineState.empty fuel)).run

theorem onlineExperiment_eq_structuralExperiment
    (fuel : Nat) (computation : OracleComp (World Index) α) :
    onlineExperiment fuel computation =
      structuralExperiment (some EncodingMonitor.State.empty)
        AdaptiveRevealMonitor.State.empty fuel computation := by
  unfold onlineExperiment structuralExperiment OnlineState.empty
  apply bind_congr
  intro table
  exact online_eq_runStructural table (some EncodingMonitor.State.empty)
    AdaptiveRevealMonitor.State.empty fuel computation

theorem onlineExperiment_true_probability_le
    (fuel : Nat) (computation : OracleComp (World Index) α) :
    Pr[(fun hit : Bool => hit = true) | onlineExperiment fuel computation] ≤
      (fuel : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
  rw [onlineExperiment_eq_structuralExperiment]
  exact structuralExperiment_empty_true_probability_le fuel computation

theorem enforced_combinedHit_probability_eq_onlineExperiment
    (fuel : Nat) (computation : OracleComp (World Index) α) :
    Pr[fun result : (Index → Digest) × (α × ActionTrace Index) =>
        CombinedHit result.1
        (enforceHazardTrace fuel result.2.2) |
      eagerExperiment computation] =
    Pr[(fun hit : Bool => hit = true) |
      onlineExperiment fuel (enforceHazardBound fuel computation)] := by
  rw [onlineExperiment_eq_structuralExperiment]
  calc
    _ = Pr[ExperimentHit |
        enforceEagerResult fuel <$> eagerExperiment computation] := by
      rw [probEvent_map]
      rfl
    _ = Pr[ExperimentHit |
        eagerExperiment (enforceHazardBound fuel computation)] := by
      rw [eagerExperiment_enforceHazardBound_eq_map]
    _ = Pr[(fun hit : Bool => hit = true) |
        tracedTableExperiment (enforceHazardBound fuel computation)] := by
      refine (probEvent_congr' (fun result _ =>
        (runObserved_empty_eq_combinedHit result.1 result.2.2).symm)
        rfl).trans ?_
      change Pr[((fun hit : Bool => hit = true) ∘ fun result =>
        runObserved result.1 (some EncodingMonitor.State.empty)
          AdaptiveRevealMonitor.State.empty result.2.2) |
            eagerExperiment (enforceHazardBound fuel computation)] = _
      rw [← probEvent_map,
        map_eagerExperiment_runObserved_eq_tracedTableExperiment]
    _ = Pr[(fun hit : Bool => hit = true) |
        structuralExperiment (some EncodingMonitor.State.empty)
          AdaptiveRevealMonitor.State.empty fuel
            (enforceHazardBound fuel computation)] := by
      apply probEvent_congr' (fun _ _ => Iff.rfl)
      unfold tracedTableExperiment structuralExperiment
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro table
      exact runTracedObserved_eq_runStructural table
        (some EncodingMonitor.State.empty)
        AdaptiveRevealMonitor.State.empty
        (RevealProbeOracleSimulation.stateAgrees_empty table)
        fuel (enforceHazardBound fuel computation)
        (enforceHazardBound_isHazardQueryBoundP fuel computation)

end XmssSecurity.FirstLaneOracleSimulation

import SphincsSecurity.Proof.AdaptiveRevealProbeCharge

namespace SphincsSecurity.AdaptiveRevealProbe

open OracleComp OracleSpec ENNReal

variable {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]

noncomputable def runCharged {α : Type} (table : Coordinate → Digest)
    (state : State Coordinate) (fuel : Nat) (computation : OracleComp (World Coordinate) α) :
    ProbComp (DetailedResult Coordinate α × Nat) :=
  OracleComp.construct
    (C := fun _ => State Coordinate → Nat → ProbComp (DetailedResult Coordinate α × Nat))
    (fun result state _ => pure (.done (tableHits state table) state result, 0))
    (fun input _ next state fuel =>
      match input with
      | .uniform n => do
          let output ← liftM (unifSpec.query n)
          next output state fuel
      | .hashOutput => do
          let output ← liftM sampleHashOutput
          next output state fuel
      | .probe coordinate candidate =>
          match fuel with
          | 0 => pure (.stopped (tableHits state table), 0)
          | remaining + 1 =>
              match state.revealed coordinate with
              | some _ => next () state remaining
              | none => (fun result => (result.1, result.2 + pendingProbeCharge state coordinate candidate)) <$>
                  next () (state.addPending coordinate candidate) remaining
      | .reveal coordinate =>
          match state.revealed coordinate with
          | some value => next value state fuel
          | none =>
              let value := table coordinate
              if value ∈ state.pending coordinate then pure (.stopped true, 0)
              else next value (state.install coordinate value) fuel)
    computation state fuel

theorem runCharged_result_eq_runDetailed {α : Type} (table : Coordinate → Digest)
    (state : State Coordinate) (fuel : Nat) (computation : OracleComp (World Coordinate) α) :
    Prod.fst <$> runCharged table state fuel computation = runDetailed table state fuel computation := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure result => simp only [runCharged, runDetailed, OracleComp.construct_pure, map_pure]
  | query_bind input next ih =>
      rw [runCharged, runDetailed, OracleComp.construct_query_bind, OracleComp.construct_query_bind]
      cases input with
      | uniform n =>
          simp only [map_bind]
          apply bind_congr
          intro output
          exact ih output state fuel
      | hashOutput =>
          simp only [map_bind]
          apply bind_congr
          intro output
          exact ih output state fuel
      | probe coordinate candidate =>
          cases fuel with
          | zero => simp only [map_pure]
          | succ remaining =>
              cases hrevealed : state.revealed coordinate with
              | some value => simpa only [runCharged, runDetailed, hrevealed] using ih () state remaining
              | none =>
                  simpa only [runCharged, runDetailed, hrevealed, Functor.map_map] using
                    ih () (state.addPending coordinate candidate) remaining
      | reveal coordinate =>
          cases hrevealed : state.revealed coordinate with
          | some value => simpa only [runCharged, runDetailed, hrevealed] using ih value state fuel
          | none =>
              simp only [hrevealed]
              split_ifs with hhit
              · simp only [map_pure]
              · exact ih (table coordinate) (state.install coordinate (table coordinate)) fuel

theorem runCharged_cost_le_fuel {α : Type} (table : Coordinate → Digest)
    (state : State Coordinate) (fuel : Nat) (computation : OracleComp (World Coordinate) α) :
    ∀ result ∈ support (runCharged table state fuel computation), result.2 ≤ fuel := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure value =>
      intro result hresult
      simp only [runCharged, OracleComp.construct_pure, support_pure, Set.mem_singleton_iff] at hresult
      rw [hresult]
      exact Nat.zero_le _
  | query_bind input next ih =>
      intro result hresult
      rw [runCharged, OracleComp.construct_query_bind] at hresult
      cases input with
      | uniform n =>
          rw [mem_support_bind_iff] at hresult
          obtain ⟨output, _, hrest⟩ := hresult
          exact ih output state fuel result hrest
      | hashOutput =>
          rw [mem_support_bind_iff] at hresult
          obtain ⟨output, _, hrest⟩ := hresult
          exact ih output state fuel result hrest
      | probe coordinate candidate =>
          cases fuel with
          | zero =>
              simp only [support_pure, Set.mem_singleton_iff] at hresult
              rw [hresult]
          | succ remaining =>
              cases hrevealed : state.revealed coordinate with
              | some value =>
                  simp only [hrevealed] at hresult
                  exact (ih () state remaining result hresult).trans (Nat.le_succ remaining)
              | none =>
                  simp only [hrevealed, support_map, Set.mem_image] at hresult
                  obtain ⟨previous, hprevious, heq⟩ := hresult
                  rw [← heq]
                  exact Nat.add_le_add (ih () (state.addPending coordinate candidate)
                    remaining previous hprevious) (pendingProbeCharge_le_one state coordinate candidate)
      | reveal coordinate =>
          cases hrevealed : state.revealed coordinate with
          | some value =>
              simp only [hrevealed] at hresult
              exact ih value state fuel result hresult
          | none =>
              simp only [hrevealed] at hresult
              split_ifs at hresult with hhit
              · simp only [support_pure, Set.mem_singleton_iff] at hresult
                rw [hresult]
                exact Nat.zero_le _
              · exact ih (table coordinate) (state.install coordinate (table coordinate)) fuel result hresult

set_option maxRecDepth 100000 in
theorem evalDist_sample_applyReveal_result {β : Type} (stopped : β) (state : State Coordinate) (coordinate : Coordinate)
    (hhidden : state.revealed coordinate = none)
    (resume : (Coordinate → Digest) → Digest → State Coordinate → ProbComp β) :
    evalDist (sampleTable >>= fun base =>
      let table := extendTable state base
      let value := table coordinate
      if value ∈ state.pending coordinate then pure stopped
      else resume table value (state.install coordinate value)) =
    evalDist (do
      let value ← ($ᵗ Digest : ProbComp Digest)
      if value ∈ state.pending coordinate then pure stopped
      else sampleTable >>= fun base =>
        (resume (extendTable (state.install coordinate value) base) value
          (state.install coordinate value))) := by
  let continuation := fun (base : Coordinate → Digest) =>
    let table := extendTable state base
    let value := table coordinate
    if value ∈ state.pending coordinate then pure stopped
    else resume table value (state.install coordinate value)
  calc
    _ = evalDist (do
          let value ← ($ᵗ Digest : ProbComp Digest)
          let base ← sampleTable
          if value ∈ state.pending coordinate then pure stopped
          else (resume (extendTable (state.install coordinate value) base)
            value (state.install coordinate value))) := by
      rw [evalDist_sampleTable_eq_bind_update coordinate continuation]
      simp only [evalDist_bind, evalDist_uniformSample]
      congr 1
      funext value
      congr 1
      funext base
      simp only [continuation]
      rw [extendTable_update_eq_install state coordinate value base hhidden]
      have hinstalled :
          extendTable (state.install coordinate value) base coordinate = value := by
        simp [extendTable, State.install]
      rw [hinstalled]
    _ = _ := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro value
      by_cases hhit : value ∈ state.pending coordinate
      · simp only [hhit, ↓reduceIte]
        exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails sampleTable
          (by simp [sampleTable]) (pure stopped)
      · simp [hhit]


noncomputable def chargedExperiment {α : Type} (state : State Coordinate) (fuel : Nat)
    (computation : OracleComp (World Coordinate) α) : ProbComp (DetailedResult Coordinate α × Nat) := do
  let base ← sampleTable
  runCharged (extendTable state base) state fuel computation

theorem chargedExperiment_result_eq {α : Type} (state : State Coordinate) (fuel : Nat)
    (computation : OracleComp (World Coordinate) α) :
    Prod.fst <$> chargedExperiment state fuel computation =
      Prod.snd <$> detailedExperiment state fuel computation := by
  unfold chargedExperiment detailedExperiment
  simp only [map_bind]
  apply bind_congr
  intro base
  simpa only [map_bind, map_pure, bind_pure] using
    runCharged_result_eq_runDetailed (extendTable state base) state fuel computation

theorem chargedExperiment_hit_eq {α : Type} (state : State Coordinate) (fuel : Nat)
    (computation : OracleComp (World Coordinate) α) :
    (fun result => result.1.hit) <$> chargedExperiment state fuel computation =
      experiment state fuel computation := by
  calc
    _ = (fun result : DetailedResult Coordinate α => result.hit) <$>
        (Prod.fst <$> chargedExperiment state fuel computation) := by rw [Functor.map_map]
    _ = _ := by rw [chargedExperiment_result_eq, Functor.map_map, detailedExperiment_hit_eq_experiment]

theorem chargedExperiment_cost_le_fuel {α : Type} (state : State Coordinate) (fuel : Nat)
    (computation : OracleComp (World Coordinate) α) :
    ∀ result ∈ support (chargedExperiment state fuel computation), result.2 ≤ fuel := by
  intro result hresult
  rw [chargedExperiment, mem_support_bind_iff] at hresult
  obtain ⟨base, _, hrun⟩ := hresult
  exact runCharged_cost_le_fuel _ _ _ _ result hrun

end SphincsSecurity.AdaptiveRevealProbe

import XmssSecurity.ExpectedQueryCount
import XmssSecurity.RevealProbeOracleSimulation

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.RevealProbeOracleSimulation

variable {Index : Type} [Fintype Index] [DecidableEq Index]

noncomputable def lazyMonitorImpl :
    QueryImpl (World Index)
      (StateT (AdaptiveRevealMonitor.State Index) ProbComp) :=
  fun input => match input with
  | .uniform n => fun state => do
      let output ← (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))
      pure (output, state)
  | .probe index target => fun state =>
      pure ((), match state.revealed index with
        | some _ => state
        | none => state.addPending index target)
  | .reveal index => fun state =>
      match state.revealed index with
      | some value => pure (value, state)
      | none => do
          let value ← $ᵗ Digest
          pure (value, state.install index value)

omit [Fintype Index] in
@[simp]
theorem lazyMonitorImpl_uniform_run
    (n : Nat) (state : AdaptiveRevealMonitor.State Index) :
    (lazyMonitorImpl (.uniform n)).run state =
      (fun output => (output, state)) <$>
        (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) := by
  rfl

omit [Fintype Index] in
@[simp]
theorem lazyMonitorImpl_probe_run
    (index : Index) (target : Digest)
    (state : AdaptiveRevealMonitor.State Index) :
    (lazyMonitorImpl (.probe index target)).run state =
      pure ((), match state.revealed index with
        | some _ => state
        | none => state.addPending index target) := by
  rfl

omit [Fintype Index] in
@[simp]
theorem lazyMonitorImpl_reveal_run
    (index : Index) (state : AdaptiveRevealMonitor.State Index) :
    (lazyMonitorImpl (.reveal index)).run state =
      match state.revealed index with
      | some value => pure (value, state)
      | none => (fun value => (value, state.install index value)) <$> ($ᵗ Digest) := by
  rfl

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem structuralExperiment_true_probability_le_expectedProbeCount
    (state : AdaptiveRevealMonitor.State Index) (hvalid : StateValid state)
    (fuel : Nat) (computation : OracleComp (World Index) α) :
    Pr[(· = true) | structuralExperiment state fuel computation] ≤
      (expectedSimulatedQueryCount lazyMonitorImpl IsProbeQuery computation state +
          state.pendingCount) *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure result =>
      rw [expectedSimulatedQueryCount_pure, zero_add]
      change Pr[(· = true) |
        (fun base : Index → Digest => tableHits state (extendTable state base)) <$>
          eagerTableSample] ≤ _
      simpa [eagerTableSample] using eagerFinalize_true_probability_le state hvalid
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          let resume := fun (base : Index → Digest) (output : Fin (n + 1)) =>
            runStructural (extendTable state base) state fuel (next output)
          have hswap :
              𝒟[structuralExperiment state fuel
                  (liftM ((World Index).query (.uniform n)) >>= next)] =
                𝒟[(liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>=
                  fun output => eagerTableSample >>= fun base =>
                    resume base output] := by
            change 𝒟[eagerTableSample >>= fun base =>
                (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>=
                  fun output => resume base output] = _
            exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
          have hcount :
              expectedSimulatedQueryCount lazyMonitorImpl IsProbeQuery
                  (liftM ((World Index).query (.uniform n)) >>= next) state =
                ∑' output, Pr[= output |
                    (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))] *
                  expectedSimulatedQueryCount lazyMonitorImpl IsProbeQuery
                    (next output) state := by
            rw [expectedSimulatedQueryCount_query_bind]
            simp only [IsProbeQuery, if_false, zero_add]
            rw [lazyMonitorImpl_uniform_run, tsum_probOutput_map_mul]
          refine (probEvent_congr' (fun _ _ => Iff.rfl) hswap).le.trans ?_
          rw [probEvent_bind_eq_tsum, hcount]
          calc
            ∑' output, Pr[= output |
                  (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))] *
                Pr[(· = true) |
                  eagerTableSample >>= fun base => resume base output] ≤
              ∑' output, Pr[= output |
                  (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))] *
                ((expectedSimulatedQueryCount lazyMonitorImpl IsProbeQuery
                    (next output) state + state.pendingCount) *
                  ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
                    apply ENNReal.tsum_le_tsum
                    intro output
                    exact mul_le_mul' le_rfl
                      (by simpa [structuralExperiment, resume, eagerTableSample] using
                        (ih output state hvalid fuel))
            _ ≤ ((∑' output, Pr[= output |
                    (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))] *
                  expectedSimulatedQueryCount lazyMonitorImpl IsProbeQuery
                    (next output) state) + state.pendingCount) *
                ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
                  simp_rw [← mul_assoc]
                  rw [ENNReal.tsum_mul_right]
                  gcongr
                  simp_rw [mul_add]
                  rw [ENNReal.tsum_add]
                  apply add_le_add_right
                  rw [ENNReal.tsum_mul_right]
                  exact mul_le_of_le_one_left (by finiteness)
                    tsum_probOutput_le_one
      | probe index target =>
          rw [expectedSimulatedQueryCount_query_bind]
          simp only [IsProbeQuery, if_true]
          rw [lazyMonitorImpl_probe_run, tsum_probOutput_pure_mul]
          simp only [structuralExperiment, runStructural,
            OracleComp.construct_query_bind]
          cases fuel with
          | zero =>
              refine (eagerFinalize_true_probability_le state hvalid).trans ?_
              apply mul_le_mul_left
              exact le_add_left le_rfl
          | succ remaining =>
              cases hrevealed : state.revealed index with
              | some value =>
                  refine (ih () state hvalid remaining).trans ?_
                  gcongr
                  exact le_add_left le_rfl
              | none =>
                  refine (ih () (state.addPending index target)
                    (hvalid.addPending index target hrevealed) remaining).trans ?_
                  apply mul_le_mul_left
                  calc
                    expectedSimulatedQueryCount lazyMonitorImpl IsProbeQuery
                          (next ()) (state.addPending index target) +
                        (state.addPending index target).pendingCount ≤
                      expectedSimulatedQueryCount lazyMonitorImpl IsProbeQuery
                          (next ()) (state.addPending index target) +
                        (state.pendingCount + 1) := by
                            gcongr
                            exact_mod_cast
                              state.pendingCount_addPending_le index target
                    _ = 1 +
                          expectedSimulatedQueryCount lazyMonitorImpl IsProbeQuery
                            (next ()) (state.addPending index target) +
                          state.pendingCount := by
                      ac_rfl
      | reveal index =>
          rw [expectedSimulatedQueryCount_query_bind]
          simp only [IsProbeQuery, if_false, zero_add]
          rw [lazyMonitorImpl_reveal_run]
          simp only [structuralExperiment, runStructural,
            OracleComp.construct_query_bind]
          cases hrevealed : state.revealed index with
          | some value =>
              rw [tsum_probOutput_pure_mul]
              change Pr[(· = true) |
                structuralExperiment state fuel (next value)] ≤ _
              exact ih value state hvalid fuel
          | none =>
              rw [tsum_probOutput_map_mul]
              let continuation := fun (base : Index → Digest) =>
                let table := extendTable state base
                let value := table index
                if value ∈ state.pending index then pure true
                else runStructural table (state.install index value) fuel (next value)
              have hrevealDist :
                  𝒟[eagerTableSample >>= continuation] =
                    𝒟[do
                      let value ← $ᵗ Digest
                      let base ← eagerTableSample
                      if value ∈ state.pending index then pure true
                      else
                        runStructural (extendTable (state.install index value) base)
                          (state.install index value) fuel (next value)] := by
                unfold eagerTableSample
                rw [evalDist_uniformTable_eq_bind_update index continuation]
                apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                intro value
                apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                intro base
                simp only [continuation]
                have htable :=
                  extendTable_update_eq_install state index value base hrevealed
                rw [htable]
                have hinstalled :
                    extendTable (state.install index value) base index = value := by
                  simp [extendTable, AdaptiveRevealMonitor.State.install]
                rw [hinstalled]
              change Pr[(· = true) |
                eagerTableSample >>= continuation] ≤ _
              refine (probEvent_congr' (fun _ _ => Iff.rfl) hrevealDist).le.trans ?_
              rw [probEvent_bind_eq_tsum]
              let continuationCost : Digest → ENNReal := fun value =>
                expectedSimulatedQueryCount lazyMonitorImpl IsProbeQuery
                  (next value) (state.install index value)
              calc
                ∑' value, Pr[= value | $ᵗ Digest] *
                    Pr[(· = true) |
                      eagerTableSample >>= fun base =>
                        if value ∈ state.pending index then pure true
                        else runStructural
                          (extendTable (state.install index value) base)
                          (state.install index value) fuel (next value)] ≤
                  ∑' value, ((if value ∈ state.pending index then
                      Pr[= value | $ᵗ Digest] else 0) +
                    Pr[= value | $ᵗ Digest] *
                      ((continuationCost value +
                        (state.install index value).pendingCount) *
                          ((2 ^ digestBits : Nat) : ENNReal)⁻¹)) := by
                            apply ENNReal.tsum_le_tsum
                            intro value
                            by_cases hhit : value ∈ state.pending index
                            · simp [hhit]
                            · simp only [hhit, if_false, zero_add]
                              exact mul_le_mul' le_rfl
                                (by simpa [continuationCost, structuralExperiment,
                                    eagerTableSample] using
                                  (ih value (state.install index value)
                                    (hvalid.install index value) fuel))
                _ ≤ ((state.pending index).card : ENNReal) *
                      ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
                    ((∑' value, Pr[= value | $ᵗ Digest] *
                        continuationCost value) +
                      (state.install index 0).pendingCount) *
                        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
                  rw [ENNReal.tsum_add]
                  apply add_le_add
                  · rw [← probEvent_eq_tsum_ite]
                    exact uniformDigest_mem_finset_le (state.pending index)
                  · simp_rw [← mul_assoc]
                    rw [ENNReal.tsum_mul_right]
                    gcongr
                    calc
                      ∑' value, Pr[= value | $ᵗ Digest] *
                          (continuationCost value +
                            (state.install index value).pendingCount) =
                        (∑' value, Pr[= value | $ᵗ Digest] *
                          continuationCost value) +
                        ∑' value, Pr[= value | $ᵗ Digest] *
                          (state.install index 0).pendingCount := by
                            simp_rw [show ∀ value : Digest,
                              (state.install index value).pendingCount =
                                (state.install index 0).pendingCount from fun _ => rfl,
                              mul_add]
                            rw [ENNReal.tsum_add]
                      _ ≤ (∑' value, Pr[= value | $ᵗ Digest] *
                            continuationCost value) +
                          (state.install index 0).pendingCount := by
                            gcongr
                            rw [ENNReal.tsum_mul_right]
                            exact mul_le_of_le_one_left (by finiteness)
                              tsum_probOutput_le_one
                _ = ((∑' value, Pr[= value | $ᵗ Digest] *
                        continuationCost value) + state.pendingCount) *
                      ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
                  rw [← add_mul]
                  congr 1
                  calc
                    ((state.pending index).card : ENNReal) +
                        ((∑' value, Pr[= value | $ᵗ Digest] *
                            continuationCost value) +
                          (state.install index 0).pendingCount) =
                      (∑' value, Pr[= value | $ᵗ Digest] *
                          continuationCost value) +
                        ((state.install index 0).pendingCount +
                          (state.pending index).card) := by ac_rfl
                    _ = (∑' value, Pr[= value | $ᵗ Digest] *
                            continuationCost value) + state.pendingCount := by
                      congr 1
                      exact_mod_cast state.pendingCount_install_add index 0

theorem eagerExperiment_observedHit_probability_le_expectedProbeCount
    (fuel : Nat) (computation : OracleComp (World Index) α)
    (hbound : computation.IsQueryBoundP IsProbeQuery fuel) :
    Pr[ObservedHit | eagerExperiment computation] ≤
      expectedSimulatedQueryCount lazyMonitorImpl IsProbeQuery computation
          AdaptiveRevealMonitor.State.empty /
        ((2 ^ digestBits : Nat) : ENNReal) := by
  change Pr[(fun result =>
    runObserved result.1 AdaptiveRevealMonitor.State.empty result.2.2 = true) |
      eagerExperiment computation] ≤ _
  change Pr[((fun hit : Bool => hit = true) ∘ fun result =>
    runObserved result.1 AdaptiveRevealMonitor.State.empty result.2.2) |
      eagerExperiment computation] ≤ _
  rw [← probEvent_map,
    map_eagerExperiment_observed_eq_tracedTableExperiment]
  refine (show Pr[(· = true) | tracedTableExperiment computation] ≤
      Pr[(· = true) |
        structuralExperiment AdaptiveRevealMonitor.State.empty fuel computation] by
    unfold tracedTableExperiment structuralExperiment
    apply probEvent_bind_mono
    intro table _htable
    exact runTracedObserved_probability_le_structural table
      AdaptiveRevealMonitor.State.empty (stateAgrees_empty table)
      fuel computation hbound).trans ?_
  simpa [div_eq_mul_inv] using
    structuralExperiment_true_probability_le_expectedProbeCount
      (AdaptiveRevealMonitor.State.empty : AdaptiveRevealMonitor.State Index)
      stateValid_empty fuel computation

noncomputable def expectedEagerObservedProbeCount
    (state : AdaptiveRevealMonitor.State Index)
    (computation : OracleComp (World Index) α) : ENNReal :=
  ∑' result, Pr[= result | do
      let base ← eagerTableSample
      (simulateQ (eagerTraceImpl (extendTable state base)) computation).run] *
    observedProbeCount result.2

theorem tsum_probOutput_mul_congr_evalDist
    (left right : ProbComp α) (cost : α → ENNReal)
    (heq : 𝒟[left] = 𝒟[right]) :
    (∑' result, Pr[= result | left] * cost result) =
      ∑' result, Pr[= result | right] * cost result := by
  apply tsum_congr
  intro result
  rw [probOutput_def, probOutput_def, heq]

theorem weighted_tsum_comm {A B : Type}
    (leftWeight : A → ENNReal) (rightWeight : B → ENNReal)
    (value : A → B → ENNReal) :
    (∑' left, leftWeight left *
      ∑' right, rightWeight right * value left right) =
    ∑' right, rightWeight right *
      ∑' left, leftWeight left * value left right := by
  calc
    _ = ∑' left, ∑' right,
          leftWeight left * (rightWeight right * value left right) := by
      apply tsum_congr
      intro left
      rw [ENNReal.tsum_mul_left]
    _ = ∑' right, ∑' left,
          leftWeight left * (rightWeight right * value left right) :=
      ENNReal.tsum_comm
    _ = _ := by
      apply tsum_congr
      intro right
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro left
      ac_rfl

theorem tsum_probOutput_mul_add_one_le
    (computation : ProbComp α) (cost : α → ENNReal) :
    (∑' result, Pr[= result | computation] * (cost result + 1)) ≤
      (∑' result, Pr[= result | computation] * cost result) + 1 := by
  simp_rw [mul_add]
  rw [ENNReal.tsum_add]
  apply add_le_add_right
  simpa only [mul_one] using (tsum_probOutput_le_one (mx := computation))

theorem expectedEagerObservedProbeCount_addPending
    (state : AdaptiveRevealMonitor.State Index)
    (index : Index) (target : Digest)
    (computation : OracleComp (World Index) α) :
    expectedEagerObservedProbeCount (state.addPending index target) computation =
      expectedEagerObservedProbeCount state computation := by
  simp [expectedEagerObservedProbeCount, extendTable_addPending]

omit [Fintype Index] [DecidableEq Index] in
theorem probFailure_simulate_eagerImpl_eq_zero
    (table : Index → Digest)
    (computation : OracleComp (World Index) α) :
    Pr[⊥ | simulateQ (eagerImpl table) computation] = 0 := by
  induction computation using OracleComp.inductionOn with
  | pure result => simp
  | query_bind input next ih =>
      rw [simulateQ_query_bind]
      cases input with
      | uniform n => simp [eagerImpl]
      | probe index target => simp [eagerImpl]
      | reveal index => simp [eagerImpl]

omit [Fintype Index] [DecidableEq Index] in
theorem probFailure_simulate_eagerTrace_eq_zero
    (table : Index → Digest)
    (computation : OracleComp (World Index) α) :
    Pr[⊥ | (simulateQ (eagerTraceImpl table) computation).run] = 0 := by
  unfold eagerTraceImpl
  rw [QueryImpl.probFailure_run_simulateQ_withTraceAppend]
  exact probFailure_simulate_eagerImpl_eq_zero table computation

theorem expectedEagerExperiment_mass_eq_one
    (state : AdaptiveRevealMonitor.State Index)
    (computation : OracleComp (World Index) α) :
    (∑' result, Pr[= result | do
      let base ← eagerTableSample
      (simulateQ (eagerTraceImpl (extendTable state base)) computation).run]) = 1 := by
  rw [tsum_probOutput_eq_one']
  simp [eagerTableSample]

omit [Fintype Index] [DecidableEq Index] in
theorem simulate_eagerTrace_mass_eq_one
    (table : Index → Digest)
    (computation : OracleComp (World Index) α) :
    (∑' result, Pr[= result |
      (simulateQ (eagerTraceImpl table) computation).run]) = 1 := by
  rw [tsum_probOutput_eq_one']
  exact probFailure_simulate_eagerTrace_eq_zero table computation

theorem tsum_probOutput_mul_add_one_eq_of_mass
    (computation : ProbComp α) (cost : α → ENNReal)
    (hmass : (∑' result, Pr[= result | computation]) = 1) :
    (∑' result, Pr[= result | computation] * (cost result + 1)) =
      (∑' result, Pr[= result | computation] * cost result) + 1 := by
  simp_rw [mul_add]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem expectedEagerObservedProbeCount_eq_expectedSimulatedQueryCount
    (state : AdaptiveRevealMonitor.State Index)
    (computation : OracleComp (World Index) α) :
    expectedEagerObservedProbeCount state computation =
      expectedSimulatedQueryCount lazyMonitorImpl IsProbeQuery computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure result =>
      simp [expectedEagerObservedProbeCount]
  | query_bind input next ih =>
      rw [expectedSimulatedQueryCount_query_bind]
      cases input with
      | uniform n =>
          simp only [IsProbeQuery, if_false, zero_add]
          rw [lazyMonitorImpl_uniform_run, tsum_probOutput_map_mul]
          simp only [expectedEagerObservedProbeCount, simulateQ_query_bind,
            WriterT.run_bind']
          simp [eagerTraceImpl, eagerImpl, traceFragment,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell,
            tsum_probOutput_bind_mul, tsum_probOutput_map_mul]
          classical
          let continuationCost := fun (base : Index → Digest)
              (output : Fin (n + 1)) =>
            ∑' result, Pr[= result |
                (simulateQ (eagerTraceImpl (extendTable state base))
                  (next output)).run] * observedProbeCount result.2
          change (∑ base, Pr[= base | eagerTableSample] *
              ∑ output, ((n : ENNReal) + 1)⁻¹ *
                continuationCost base output) = _
          calc
            _ = ∑ output, ((n : ENNReal) + 1)⁻¹ *
                ∑ base, Pr[= base | eagerTableSample] *
                  continuationCost base output := by
                    simp_rw [Finset.mul_sum]
                    rw [Finset.sum_comm]
                    apply Finset.sum_congr rfl
                    intro output _houtput
                    apply Finset.sum_congr rfl
                    intro base _hbase
                    ac_rfl
            _ = _ := by
              apply Finset.sum_congr rfl
              intro output _houtput
              exact congrArg (fun value => ((n : ENNReal) + 1)⁻¹ * value)
                (by simpa [expectedEagerObservedProbeCount, eagerTraceImpl,
                    tsum_probOutput_bind_mul, continuationCost] using
                  ih output state)
      | probe index target =>
          simp only [IsProbeQuery, if_true]
          rw [lazyMonitorImpl_probe_run, tsum_probOutput_pure_mul]
          simp only [expectedEagerObservedProbeCount, simulateQ_query_bind,
            WriterT.run_bind']
          simp [eagerTraceImpl, eagerImpl, traceFragment,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell,
            tsum_probOutput_bind_mul, tsum_probOutput_map_mul,
            observedProbeCount]
          classical
          let continuationState :=
            match state.revealed index with
            | some _ => state
            | none => state.addPending index target
          let continuationCost := fun (base : Index → Digest) =>
            ∑' result, Pr[= result |
                (simulateQ (eagerTraceImpl (extendTable state base))
                  (next ())).run] * observedProbeCount result.2
          change (∑ base, Pr[= base | eagerTableSample] *
              ∑' result, Pr[= result |
                  (simulateQ (eagerTraceImpl (extendTable state base))
                    (next ())).run] *
                (observedProbeCount result.2 + 1)) = _
          have hcontinuation :
              expectedEagerObservedProbeCount state (next ()) =
                expectedEagerObservedProbeCount continuationState (next ()) := by
            cases hrevealed : state.revealed index with
            | some value => simp [continuationState, hrevealed]
            | none =>
                simpa [continuationState, hrevealed] using
                  (expectedEagerObservedProbeCount_addPending state index
                    target (next ())).symm
          calc
            _ = ∑ base, Pr[= base | eagerTableSample] *
                (continuationCost base + 1) := by
                  apply Finset.sum_congr rfl
                  intro base _hbase
                  congr 1
                  exact tsum_probOutput_mul_add_one_eq_of_mass _ _
                    (simulate_eagerTrace_mass_eq_one
                      (extendTable state base) (next ()))
            _ = (∑ base, Pr[= base | eagerTableSample] *
                    continuationCost base) +
                  ∑ base, Pr[= base | eagerTableSample] := by
                    simp_rw [mul_add, mul_one]
                    rw [Finset.sum_add_distrib]
            _ = expectedEagerObservedProbeCount state (next ()) + 1 := by
                  congr 1
                  · simp [expectedEagerObservedProbeCount,
                      continuationCost, eagerTraceImpl,
                      tsum_probOutput_bind_mul]
                  · simp [eagerTableSample]
                    rw [ENNReal.mul_inv_cancel]
                    · norm_num
                    · finiteness
            _ = expectedEagerObservedProbeCount continuationState (next ()) + 1 := by
                  rw [hcontinuation]
            _ = expectedSimulatedQueryCount lazyMonitorImpl IsProbeQuery
                    (next ()) continuationState + 1 := by
                  exact congrArg (fun value => value + 1)
                    (ih () continuationState)
            _ = 1 + expectedSimulatedQueryCount lazyMonitorImpl IsProbeQuery
                  (next ()) continuationState := by ac_rfl
      | reveal index =>
          simp only [IsProbeQuery, if_false, zero_add]
          rw [lazyMonitorImpl_reveal_run]
          cases hrevealed : state.revealed index with
          | some value =>
              rw [tsum_probOutput_pure_mul]
              simp only [expectedEagerObservedProbeCount, simulateQ_query_bind,
                WriterT.run_bind']
              simp [eagerTraceImpl, eagerImpl, traceFragment,
                QueryImpl.withTraceAppend_apply, WriterT.run_tell,
                tsum_probOutput_bind_mul, tsum_probOutput_map_mul,
                observedProbeCount, extendTable, hrevealed]
              simpa [expectedEagerObservedProbeCount, eagerTraceImpl,
                tsum_probOutput_bind_mul] using
                ih value state
          | none =>
              rw [tsum_probOutput_map_mul]
              let resumeTrace := fun (table : Index → Digest) (value : Digest) =>
                (fun result =>
                  (result.1, .reveal index value :: result.2)) <$>
                    (simulateQ (eagerTraceImpl table) (next value)).run
              have hdist :
                  𝒟[do
                    let base ← eagerTableSample
                    (simulateQ (eagerTraceImpl (extendTable state base))
                      (revealQuery index >>= next)).run] =
                  𝒟[do
                    let value ← $ᵗ Digest
                    let base ← eagerTableSample
                    resumeTrace (extendTable (state.install index value) base)
                      value] := by
                let conditionedContinue :=
                  fun (base : Index → Digest) (value : Digest) =>
                    resumeTrace (extendTable state base) value
                calc
                  𝒟[do
                    let base ← eagerTableSample
                    (simulateQ (eagerTraceImpl (extendTable state base))
                      (revealQuery index >>= next)).run] =
                    𝒟[do
                      let base ← eagerTableSample
                      conditionedContinue base (base index)] := by
                        apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                        intro base
                        rw [simulateQ_bind, WriterT.run_bind',
                          simulate_eagerTrace_revealQuery]
                        simp [conditionedContinue, resumeTrace, extendTable, hrevealed]
                        simp only [map_eq_bind_pure_comp]
                        apply bind_congr
                        intro result
                        rcases result with ⟨result, trace⟩
                        rfl
                  _ = 𝒟[do
                      let value ← $ᵗ Digest
                      let base ← eagerTableSample
                      conditionedContinue (Function.update base index value)
                        value] := by
                    unfold eagerTableSample
                    exact evalDist_uniformTable_bind_coordinate_continuation
                      index conditionedContinue
                  _ = _ := by
                    apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                    intro value
                    apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                    intro base
                    simp only [conditionedContinue]
                    rw [extendTable_update_eq_install state index value base
                      hrevealed]
              unfold expectedEagerObservedProbeCount
              refine (tsum_probOutput_mul_congr_evalDist _ _ _ hdist).trans ?_
              rw [tsum_probOutput_bind_mul]
              apply tsum_congr
              intro value
              congr 1
              rw [tsum_probOutput_bind_mul]
              simpa [resumeTrace, tsum_probOutput_map_mul, observedProbeCount,
                expectedEagerObservedProbeCount, eagerTraceImpl,
                tsum_probOutput_bind_mul] using
                ih value (state.install index value)

end XmssSecurity.RevealProbeOracleSimulation

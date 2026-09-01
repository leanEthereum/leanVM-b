import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalSource

/-!
# Chronological hiddenness of source snapshots

The retained private witness records the revealed-coordinate set at its exact stop. This file
proves that revealed coordinates only grow on the way to such a stop. Combined with canonical
candidate-time contexts, this makes the selected layer-root snapshot hidden.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

set_option maxRecDepth 100000 in
theorem revealed_subset_privateWitness_of_mem_runDirectResolvedWitnessFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (witness : PrivateHitWitness)
    (hresult : DirectWitnessResult.stoppedPrivate witness ∈ support
      (runDirectResolvedWitnessFromTable context fuel table computation)) :
    context.state.revealed ⊆ witness.revealed := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      simp [runDirectResolvedWitnessFromTable] at hresult
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runDirectResolvedWitnessFromTable_uniform_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output context fuel hrest
      | hashOutput =>
          rw [runDirectResolvedWitnessFromTable_hashOutput_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output context fuel hrest
      | ensure coordinate =>
          rw [runDirectResolvedWitnessFromTable_ensure_query_bind] at hresult
          exact ih () { context with state := context.state.ensure coordinate } fuel hresult
      | probe coordinate candidate =>
          rw [runDirectResolvedWitnessFromTable_probe_query_bind] at hresult
          cases fuel with
          | zero => simp at hresult
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · exact ih () context remaining (by simpa [hrevealed] using hresult)
              · exact ih ()
                  { context with state := context.state.addPending coordinate candidate }
                  remaining (by simpa [hrevealed] using hresult)
      | peek coordinate =>
          rw [runDirectResolvedWitnessFromTable_peek_query_bind] at hresult
          exact ih (context.state.values coordinate) context fuel hresult
      | publish coordinate =>
          rw [runDirectResolvedWitnessFromTable_publish_query_bind] at hresult
          have htail := ih ()
            { context with state := context.state.publish coordinate } fuel hresult
          intro other hother
          apply htail
          simp [LazyRevealProbe.State.publish, hother]
      | reveal coordinate =>
          rw [runDirectResolvedWitnessFromTable_reveal_query_bind] at hresult
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
                    exact ih output
                      { state := context.state.materialize
                          (.chainStart lay tree leafIdx chainIdx) output
                        values := context.values }
                      fuel hresult
              | position target =>
                  cases hprivate : context.values target with
                  | some output =>
                      by_cases hhit : context.state.hitAt (.position target) output
                      · simp only [hprivate, hhit, ↓reduceIte] at hresult
                        have hwitness : witness =
                            ⟨target, output, context.state.revealed⟩ := by
                          simpa using hresult
                        subst witness
                        exact Finset.Subset.rfl
                      · simp only [hprivate, hhit, ↓reduceIte] at hresult
                        exact ih output
                          { state := context.state.materialize (.position target) output
                            values := context.values }
                          fuel hresult
                  | none =>
                      simp only [hprivate, mem_support_bind_iff] at hresult
                      obtain ⟨output, _houtput, hrest⟩ := hresult
                      by_cases hhit : context.state.hitAt (.position target) output
                      · simp [hhit] at hrest
                      · simp only [hhit, ↓reduceIte] at hrest
                        exact ih output
                          { state := context.state.materialize (.position target) output
                            values := context.values.install target output }
                          fuel hrest

set_option maxRecDepth 100000 in
theorem revealed_subset_done_of_mem_runDirectResolvedWitnessFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult α)
    (hresult : DirectWitnessResult.done result ∈ support
      (runDirectResolvedWitnessFromTable context fuel table computation)) :
    context.state.revealed ⊆ result.context.state.revealed := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      simp [runDirectResolvedWitnessFromTable] at hresult
      subst result
      exact Finset.Subset.rfl
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runDirectResolvedWitnessFromTable_uniform_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output context fuel hrest
      | hashOutput =>
          rw [runDirectResolvedWitnessFromTable_hashOutput_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output context fuel hrest
      | ensure coordinate =>
          rw [runDirectResolvedWitnessFromTable_ensure_query_bind] at hresult
          exact ih () { context with state := context.state.ensure coordinate } fuel hresult
      | probe coordinate candidate =>
          rw [runDirectResolvedWitnessFromTable_probe_query_bind] at hresult
          cases fuel with
          | zero => simp at hresult
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · exact ih () context remaining (by simpa [hrevealed] using hresult)
              · exact ih ()
                  { context with state := context.state.addPending coordinate candidate }
                  remaining (by simpa [hrevealed] using hresult)
      | peek coordinate =>
          rw [runDirectResolvedWitnessFromTable_peek_query_bind] at hresult
          exact ih (context.state.values coordinate) context fuel hresult
      | publish coordinate =>
          rw [runDirectResolvedWitnessFromTable_publish_query_bind] at hresult
          have htail := ih ()
            { context with state := context.state.publish coordinate } fuel hresult
          intro other hother
          apply htail
          simp [LazyRevealProbe.State.publish, hother]
      | reveal coordinate =>
          rw [runDirectResolvedWitnessFromTable_reveal_query_bind] at hresult
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
                    exact ih output
                      { state := context.state.materialize
                          (.chainStart lay tree leafIdx chainIdx) output
                        values := context.values }
                      fuel hresult
              | position target =>
                  cases hprivate : context.values target with
                  | some output =>
                      by_cases hhit : context.state.hitAt (.position target) output
                      · simp [hprivate, hhit] at hresult
                      · simp only [hprivate, hhit, ↓reduceIte] at hresult
                        exact ih output
                          { state := context.state.materialize (.position target) output
                            values := context.values }
                          fuel hresult
                  | none =>
                      simp only [hprivate, mem_support_bind_iff] at hresult
                      obtain ⟨output, _houtput, hrest⟩ := hresult
                      by_cases hhit : context.state.hitAt (.position target) output
                      · simp [hhit] at hrest
                      · simp only [hhit, ↓reduceIte] at hrest
                        exact ih output
                          { state := context.state.materialize (.position target) output
                            values := context.values.install target output }
                          fuel hrest

set_option maxRecDepth 100000 in
theorem privateValue_eq_privateWitness_of_mem_runDirectResolvedWitnessFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (witness : PrivateHitWitness)
    (position : Position) (output : HashOutput)
    (hvalue : context.values position = some output)
    (hposition : position = witness.position)
    (hresult : DirectWitnessResult.stoppedPrivate witness ∈ support
      (runDirectResolvedWitnessFromTable context fuel table computation)) :
    output = witness.output := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value => simp [runDirectResolvedWitnessFromTable] at hresult
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runDirectResolvedWitnessFromTable_uniform_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨sampled, _hsampled, hrest⟩ := hresult
          exact ih sampled context fuel hvalue hrest
      | hashOutput =>
          rw [runDirectResolvedWitnessFromTable_hashOutput_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨sampled, _hsampled, hrest⟩ := hresult
          exact ih sampled context fuel hvalue hrest
      | ensure coordinate =>
          rw [runDirectResolvedWitnessFromTable_ensure_query_bind] at hresult
          exact ih () { context with state := context.state.ensure coordinate } fuel hvalue hresult
      | probe coordinate candidate =>
          rw [runDirectResolvedWitnessFromTable_probe_query_bind] at hresult
          cases fuel with
          | zero => simp at hresult
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · exact ih () context remaining hvalue (by simpa [hrevealed] using hresult)
              · exact ih ()
                  { context with state := context.state.addPending coordinate candidate }
                  remaining hvalue (by simpa [hrevealed] using hresult)
      | peek coordinate =>
          rw [runDirectResolvedWitnessFromTable_peek_query_bind] at hresult
          exact ih (context.state.values coordinate) context fuel hvalue hresult
      | publish coordinate =>
          rw [runDirectResolvedWitnessFromTable_publish_query_bind] at hresult
          exact ih () { context with state := context.state.publish coordinate } fuel hvalue hresult
      | reveal coordinate =>
          rw [runDirectResolvedWitnessFromTable_reveal_query_bind] at hresult
          cases hstate : context.state.values coordinate with
          | some sampled =>
              simp only [hstate] at hresult
              exact ih sampled context fuel hvalue hresult
          | none =>
              simp only [hstate] at hresult
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let sampled := table ⟨lay, tree, leafIdx, chainIdx⟩
                  by_cases hhit : context.state.hitAt
                      (.chainStart lay tree leafIdx chainIdx) sampled
                  · simp [sampled, hhit] at hresult
                  · simp only [sampled, hhit, ↓reduceIte] at hresult
                    exact ih sampled
                      { state := context.state.materialize
                          (.chainStart lay tree leafIdx chainIdx) sampled
                        values := context.values }
                      fuel hvalue hresult
              | position target =>
                  cases hprivate : context.values target with
                  | some sampled =>
                      by_cases hhit : context.state.hitAt (.position target) sampled
                      · simp only [hprivate, hhit, ↓reduceIte] at hresult
                        have hwitness : witness =
                            ⟨target, sampled, context.state.revealed⟩ := by
                          simpa using hresult
                        subst witness
                        subst position
                        exact Option.some.inj (hvalue.symm.trans hprivate)
                      · simp only [hprivate, hhit, ↓reduceIte] at hresult
                        exact ih sampled
                          { state := context.state.materialize (.position target) sampled
                            values := context.values }
                          fuel hvalue hresult
                  | none =>
                      simp only [hprivate, mem_support_bind_iff] at hresult
                      obtain ⟨sampled, _hsampled, hrest⟩ := hresult
                      by_cases hhit : context.state.hitAt (.position target) sampled
                      · simp [hhit] at hrest
                      · simp only [hhit, ↓reduceIte] at hrest
                        have hne : position ≠ target := by
                          intro heq
                          subst target
                          rw [hprivate] at hvalue
                          simp at hvalue
                        have hnextValue :
                            context.values.install target sampled position = some output := by
                          simpa [DeferredStructuralValues.install,
                            Function.update_of_ne hne] using hvalue
                        exact ih sampled
                          { state := context.state.materialize (.position target) sampled
                            values := context.values.install target sampled }
                          fuel hnextValue hrest

end SphincsSecurity.Concrete.OtsProbeSimulation

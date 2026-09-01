import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalSource

/-!
# Chronological hiddenness of source snapshots

The retained private witness records the revealed-coordinate set at its exact stop. This file
proves that revealed coordinates only grow on the way to such a stop. Combined with canonical
candidate-time contexts, this makes the selected layer-root snapshot hidden.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

theorem PublishedValues.not_revealed_of_value_none
    {context : DeferredContext}
    (hpublished : PublishedValues context.state)
    {coordinate : Coordinate} (hvalue : context.state.values coordinate = none) :
    coordinate ∉ context.state.revealed := by
  intro hrevealed
  exact (hpublished coordinate hrevealed) hvalue

theorem deferredValue_eq_of_positionValue_eq_of_state_none
    {context : DeferredContext} {position : Position} {output : HashOutput}
    (hstate : context.state.values (.position position) = none)
    (hvalue : context.positionValue position = some output) :
    context.values position = some output := by
  simpa [DeferredContext.positionValue, hstate] using hvalue

theorem witnessFirstUsesSomeDelayedLayerRootSnapshot_of_sourceFacts
    {output : PrivateWitnessSnapshotOutput}
    (hroot : WitnessFirstUsesSomeLayerRoot
      (erasePrivateWitnessSnapshotOutput output))
    (hpublished : ∀ snapshot ∈ output.2,
      PublishedValues snapshot.context.state)
    (hsource : ∀ witness (sourceOrdinal : Fin output.2.length),
      output.1 = some witness →
      firstPrivateWitnessOrdinal? witness
          (output.2.map PlannedProbeSnapshot.toProbe) =
        some (snapshotProbeOrdinal sourceOrdinal) →
      (output.2.get sourceOrdinal).context.state.values
          (.position witness.position) = none ∧
        (output.2.get sourceOrdinal).context.positionValue witness.position =
          some witness.output) :
    WitnessFirstUsesSomeDelayedLayerRootSnapshot output := by
  unfold erasePrivateWitnessSnapshotOutput at hroot
  obtain ⟨ordinal, witness, planOrdinal, hwitness, hordinal, hfirst, hrootProbe⟩ := hroot
  let sourceOrdinal : Fin output.2.length :=
    ⟨planOrdinal.val, by simpa only [List.length_map] using planOrdinal.isLt⟩
  have hplanOrdinal : snapshotProbeOrdinal sourceOrdinal = planOrdinal := by
    apply Fin.ext
    rfl
  have hsourceFirst : firstPrivateWitnessOrdinal? witness
      (output.2.map PlannedProbeSnapshot.toProbe) =
        some (snapshotProbeOrdinal sourceOrdinal) := by
    rw [hplanOrdinal]
    exact hfirst
  obtain ⟨hstate, hpositionValue⟩ :=
    hsource witness sourceOrdinal hwitness hsourceFirst
  have hsnapshotPublished := hpublished (output.2.get sourceOrdinal)
    (List.get_mem _ _)
  refine ⟨ordinal, witness, sourceOrdinal, hwitness, ?_, hsourceFirst, ?_, hstate, ?_, ?_⟩
  · exact hordinal ▸ rfl
  · rw [← hplanOrdinal] at hrootProbe
    simpa only [List.get_eq_getElem, List.getElem_map,
      PlannedProbeSnapshot.toProbe, snapshotProbeOrdinal_val] using hrootProbe
  · exact hsnapshotPublished.not_revealed_of_value_none hstate
  · exact deferredValue_eq_of_positionValue_eq_of_state_none hstate hpositionValue

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

theorem publishedValues_of_done_runDirectResolvedWitnessFromTable
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hpreserves : PreservesPublishedValues computation)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (α × SplitHashCache))
    (hpublished : PublishedValues context.state)
    (hresult : DirectWitnessResult.done result ∈ support
      (runDirectResolvedWitnessFromTable context fuel table (computation.run cache))) :
    PublishedValues result.context.state := by
  have hdetailed : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable context fuel table (computation.run cache)) := by
    rw [← map_erase_runDirectResolvedWitnessFromTable (computation.run cache) context fuel table,
      support_map]
    exact ⟨DirectWitnessResult.done result, hresult, rfl⟩
  exact publishedValues_of_done_runDirectResolvedDetailedFromTable computation hpreserves context
    fuel table cache result hpublished hdetailed

def SnapshotsPublished (snapshots : List PlannedProbeSnapshot) : Prop :=
  ∀ snapshot ∈ snapshots, PublishedValues snapshot.context.state

theorem SnapshotsPublished.appendPlannedSnapshot
    {snapshots : List PlannedProbeSnapshot}
    (hsnapshots : SnapshotsPublished snapshots)
    (candidate? : Option Probe) (context : DeferredContext)
    (hpublished : PublishedValues context.state) :
    SnapshotsPublished (appendPlannedSnapshot snapshots candidate? context) := by
  cases candidate? with
  | none => exact hsnapshots
  | some candidate =>
      intro snapshot hsnapshot
      change snapshot ∈ snapshots ++ [⟨candidate, context⟩] at hsnapshot
      simp only [List.mem_append, List.mem_singleton] at hsnapshot
      rcases hsnapshot with hold | rfl
      · exact hsnapshots snapshot hold
      · exact hpublished

theorem snapshotsPublished_of_mem_finishDirectWitnessSnapshotObserve
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp PrivateWitnessSnapshotOutput)
    (snapshots : List PlannedProbeSnapshot) (result : DirectWitnessResult α)
    (hsnapshots : SnapshotsPublished snapshots)
    (hobserve : ∀ resolved output,
      result = .done resolved →
      output ∈ support
        (observe resolved.context resolved.remaining resolved.value snapshots) →
      SnapshotsPublished output.2)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (finishDirectWitnessSnapshotObserve observe snapshots result)) :
    SnapshotsPublished output.2 := by
  cases result with
  | stoppedFuel =>
      simp [finishDirectWitnessSnapshotObserve] at houtput
      subst output
      exact hsnapshots
  | stoppedOrdinary =>
      simp [finishDirectWitnessSnapshotObserve] at houtput
      subst output
      exact hsnapshots
  | stoppedPrivate witness =>
      simp [finishDirectWitnessSnapshotObserve] at houtput
      subst output
      exact hsnapshots
  | done resolved =>
      exact hobserve resolved output rfl (by
        simpa [finishDirectWitnessSnapshotObserve] using houtput)

theorem snapshotsPublished_of_mem_runDirectWitnessSnapshotObserve
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp PrivateWitnessSnapshotOutput)
    (snapshots : List PlannedProbeSnapshot) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hsnapshots : SnapshotsPublished snapshots)
    (hobserve : ∀ result output,
      DirectWitnessResult.done result ∈ support
        (runDirectResolvedWitnessFromTable context fuel table computation) →
      output ∈ support
        (observe result.context result.remaining result.value snapshots) →
      SnapshotsPublished output.2)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (runDirectWitnessSnapshotObserve observe snapshots context fuel table computation)) :
    SnapshotsPublished output.2 := by
  unfold runDirectWitnessSnapshotObserve at houtput
  rw [mem_support_bind_iff] at houtput
  obtain ⟨result, hresult, hfinish⟩ := houtput
  apply snapshotsPublished_of_mem_finishDirectWitnessSnapshotObserve observe snapshots result
    hsnapshots _ output hfinish
  intro resolved nextOutput heq hnext
  subst result
  exact hobserve resolved nextOutput hresult hnext

theorem snapshotsPublished_of_mem_classifyDirectWitnessSnapshotObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp PrivateWitnessSnapshotOutput)
    (context : DeferredContext) (fuel : Nat) (value : α)
    (snapshots : List PlannedProbeSnapshot)
    (hsnapshots : SnapshotsPublished snapshots)
    (hobserve : ∀ output ∈ support (observe context fuel value snapshots),
      SnapshotsPublished output.2)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (classifyDirectWitnessSnapshotObserve table observe context fuel value snapshots)) :
    SnapshotsPublished output.2 := by
  classical
  unfold classifyDirectWitnessSnapshotObserve at houtput
  by_cases hhit : PrivateStructuralHit context
  · simp [hhit] at houtput
    subst output
    exact hsnapshots
  · simp only [hhit, ↓reduceDIte] at houtput
    by_cases hcompletable : DeferredCompletable table context
    · exact hobserve output (by simpa [hcompletable] using houtput)
    · simp [hcompletable] at houtput
      subst output
      exact hsnapshots

theorem snapshotsPublished_of_mem_canonicalizeDirectWitnessSnapshotObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp PrivateWitnessSnapshotOutput)
    (context : DeferredContext) (fuel : Nat) (value : α)
    (snapshots : List PlannedProbeSnapshot)
    (hsnapshots : SnapshotsPublished snapshots)
    (hobserve : PublishedValues context.state →
      ∀ output ∈ support
        (observe (canonicalizeMaterializedValues table context) fuel value snapshots),
      SnapshotsPublished output.2)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (canonicalizeDirectWitnessSnapshotObserve table observe context fuel value snapshots)) :
    SnapshotsPublished output.2 := by
  classical
  let canonical := canonicalizeMaterializedValues table context
  unfold canonicalizeDirectWitnessSnapshotObserve at houtput
  by_cases hhit : PrivateStructuralHit canonical
  · simp [canonical, hhit] at houtput
    subst output
    exact hsnapshots
  · simp only [canonical, hhit, ↓reduceDIte] at houtput
    by_cases hpublished : PublishedValues context.state
    · apply snapshotsPublished_of_mem_classifyDirectWitnessSnapshotObserve table observe canonical
        fuel value snapshots hsnapshots
      · exact hobserve hpublished
      · simpa [hpublished] using houtput
    · simp [hpublished] at houtput
      subst output
      exact hsnapshots

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem snapshotsPublished_of_mem_directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) →
      List PlannedProbeSnapshot → ProbComp PrivateWitnessSnapshotOutput)
    (snapshots : List PlannedProbeSnapshot) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hsnapshots : SnapshotsPublished snapshots)
    (hpublished : PublishedValues context.state)
    (hobserve : ∀ nextContext remaining value nextSnapshots,
      SnapshotsPublished nextSnapshots → PublishedValues nextContext.state →
      ∀ output ∈ support (observe nextContext remaining value nextSnapshots),
        SnapshotsPublished output.2)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve parameter root ftsSecret
        computation observe snapshots context fuel table cache)) :
    SnapshotsPublished output.2 := by
  induction computation using OracleComp.inductionOn generalizing
      snapshots context fuel cache output with
  | pure value =>
      rw [directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve,
        OracleComp.construct_pure] at houtput
      exact hobserve context fuel (value, cache) snapshots hsnapshots hpublished output houtput
  | query_bind query next ih =>
      rw [directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve,
        OracleComp.construct_query_bind] at houtput
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              apply snapshotsPublished_of_mem_runDirectWitnessSnapshotObserve _ snapshots
                context fuel table ((splitUniformImpl n).run cache) hsnapshots _ output houtput
              intro result nextOutput _hresult hnext
              apply snapshotsPublished_of_mem_canonicalizeDirectWitnessSnapshotObserve table _
                result.context result.remaining result.value snapshots hsnapshots _ nextOutput hnext
              intro hnextPublished finalOutput hfinal
              exact ih result.value.1 snapshots
                (canonicalizeMaterializedValues table result.context) result.remaining
                result.value.2 hsnapshots
                hnextPublished.to_canonicalizedMaterializedValues finalOutput hfinal
          | inr input =>
              let plan := purePlanProbingHashQuery parameter input context.state
              let nextSnapshots := appendPlannedSnapshot snapshots
                (rootAwarePlannedCandidate? parameter input context.state) context
              have hnextSnapshots : SnapshotsPublished nextSnapshots :=
                hsnapshots.appendPlannedSnapshot _ context hpublished
              apply snapshotsPublished_of_mem_runDirectWitnessSnapshotObserve _ nextSnapshots
                context fuel table ((probingHashQueryAfterPlan parameter input plan).run cache)
                hnextSnapshots _ output houtput
              intro result nextOutput _hresult hnext
              apply snapshotsPublished_of_mem_canonicalizeDirectWitnessSnapshotObserve table _
                result.context result.remaining result.value nextSnapshots hnextSnapshots _
                nextOutput hnext
              intro hnextPublished finalOutput hfinal
              exact ih result.value.1 nextSnapshots
                (canonicalizeMaterializedValues table result.context) result.remaining
                result.value.2 hnextSnapshots
                hnextPublished.to_canonicalizedMaterializedValues finalOutput hfinal
      | inr message =>
          apply snapshotsPublished_of_mem_runDirectWitnessSnapshotObserve _ snapshots context fuel
            table ((maskedSign parameter root ftsSecret message).run cache) hsnapshots _ output
            houtput
          intro result nextOutput _hresult hnext
          apply snapshotsPublished_of_mem_canonicalizeDirectWitnessSnapshotObserve table _
            result.context result.remaining result.value snapshots hsnapshots _ nextOutput hnext
          intro hnextPublished finalOutput hfinal
          exact ih result.value.1 snapshots
            (canonicalizeMaterializedValues table result.context) result.remaining result.value.2
            hsnapshots hnextPublished.to_canonicalizedMaterializedValues finalOutput hfinal

theorem snapshotsPublished_of_mem_retainedResolvedFinalizationPrivateWitnessSnapshotObserve
    (table : OtsSecretIndex → HashOutput) (root : Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : RetainedRestResult × SplitHashCache)
    (snapshots : List PlannedProbeSnapshot)
    (hsnapshots : SnapshotsPublished snapshots)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (retainedResolvedFinalizationPrivateWitnessSnapshotObserve table root context fuel value
        snapshots)) :
    SnapshotsPublished output.2 := by
  classical
  unfold retainedResolvedFinalizationPrivateWitnessSnapshotObserve at houtput
  by_cases hhit : PrivateStructuralHit context <;> simp [hhit] at houtput <;>
    subst output <;> exact hsnapshots

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem snapshotsPublished_of_mem_granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (snapshots : List PlannedProbeSnapshot)
    (hsnapshots : SnapshotsPublished snapshots)
    (hpublished : PublishedValues context.state)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve adversary parameter
        table ftsSecret context fuel value snapshots)) :
    SnapshotsPublished output.2 := by
  unfold granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve at houtput
  apply snapshotsPublished_of_mem_directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve
    parameter value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
    (retainedResolvedFinalizationPrivateWitnessSnapshotObserve table value.1)
    snapshots context fuel table value.2 hsnapshots hpublished _ output houtput
  intro nextContext remaining nextValue nextSnapshots hnextSnapshots _hnextPublished
    finalOutput hfinal
  exact snapshotsPublished_of_mem_retainedResolvedFinalizationPrivateWitnessSnapshotObserve table
    value.1 nextContext remaining nextValue nextSnapshots hnextSnapshots finalOutput hfinal

end SphincsSecurity.Concrete.OtsProbeSimulation

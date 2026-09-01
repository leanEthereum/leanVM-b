import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationProjection

/-!
# Successful stopped hidden-hit classification

A missing chain-start obstruction cannot disappear along a successful materialized run. This is the
unrecoverable half of the stopped coupling: once it has been separated from a matched private stop,
successful finalization rules it out.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

theorem MissingChainStartHit.ensure
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hmissing : MissingChainStartHit table context) (coordinate : Coordinate) :
    MissingChainStartHit table
      { context with state := context.state.ensure coordinate } := by
  obtain ⟨index, hvalue, hhit⟩ := hmissing
  exact ⟨index, by simpa using hvalue, by simpa using hhit⟩

theorem MissingChainStartHit.publish
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hmissing : MissingChainStartHit table context) (coordinate : Coordinate) :
    MissingChainStartHit table
      { context with state := context.state.publish coordinate } := by
  obtain ⟨index, hvalue, hhit⟩ := hmissing
  exact ⟨index, by simpa using hvalue, by simpa using hhit⟩

theorem MissingChainStartHit.addPending
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hmissing : MissingChainStartHit table context)
    (coordinate : Coordinate) (candidate : Digest) :
    MissingChainStartHit table
      { context with state := context.state.addPending coordinate candidate } := by
  obtain ⟨index, hvalue, hhit⟩ := hmissing
  refine ⟨index, by simpa using hvalue, ?_⟩
  unfold LazyRevealProbe.State.hitAt at hhit ⊢
  rw [LazyRevealProbe.State.mem_pendingAt_iff] at hhit ⊢
  exact Finset.mem_insert_of_mem hhit

theorem missingChainStartHit_materialize_of_ne
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (index : OtsSecretIndex)
    (hvalue : context.state.values index.coordinate = none)
    (hhit : context.state.hitAt index.coordinate (table index))
    (coordinate : Coordinate) (output : HashOutput)
    (hne : coordinate ≠ index.coordinate) :
    MissingChainStartHit table
      { context with state := context.state.materialize coordinate output } := by
  refine ⟨index, ?_, ?_⟩
  · simpa [LazyRevealProbe.State.materialize, Function.update_of_ne hne.symm] using hvalue
  · unfold LazyRevealProbe.State.hitAt at hhit ⊢
    rw [LazyRevealProbe.State.mem_pendingAt_iff] at hhit ⊢
    exact Finset.mem_filter.mpr ⟨hhit, hne.symm⟩

set_option maxRecDepth 100000 in
theorem missingChainStartHit_of_mem_runObservedCleanFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (result : ObservedCleanRunResult α)
    (hmissing : MissingChainStartHit table (directDeferredContext state))
    (hresult : some result ∈ support
      (runObservedCleanFromTable observations state fuel table computation)) :
    result.table = table ∧
      MissingChainStartHit table (directDeferredContext result.state) := by
  induction computation using OracleComp.inductionOn generalizing
      observations state fuel table with
  | pure value =>
      simp [runObservedCleanFromTable] at hresult
      subst result
      exact ⟨rfl, hmissing⟩
  | query_bind query next ih =>
      cases query with
      | uniform n =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output observations state fuel table hmissing hrest
      | hashOutput =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output observations state fuel table hmissing hrest
      | ensure coordinate =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind] at hresult
          exact ih () observations (state.ensure coordinate) fuel table
            (hmissing.ensure coordinate) hresult
      | probe coordinate candidate =>
          rw [runObservedCleanFromTable_probe_query_bind] at hresult
          cases fuel with
          | zero => simp at hresult
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ state.revealed
              · exact ih ()
                  (observations ++ [cleanProbeObservation state coordinate candidate])
                  state remaining table hmissing (by simpa [hrevealed] using hresult)
              · exact ih ()
                  (observations ++ [cleanProbeObservation state coordinate candidate])
                  (state.addPending coordinate candidate) remaining table
                  (hmissing.addPending coordinate candidate)
                  (by simpa [hrevealed] using hresult)
      | peek coordinate =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind] at hresult
          exact ih (state.values coordinate) observations state fuel table hmissing hresult
      | publish coordinate =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind] at hresult
          exact ih () observations (state.publish coordinate) fuel table
            (hmissing.publish coordinate) hresult
      | reveal coordinate =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind] at hresult
          obtain ⟨index, hvalue, hhit⟩ := hmissing
          cases hstored : state.values coordinate with
          | some output =>
              simp only [hstored] at hresult
              exact ih output observations state fuel table ⟨index, hvalue, hhit⟩ hresult
          | none =>
              simp only [hstored] at hresult
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let revealedIndex : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
                  let output := table revealedIndex
                  by_cases hcoordinate :
                      Coordinate.chainStart lay tree leafIdx chainIdx = index.coordinate
                  · have heq : revealedIndex = index :=
                      OtsSecretIndex.coordinate_injective (by
                        simpa [revealedIndex, OtsSecretIndex.coordinate] using hcoordinate)
                    have hhit' : state.hitAt
                        (.chainStart lay tree leafIdx chainIdx) output := by
                      have hhitState : state.hitAt index.coordinate (table index) := by
                        simpa only [directDeferredContext] using hhit
                      simpa [output, heq, hcoordinate] using hhitState
                    have hhitLiteral : state.hitAt
                        (.chainStart lay tree leafIdx chainIdx)
                        (table ⟨lay, tree, leafIdx, chainIdx⟩) := by
                      simpa [output, revealedIndex] using hhit'
                    simp [hhitLiteral] at hresult
                  ·
                    by_cases hrevealedHit : state.hitAt
                        (.chainStart lay tree leafIdx chainIdx) output
                    · have hhitLiteral : state.hitAt
                          (.chainStart lay tree leafIdx chainIdx)
                          (table ⟨lay, tree, leafIdx, chainIdx⟩) := by
                        simpa [output, revealedIndex] using hrevealedHit
                      simp [hhitLiteral] at hresult
                    · have hnotHitLiteral : ¬state.hitAt
                          (.chainStart lay tree leafIdx chainIdx)
                          (table ⟨lay, tree, leafIdx, chainIdx⟩) := by
                        simpa [output, revealedIndex] using hrevealedHit
                      simp only [if_neg hnotHitLiteral] at hresult
                      have hrest : some result ∈ support
                          (runObservedCleanFromTable observations
                            (state.materialize
                              (.chainStart lay tree leafIdx chainIdx) output)
                            fuel table (next output)) := by
                        rw [runObservedCleanFromTable]
                        simpa [output, revealedIndex] using hresult
                      exact ih output observations
                        (state.materialize (.chainStart lay tree leafIdx chainIdx) output)
                        fuel table
                        (missingChainStartHit_materialize_of_ne index hvalue hhit
                          (.chainStart lay tree leafIdx chainIdx) output hcoordinate)
                        hrest
              | position position =>
                  rw [mem_support_bind_iff] at hresult
                  obtain ⟨output, _houtput, hrest⟩ := hresult
                  by_cases hpositionHit : state.hitAt (.position position) output
                  · simp [hpositionHit] at hrest
                  · simp only [hpositionHit, ↓reduceIte] at hrest
                    have hcoordinate : Coordinate.position position ≠ index.coordinate := by
                      cases index
                      simp [OtsSecretIndex.coordinate]
                    exact ih output observations (state.materialize (.position position) output)
                      fuel table
                      (missingChainStartHit_materialize_of_ne index hvalue hhit
                        (.position position) output hcoordinate)
                      hrest

set_option maxRecDepth 100000 in
theorem missingChainStartHit_of_mem_observedMaterializedBoundary
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ObservedCleanRunResult (α × SplitHashCache))
    (hmissing : MissingChainStartHit table (directDeferredContext state))
    (hresult : some result ∈ support
      (observedMaterializedBoundary parameter root ftsSecret computation observations state fuel
        table cache)) :
    result.table = table ∧
      MissingChainStartHit table (directDeferredContext result.state) := by
  induction computation using OracleComp.inductionOn generalizing
      observations state fuel table cache with
  | pure value =>
      simp [observedMaterializedBoundary] at hresult
      obtain rfl := hresult
      exact ⟨rfl, hmissing⟩
  | query_bind query next ih =>
      rw [observedMaterializedBoundary, OracleComp.construct_query_bind] at hresult
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              rw [mem_support_bind_iff] at hresult
              obtain ⟨step?, hstep, hrest⟩ := hresult
              cases step? with
              | none => simp at hrest
              | some step =>
                  have hnext := missingChainStartHit_of_mem_runObservedCleanFromTable
                    ((splitUniformImpl n).run cache) observations state fuel table step hmissing hstep
                  exact ih step.value.1 step.observations step.state step.remaining table
                    step.value.2 hnext.2 (by
                      simpa only [observedMaterializedBoundary] using hrest)
          | inr input =>
              rw [mem_support_bind_iff] at hresult
              obtain ⟨step?, hstep, hrest⟩ := hresult
              cases step? with
              | none => simp at hrest
              | some step =>
                  let publicContext := materializedCanonicalContext table state
                  let plan := purePlanProbingHashQuery parameter input publicContext.state
                  have hnext := missingChainStartHit_of_mem_runObservedCleanFromTable
                    ((probingHashQueryAfterRootAwarePublicPlan parameter input publicContext.state
                      plan).run cache) observations state fuel table step hmissing hstep
                  exact ih step.value.1 step.observations step.state step.remaining table
                    step.value.2 hnext.2 (by
                      simpa only [observedMaterializedBoundary] using hrest)
      | inr message =>
          rw [mem_support_bind_iff] at hresult
          obtain ⟨step?, hstep, hrest⟩ := hresult
          cases step? with
          | none => simp at hrest
          | some step =>
              have hnext := missingChainStartHit_of_mem_runObservedCleanFromTable
                ((maskedSign parameter root ftsSecret message).run cache) observations state fuel
                  table step hmissing hstep
              exact ih step.value.1 step.observations step.state step.remaining table
                step.value.2 hnext.2 (by
                  simpa only [observedMaterializedBoundary] using hrest)

theorem not_missingChainStartHit_of_successful_observedMaterializedBoundary
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ObservedCleanRunResult (α × SplitHashCache))
    (finalResult : ObservedCleanRunResult (α × SplitHashCache))
    (hrun : some result ∈ support
      (observedMaterializedBoundary parameter root ftsSecret computation observations state fuel
        table cache))
    (hfinish : some finalResult ∈ support
      (finishObservedCleanRunFromTable (some result))) :
    ¬MissingChainStartHit table (directDeferredContext state) := by
  intro hmissing
  have hpersist := missingChainStartHit_of_mem_observedMaterializedBoundary parameter root
    ftsSecret computation observations state fuel table cache result hmissing hrun
  have hfinalMissing := hpersist.2
  rw [← hpersist.1] at hfinalMissing
  exact not_missingChainStartHit_of_mem_finishObservedCleanRunFromTable result finalResult hfinish
    hfinalMissing

def CleanProbeObservation.ExistingHiddenChainStartHit
    (observation : CleanProbeObservation) : Prop :=
  observation.ExistingHiddenHit ∧
    ∃ index : OtsSecretIndex, observation.coordinate = index.coordinate

def FirstExistingHiddenChainStartHit
    (observations : List CleanProbeObservation) : Prop :=
  ∃ selected : Fin observations.length,
    (observations.get selected).ExistingHiddenChainStartHit ∧
      ∀ earlier : Fin observations.length,
        earlier.val < selected.val →
          ¬(observations.get earlier).ExistingHiddenHit

theorem FirstExistingHiddenChainStartHit.prefix
    {before after : List CleanProbeObservation}
    (hhit : FirstExistingHiddenChainStartHit before)
    (hprefix : before <+: after) :
    FirstExistingHiddenChainStartHit after := by
  obtain ⟨selected, hselected, hfirst⟩ := hhit
  have hselectedLt : selected.val < after.length :=
    selected.isLt.trans_le hprefix.length_le
  let selected' : Fin after.length := ⟨selected.val, hselectedLt⟩
  refine ⟨selected', ?_, ?_⟩
  · have hget : after[selected.val] = before[selected.val] :=
      (hprefix.getElem selected.isLt).symm
    simpa [selected', hget] using hselected
  · intro earlier hearlier
    have hearlierBefore : earlier.val < before.length := hearlier.trans selected.isLt
    let earlier' : Fin before.length := ⟨earlier.val, hearlierBefore⟩
    have hget : after[earlier.val] = before[earlier.val] :=
      (hprefix.getElem hearlierBefore).symm
    simpa [earlier', hget] using hfirst earlier' (by simpa [selected', earlier'] using hearlier)

theorem firstExistingHiddenHit_selected_unique
    {observations : List CleanProbeObservation}
    {left right : Fin observations.length}
    (hleft : (observations.get left).ExistingHiddenHit ∧
      ∀ earlier : Fin observations.length,
        earlier.val < left.val → ¬(observations.get earlier).ExistingHiddenHit)
    (hright : (observations.get right).ExistingHiddenHit ∧
      ∀ earlier : Fin observations.length,
        earlier.val < right.val → ¬(observations.get earlier).ExistingHiddenHit) :
    left = right := by
  apply Fin.ext
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact hright.2 left hlt hleft.1
  · exact hleft.2 right hgt hright.1

theorem FirstExistingHiddenChainStartHit.selected_eq
    {result : ObservedCleanRunResult α} {ordinal : Nat}
    (hchain : FirstExistingHiddenChainStartHit result.observations)
    (hfirst : FirstExistingHiddenHitAt result ordinal) :
    ∃ selected : Fin result.observations.length,
      selected.val = ordinal ∧
      (result.observations.get selected).ExistingHiddenChainStartHit := by
  obtain ⟨chainSelected, hchainHit, hchainFirst⟩ := hchain
  obtain ⟨selected, hordinal, hselectedHit, hselectedFirst⟩ := hfirst
  have heq : chainSelected = selected := firstExistingHiddenHit_selected_unique
    ⟨hchainHit.1, hchainFirst⟩ ⟨hselectedHit, by
      intro earlier hearlier
      exact hselectedFirst earlier (by omega)⟩
  subst chainSelected
  exact ⟨selected, hordinal, hchainHit⟩

theorem not_firstExistingHiddenRootHitAt_of_firstChainStart
    {result : ObservedCleanRunResult α} {ordinal : Nat}
    (hchain : FirstExistingHiddenChainStartHit result.observations)
    (hfirst : FirstExistingHiddenHitAt result ordinal) :
    ∀ selected : Fin result.observations.length,
      selected.val = ordinal →
      ¬(result.observations.get selected).toProbe.IsLayerRoot := by
  intro selected hselected
  obtain ⟨chainSelected, hchainOrdinal, hchainHit⟩ := hchain.selected_eq hfirst
  have heq : chainSelected = selected := by
    apply Fin.ext
    omega
  subst chainSelected
  rintro ⟨position, hposition, _hroot⟩
  obtain ⟨index, hindex⟩ := hchainHit.2
  change (result.observations.get selected).coordinate = .position position at hposition
  rw [hposition] at hindex
  cases index
  simp [OtsSecretIndex.coordinate] at hindex

def ObservedStoppedCause
    (table : OtsSecretIndex → HashOutput)
    (result : ObservedCleanRunResult α) : Prop :=
  MissingChainStartHit table (directDeferredContext result.state) ∨
    FirstExistingHiddenChainStartHit result.observations

def SnapshotObservedPrefixStoppedRel
    (table : OtsSecretIndex → HashOutput)
    (source : PrivateWitnessSnapshotOutput)
    (observed : Option (ObservedCleanRunResult (α × SplitHashCache))) : Prop :=
  observed = none ∨
    (∃ result aligned, observed = some result ∧
      aligned <+: result.observations ∧
      SnapshotsObservedAt table source.2 aligned ∧
      ∀ witness, source.1 = some witness →
        result.state.values (.position witness.position) = some witness.output) ∨
    ∃ result, observed = some result ∧
      result.table = table ∧
      DoomedResolvedContext table (directDeferredContext result.state) ∧
      ObservedStoppedCause table result

theorem observedStoppedCause_of_mem_observedMaterializedBoundary
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ObservedCleanRunResult (α × SplitHashCache))
    (hcause : MissingChainStartHit table (directDeferredContext state) ∨
      FirstExistingHiddenChainStartHit observations)
    (hresult : some result ∈ support
      (observedMaterializedBoundary parameter root ftsSecret computation observations state fuel
        table cache)) :
    ObservedStoppedCause table result := by
  rcases hcause with hmissing | hchain
  · exact Or.inl
      (missingChainStartHit_of_mem_observedMaterializedBoundary parameter root ftsSecret
        computation observations state fuel table cache result hmissing hresult).2
  · right
    have hprefix := observations_prefix_of_mem_observedMaterializedBoundary parameter root
      ftsSecret computation observations state fuel table cache result hresult
    exact hchain.prefix hprefix

theorem relTriple_any_observedMaterializedBoundary_of_stoppedCause
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (source : ProbComp PrivateWitnessSnapshotOutput)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hdoomed : DoomedResolvedContext table (directDeferredContext state))
    (hcause : MissingChainStartHit table (directDeferredContext state) ∨
      FirstExistingHiddenChainStartHit observations) :
    RelTriple source
      (observedMaterializedBoundary parameter root ftsSecret computation observations state fuel
        table cache)
      (SnapshotObservedPrefixStoppedRel table) := by
  have hbase := relTriple_true source
    (observedMaterializedBoundary parameter root ftsSecret computation observations state fuel
      table cache)
  have hboth :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hbase
  apply relTriple_post_mono hboth
  intro sourceOutput observed hrelation
  cases observed with
  | none => exact Or.inl rfl
  | some result =>
      right
      right
      refine ⟨result, rfl, ?_, ?_, ?_⟩
      · exact (materializedDoomed_of_mem_observedMaterializedBoundary parameter root ftsSecret
          computation observations state fuel table cache result hdoomed hrelation.2).1
      · exact (materializedDoomed_of_mem_observedMaterializedBoundary parameter root ftsSecret
          computation observations state fuel table cache result hdoomed hrelation.2).2
      · exact observedStoppedCause_of_mem_observedMaterializedBoundary parameter root ftsSecret
          computation observations state fuel table cache result hcause hrelation.2

theorem SnapshotObservedPrefixStoppedRel.aligned_of_successful_firstRoot
    {table : OtsSecretIndex → HashOutput}
    {source : PrivateWitnessSnapshotOutput}
    {result : ObservedCleanRunResult (α × SplitHashCache)}
    (hrelation : SnapshotObservedPrefixStoppedRel table source (some result))
    (finalResult : ObservedCleanRunResult (α × SplitHashCache))
    (hfinish : some finalResult ∈ support
      (finishObservedCleanRunFromTable (some result)))
    (ordinal : Nat)
    (hfirst : FirstExistingHiddenHitAt result ordinal)
    (hroot : ∀ selected : Fin result.observations.length,
      selected.val = ordinal →
        (result.observations.get selected).toProbe.IsLayerRoot) :
    ∃ aligned,
      aligned <+: result.observations ∧
      SnapshotsObservedAt table source.2 aligned ∧
      ∀ witness, source.1 = some witness →
        result.state.values (.position witness.position) = some witness.output := by
  rcases hrelation with hnone | haligned | hstopped
  · simp at hnone
  · obtain ⟨other, aligned, hresult, hprefix, hsnapshots, hstored⟩ := haligned
    have heq : other = result := Option.some.inj hresult.symm
    subst other
    exact ⟨aligned, hprefix, hsnapshots, hstored⟩
  · obtain ⟨other, hresult, htable, _hdoomed, hcause⟩ := hstopped
    have heq : other = result := Option.some.inj hresult.symm
    subst other
    rcases hcause with hmissing | hchain
    · rw [← htable] at hmissing
      exact (not_missingChainStartHit_of_mem_finishObservedCleanRunFromTable result finalResult
        hfinish hmissing).elim
    · obtain ⟨selected, hselected, _hhit⟩ := hchain.selected_eq hfirst
      exact (not_firstExistingHiddenRootHitAt_of_firstChainStart hchain hfirst selected hselected
        (hroot selected hselected)).elim

theorem candidateStopCause_of_not_completable
    (table : OtsSecretIndex → HashOutput)
    (candidate : Probe)
    (observations : List CleanProbeObservation)
    (left right : DeferredContext)
    (hcontext : FinalizationContextLE table left right)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hcanonical : CanonicalMaterializedValues table left)
    (hrightMaterialized : right = directDeferredContext right.state)
    (hhidden : candidate.coordinate ∉ right.state.revealed)
    (hnoEarlier : ∀ observation ∈ observations,
      ¬observation.ExistingHiddenHit)
    (hcard : (right.state.addPending candidate.coordinate candidate.candidate).pending.card <
      Fintype.card Digest)
    (hnotCompletable : ¬DeferredCompletable table
      ({ right with state := right.state.addPending candidate.coordinate candidate.candidate } :
        DeferredContext)) :
    PrivateStructuralHit
        ({ left with state := left.state.addPending candidate.coordinate candidate.candidate } :
          DeferredContext) ∨
      MissingChainStartHit table
        ({ right with state := right.state.addPending candidate.coordinate candidate.candidate } :
          DeferredContext) ∨
      FirstExistingHiddenChainStartHit
        (observations ++ [cleanProbeObservation right.state
          candidate.coordinate candidate.candidate]) := by
  let nextRight : DeferredContext :=
    { right with state := right.state.addPending candidate.coordinate candidate.candidate }
  cases hvalue : right.state.values candidate.coordinate with
  | some output =>
      have hhit : truncateHash output = candidate.candidate := by
        by_contra hmiss
        obtain ⟨completion, hcompletion⟩ := hcontext.rightCompletable
        have hresolved : resolvedCompletionValue table right candidate.coordinate = some output := by
          cases hcoordinate : candidate.coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              have hvalue' : right.state.values
                  (.chainStart lay tree leafIdx chainIdx) = some output := by
                simpa [hcoordinate] using hvalue
              have htable := hcontext.view.rightStarts ⟨lay, tree, leafIdx, chainIdx⟩ output
                hvalue'
              simp [resolvedCompletionValue, htable]
          | position position =>
              rw [hrightMaterialized]
              have hvalue' : right.state.values (.position position) = some output := by
                simpa [hcoordinate] using hvalue
              simp [resolvedCompletionValue, directDeferredContext,
                DeferredContext.positionValue, hvalue']
        have hcompletionOutput : completion candidate.coordinate = output :=
          hcompletion.eq_resolvedCompletionValue candidate.coordinate output hresolved
        apply hnotCompletable
        refine ⟨completion, hcompletion.addPending_of_avoids
          candidate.coordinate candidate.candidate ?_⟩
        rw [hcompletionOutput]
        exact hmiss
      cases hcoordinate : candidate.coordinate with
      | chainStart lay tree leafIdx chainIdx =>
          right
          right
          let observation := cleanProbeObservation right.state
            (.chainStart lay tree leafIdx chainIdx) candidate.candidate
          change FirstExistingHiddenChainStartHit (observations ++ [observation])
          have hobservationHit : observation.ExistingHiddenChainStartHit := by
            refine ⟨?_, ⟨⟨lay, tree, leafIdx, chainIdx⟩, ?_⟩⟩
            · refine ⟨?_, output, ?_, hhit⟩
              · have hhidden' : Coordinate.chainStart lay tree leafIdx chainIdx ∉
                    right.state.revealed := by simpa [hcoordinate] using hhidden
                simp [observation, cleanProbeObservation, hhidden']
              · have hvalue' : right.state.values
                    (.chainStart lay tree leafIdx chainIdx) = some output := by
                  simpa [hcoordinate] using hvalue
                simp [observation, cleanProbeObservation, hvalue']
            · rfl
          have hlength : observations.length < (observations ++ [observation]).length := by simp
          let selected : Fin (observations ++ [observation]).length :=
            ⟨observations.length, hlength⟩
          refine ⟨selected, ?_, ?_⟩
          · simpa [selected, observation]
          · intro earlier hearlier
            have hearlierLength : earlier.val < observations.length := by
              simpa [selected] using hearlier
            let before : Fin observations.length := ⟨earlier.val, hearlierLength⟩
            have hbefore := hnoEarlier (observations.get before) (List.get_mem _ _)
            simpa [selected, before, List.getElem_append, hearlierLength] using hbefore
      | position position =>
          left
          have hleftHidden : left.state.values (.position position) = none := by
            apply canonical_value_none_of_not_revealed hcanonical
            intro hleftRevealed
            apply hhidden
            rw [← hrevealed]
            simpa [hcoordinate] using hleftRevealed
          have hrightValue : right.state.values (.position position) = some output := by
            simpa [hcoordinate] using hvalue
          have hprivate : left.values position = some output :=
            hcontext.view.privateValue_of_left_hidden_of_right_materialized position output
              hleftHidden hrightValue
          refine ⟨position, output, ?_, hprivate, ?_⟩
          · simpa [LazyRevealProbe.State.addPending, hcoordinate] using hleftHidden
          · unfold LazyRevealProbe.State.hitAt
            rw [LazyRevealProbe.State.mem_pendingAt_iff]
            simp [LazyRevealProbe.State.addPending, hhit]
  | none =>
      right
      left
      have hvalid : nextRight.Valid := by
        apply hcontext.rightValid.addPending_of_value_none
        exact hvalue
      have hstarts : StartTableAgrees nextRight.state table := by
        exact hcontext.view.rightStarts.addPending candidate.coordinate candidate.candidate
      have hcause := privateStructuralHit_or_missingChainStartHit_of_not_completable table nextRight
        hvalid hstarts hcard hnotCompletable
      exact hcause.resolve_left (not_privateStructuralHit_of_directDeferredContext nextRight (by
        dsimp [nextRight]
        rw [hrightMaterialized]
        simp [directDeferredContext, directDeferredValues_addPending]))

end SphincsSecurity.Concrete.OtsProbeSimulation

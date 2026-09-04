import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootProbe

/-!
# Root-probe coupling

The root-aware run differs from the original run only by additional pending probes. A successful
root-aware execution therefore determines the original execution with the same values, public
state and outputs. The additional pending set may instead stop the root-aware execution, which is
the failure event used by the probability bound.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

structure ProbeStateLE (left right : LazyRevealProbe.State Coordinate) : Prop where
  pending : left.pending ⊆ right.pending
  values : left.values = right.values
  revealed : left.revealed = right.revealed
  ensured : left.ensured = right.ensured
  extraRoot : ∀ coordinate candidate,
    (coordinate, candidate) ∈ right.pending →
      (coordinate, candidate) ∈ left.pending ∨
        (⟨coordinate, candidate⟩ : Probe).IsLayerRoot

theorem ProbeStateLE.refl (state : LazyRevealProbe.State Coordinate) :
    ProbeStateLE state state :=
  ⟨fun _ h => h, rfl, rfl, rfl, fun _ _ h => Or.inl h⟩

theorem ProbeStateLE.trans {left middle right : LazyRevealProbe.State Coordinate}
    (hleft : ProbeStateLE left middle) (hright : ProbeStateLE middle right) :
    ProbeStateLE left right :=
  ⟨fun _ hentry => hright.pending (hleft.pending hentry),
    hleft.values.trans hright.values,
    hleft.revealed.trans hright.revealed,
    hleft.ensured.trans hright.ensured,
    fun coordinate candidate hentry => by
      rcases hright.extraRoot coordinate candidate hentry with hmiddle | hroot
      · exact hleft.extraRoot coordinate candidate hmiddle
      · exact Or.inr hroot⟩

theorem ProbeStateLE.hitAt
    {left right : LazyRevealProbe.State Coordinate}
    (hle : ProbeStateLE left right) (coordinate : Coordinate) (output : HashOutput) :
    left.hitAt coordinate output → right.hitAt coordinate output := by
  intro hhit
  unfold LazyRevealProbe.State.hitAt at hhit ⊢
  rw [LazyRevealProbe.State.mem_pendingAt_iff] at hhit ⊢
  exact hle.pending hhit

theorem ProbeStateLE.not_hitAt_left
    {left right : LazyRevealProbe.State Coordinate}
    (hle : ProbeStateLE left right) (coordinate : Coordinate) (output : HashOutput)
    (hmiss : ¬right.hitAt coordinate output) :
    ¬left.hitAt coordinate output :=
  fun hhit => hmiss (hle.hitAt coordinate output hhit)

theorem ProbeStateLE.chainStart_pending_of_right
    {left right : LazyRevealProbe.State Coordinate}
    (hle : ProbeStateLE left right) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) (candidate : Digest)
    (hentry : (Coordinate.chainStart lay tree leafIdx chainIdx, candidate) ∈ right.pending) :
    (Coordinate.chainStart lay tree leafIdx chainIdx, candidate) ∈ left.pending := by
  rcases hle.extraRoot _ _ hentry with hleft | ⟨position, hcoordinate, _hroot⟩
  · exact hleft
  · cases hcoordinate

theorem ProbeStateLE.addPendingRight
    {left right : LazyRevealProbe.State Coordinate}
    (hle : ProbeStateLE left right) (coordinate : Coordinate) (candidate : Digest)
    (hroot : (⟨coordinate, candidate⟩ : Probe).IsLayerRoot) :
    ProbeStateLE left (right.addPending coordinate candidate) := by
  refine ⟨?_, hle.values, hle.revealed, hle.ensured, ?_⟩
  intro entry hentry
  exact Finset.mem_insert_of_mem (hle.pending hentry)
  intro other otherCandidate hentry
  simp only [LazyRevealProbe.State.addPending, Finset.mem_insert] at hentry
  rcases hentry with hnew | hold
  · have hcoordinate : other = coordinate := congrArg Prod.fst hnew
    have hcandidate : otherCandidate = candidate := congrArg Prod.snd hnew
    subst other
    subst otherCandidate
    exact Or.inr hroot
  · exact hle.extraRoot other otherCandidate hold

theorem ProbeStateLE.addPending
    {left right : LazyRevealProbe.State Coordinate}
    (hle : ProbeStateLE left right) (coordinate : Coordinate) (candidate : Digest) :
    ProbeStateLE (left.addPending coordinate candidate)
      (right.addPending coordinate candidate) := by
  refine ⟨?_, hle.values, hle.revealed, hle.ensured, ?_⟩
  intro entry hentry
  simp only [LazyRevealProbe.State.addPending, Finset.mem_insert] at hentry ⊢
  exact hentry.elim Or.inl (fun hold => Or.inr (hle.pending hold))
  intro other otherCandidate hentry
  simp only [LazyRevealProbe.State.addPending, Finset.mem_insert] at hentry ⊢
  rcases hentry with hnew | hold
  · exact Or.inl (Or.inl hnew)
  · rcases hle.extraRoot other otherCandidate hold with hleft | hroot
    · exact Or.inl (Or.inr hleft)
    · exact Or.inr hroot

theorem ProbeStateLE.ensure
    {left right : LazyRevealProbe.State Coordinate}
    (hle : ProbeStateLE left right) (coordinate : Coordinate) :
    ProbeStateLE (left.ensure coordinate) (right.ensure coordinate) := by
  refine ⟨hle.pending, hle.values, hle.revealed, ?_, hle.extraRoot⟩
  simp [LazyRevealProbe.State.ensure, hle.ensured]

theorem ProbeStateLE.publish
    {left right : LazyRevealProbe.State Coordinate}
    (hle : ProbeStateLE left right) (coordinate : Coordinate) :
    ProbeStateLE (left.publish coordinate) (right.publish coordinate) := by
  refine ⟨hle.pending, hle.values, ?_, hle.ensured, hle.extraRoot⟩
  simp [LazyRevealProbe.State.publish, hle.revealed]

theorem ProbeStateLE.materialize
    {left right : LazyRevealProbe.State Coordinate}
    (hle : ProbeStateLE left right) (coordinate : Coordinate) (output : HashOutput) :
    ProbeStateLE (left.materialize coordinate output)
      (right.materialize coordinate output) := by
  refine ⟨?_, ?_, hle.revealed, ?_, ?_⟩
  · intro entry hentry
    simp only [LazyRevealProbe.State.materialize, LazyRevealProbe.State.pendingAway,
      Finset.mem_filter] at hentry ⊢
    exact ⟨hle.pending hentry.1, hentry.2⟩
  · simp [LazyRevealProbe.State.materialize, hle.values]
  · simp [LazyRevealProbe.State.materialize, hle.ensured]
  · intro other candidate hentry
    simp only [LazyRevealProbe.State.materialize, LazyRevealProbe.State.pendingAway,
      Finset.mem_filter] at hentry ⊢
    rcases hle.extraRoot other candidate hentry.1 with hleft | hroot
    · exact Or.inl ⟨hleft, hentry.2⟩
    · exact Or.inr hroot

theorem ProbeStateLE.clearPending
    {left right : LazyRevealProbe.State Coordinate}
    (hle : ProbeStateLE left right) (coordinate : Coordinate) :
    ProbeStateLE (left.clearPending coordinate) (right.clearPending coordinate) := by
  refine ⟨?_, hle.values, hle.revealed, hle.ensured, ?_⟩
  intro entry hentry
  simp only [LazyRevealProbe.State.clearPending, LazyRevealProbe.State.pendingAway,
    Finset.mem_filter] at hentry ⊢
  exact ⟨hle.pending hentry.1, hentry.2⟩
  intro other candidate hentry
  simp only [LazyRevealProbe.State.clearPending, LazyRevealProbe.State.pendingAway,
    Finset.mem_filter] at hentry ⊢
  rcases hle.extraRoot other candidate hentry.1 with hleft | hroot
  · exact Or.inl ⟨hleft, hentry.2⟩
  · exact Or.inr hroot

theorem ProbeStateLE.complete
    {left right : LazyRevealProbe.State Coordinate}
    (hle : ProbeStateLE left right) (coordinate : Coordinate) (output : HashOutput) :
    ProbeStateLE (left.complete coordinate output) (right.complete coordinate output) := by
  refine ⟨?_, ?_, hle.revealed, hle.ensured, ?_⟩
  · intro entry hentry
    simp only [LazyRevealProbe.State.complete, LazyRevealProbe.State.pendingAway,
      Finset.mem_filter] at hentry ⊢
    exact ⟨hle.pending hentry.1, hentry.2⟩
  · simp [LazyRevealProbe.State.complete, hle.values]
  · intro other candidate hentry
    simp only [LazyRevealProbe.State.complete, LazyRevealProbe.State.pendingAway,
      Finset.mem_filter] at hentry ⊢
    rcases hle.extraRoot other candidate hentry.1 with hleft | hroot
    · exact Or.inl ⟨hleft, hentry.2⟩
    · exact Or.inr hroot

theorem ProbeStateLE.coordinates
    {left right : LazyRevealProbe.State Coordinate}
    (hle : ProbeStateLE left right) : left.coordinates ⊆ right.coordinates := by
  intro coordinate hcoordinate
  unfold LazyRevealProbe.State.coordinates at hcoordinate ⊢
  simp only [Finset.mem_union, Finset.mem_image] at hcoordinate ⊢
  rcases hcoordinate with hensured | ⟨entry, hentry, hvalue⟩
  · left
    rw [← hle.ensured]
    exact hensured
  · right
    exact ⟨entry, hle.pending hentry, hvalue⟩

theorem ProbeStateLE.revealed_iff
    {left right : LazyRevealProbe.State Coordinate}
    (hle : ProbeStateLE left right) (coordinate : Coordinate) :
    coordinate ∈ left.revealed ↔ coordinate ∈ right.revealed := by
  rw [hle.revealed]

def CleanRunProbeLE (left right : Option (CleanRunResult α)) : Prop :=
  match left, right with
  | _, none => True
  | none, some _ => False
  | some leftResult, some rightResult =>
      leftResult.value = rightResult.value ∧
        leftResult.table = rightResult.table ∧
        rightResult.remaining ≤ leftResult.remaining ∧
        ProbeStateLE leftResult.state rightResult.state

theorem CleanRunProbeLE.failure_right (left : Option (CleanRunResult α)) :
    CleanRunProbeLE left none := by
  cases left <;> trivial

theorem CleanRunProbeLE.some_iff
    (leftResult rightResult : CleanRunResult α) :
    CleanRunProbeLE (some leftResult) (some rightResult) ↔
      leftResult.value = rightResult.value ∧
        leftResult.table = rightResult.table ∧
        rightResult.remaining ≤ leftResult.remaining ∧
        ProbeStateLE leftResult.state rightResult.state := by
  rfl

def FinalizeFailureLE
    (left right : Option (LazyRevealProbe.State Coordinate ×
      (OtsSecretIndex → HashOutput))) : Prop :=
  left = none → right = none

def CleanFinishFailureLE
    (left right : Option (CleanRunResult α)) : Prop :=
  left = none → right = none

theorem relTriple_finalize_any_pure_none
    (run : ProbComp (Option (LazyRevealProbe.State Coordinate ×
      (OtsSecretIndex → HashOutput)))) :
    RelTriple run
      (pure none : ProbComp (Option (LazyRevealProbe.State Coordinate ×
        (OtsSecretIndex → HashOutput)))) FinalizeFailureLE := by
  have hbase : RelTriple (run >>= pure) (run >>= fun _ => pure none)
      FinalizeFailureLE := by
    apply relTriple_bind (relTriple_refl run)
    intro left right heq
    subst right
    exact relTriple_pure_pure (by simp [FinalizeFailureLE])
  have hleft : 𝒟[run] = 𝒟[run >>= pure] := by rw [bind_pure]
  have hright : 𝒟[run >>= fun _ => pure none] =
      𝒟[(pure none : ProbComp (Option (LazyRevealProbe.State Coordinate ×
        (OtsSecretIndex → HashOutput))))] :=
    OracleComp.DeferredSampling.evalDist_bind_const_neverFails run
      (probFailure_eq_zero (mx := run)) (pure none)
  exact relTriple_of_evalDist_eq_left hleft
    (relTriple_of_evalDist_eq_right hright hbase)

theorem relTriple_finalize_pure_some_any
    (result : LazyRevealProbe.State Coordinate × (OtsSecretIndex → HashOutput))
    (run : ProbComp (Option (LazyRevealProbe.State Coordinate ×
      (OtsSecretIndex → HashOutput)))) :
    RelTriple
      (pure (some result) : ProbComp (Option (LazyRevealProbe.State Coordinate ×
        (OtsSecretIndex → HashOutput)))) run FinalizeFailureLE := by
  have hbase := relTriple_true
    (pure (some result) : ProbComp (Option (LazyRevealProbe.State Coordinate ×
      (OtsSecretIndex → HashOutput)))) run
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun output => output = some result) (by
        intro output houtput
        simpa using houtput)
  exact relTriple_post_mono hsupported fun left _ hrelation => by
    rw [hrelation.2]
    simp [FinalizeFailureLE]

theorem relTriple_cleanFinish_any_pure_none
    (run : ProbComp (Option (CleanRunResult α))) :
    RelTriple run (pure none : ProbComp (Option (CleanRunResult α)))
      CleanFinishFailureLE := by
  have hbase : RelTriple (run >>= pure) (run >>= fun _ => pure none)
      CleanFinishFailureLE := by
    apply relTriple_bind (relTriple_refl run)
    intro left right heq
    subst right
    exact relTriple_pure_pure (by simp [CleanFinishFailureLE])
  have hleft : 𝒟[run] = 𝒟[run >>= pure] := by rw [bind_pure]
  have hright : 𝒟[run >>= fun _ => pure none] =
      𝒟[(pure none : ProbComp (Option (CleanRunResult α)))] :=
    OracleComp.DeferredSampling.evalDist_bind_const_neverFails run
      (probFailure_eq_zero (mx := run)) (pure none)
  exact relTriple_of_evalDist_eq_left hleft
    (relTriple_of_evalDist_eq_right hright hbase)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem relTriple_finalizeCleanFromTable_probeStateLE :
    ∀ (leftCoordinates rightCoordinates : List Coordinate)
      (leftState rightState : LazyRevealProbe.State Coordinate)
      (table : OtsSecretIndex → HashOutput),
      leftCoordinates.Nodup → rightCoordinates.Nodup →
      (∀ coordinate ∈ leftCoordinates, coordinate ∈ rightCoordinates) →
      ProbeStateLE leftState rightState →
      RelTriple
        (finalizeCleanFromTable leftCoordinates leftState table)
        (finalizeCleanFromTable rightCoordinates rightState table)
        FinalizeFailureLE
  | [], rightCoordinates, leftState, rightState, table,
      _hleftNodup, _hrightNodup, _hsubset, _hstate => by
      simp only [finalizeCleanFromTable]
      exact relTriple_finalize_pure_some_any (leftState, table) _
  | coordinate :: leftRemaining, rightCoordinates, leftState, rightState, table,
      hleftNodup, hrightNodup, hsubset, hstate => by
      have hcoordinate : coordinate ∈ rightCoordinates :=
        hsubset coordinate (by simp)
      apply relTriple_of_evalDist_eq_right
        (evalDist_finalizeCleanFromTable_move_to_front coordinate rightCoordinates rightState
          table hcoordinate).symm
      have hrightMovedNodup : (coordinate :: rightCoordinates.erase coordinate).Nodup :=
        (List.perm_cons_erase hcoordinate).nodup_iff.mp hrightNodup
      have htailSubset : ∀ other ∈ leftRemaining,
          other ∈ rightCoordinates.erase coordinate := by
        intro other hother
        have hne : other ≠ coordinate := by
          intro heq
          subst other
          exact (List.nodup_cons.mp hleftNodup).1 hother
        exact (List.mem_erase_of_ne hne).2 (hsubset other (by simp [hother]))
      have hvalue : leftState.values coordinate = rightState.values coordinate := by
        rw [hstate.values]
      cases hrightValue : rightState.values coordinate with
      | some output =>
          have hleftValue : leftState.values coordinate = some output := by
            rw [hvalue, hrightValue]
          rw [finalizeCleanFromTable_cons_of_some coordinate leftRemaining leftState table output
            hleftValue,
            finalizeCleanFromTable_cons_of_some coordinate
              (rightCoordinates.erase coordinate) rightState table output hrightValue]
          exact relTriple_finalizeCleanFromTable_probeStateLE leftRemaining
            (rightCoordinates.erase coordinate) (leftState.clearPending coordinate)
            (rightState.clearPending coordinate) table (List.nodup_cons.mp hleftNodup).2
            (List.nodup_cons.mp hrightMovedNodup).2 htailSubset
            (hstate.clearPending coordinate)
      | none =>
          have hleftValue : leftState.values coordinate = none := by
            rw [hvalue, hrightValue]
          rw [finalizeCleanFromTable_cons_of_none coordinate leftRemaining leftState table
            hleftValue,
            finalizeCleanFromTable_cons_of_none coordinate
              (rightCoordinates.erase coordinate) rightState table hrightValue]
          apply relTriple_bind
            (relTriple_refl (completionOutputFromTable coordinate table))
          intro leftOutput rightOutput houtput
          subst rightOutput
          by_cases hrightHit : rightState.hitAt coordinate leftOutput
          · simp only [hrightHit, ↓reduceIte]
            exact relTriple_finalize_any_pure_none _
          · have hleftHit : ¬leftState.hitAt coordinate leftOutput :=
              hstate.not_hitAt_left coordinate leftOutput hrightHit
            simp only [hleftHit, hrightHit, ↓reduceIte]
            exact relTriple_finalizeCleanFromTable_probeStateLE leftRemaining
              (rightCoordinates.erase coordinate) (leftState.complete coordinate leftOutput)
              (rightState.complete coordinate leftOutput) table
              (List.nodup_cons.mp hleftNodup).2
              (List.nodup_cons.mp hrightMovedNodup).2 htailSubset
              (hstate.complete coordinate leftOutput)

theorem relTriple_finishCleanRunFromTable_probeLE
    (left right : Option (CleanRunResult α))
    (hrelation : CleanRunProbeLE left right) :
    RelTriple (finishCleanRunFromTable left) (finishCleanRunFromTable right)
      CleanFinishFailureLE := by
  cases right with
  | none => exact relTriple_cleanFinish_any_pure_none _
  | some rightResult =>
      cases left with
      | none => simp [CleanRunProbeLE] at hrelation
      | some leftResult =>
          rcases hrelation with ⟨hvalue, htable, hremaining, hstate⟩
          simp only [finishCleanRunFromTable]
          rw [← htable]
          apply relTriple_bind
            (relTriple_finalizeCleanFromTable_probeStateLE
              leftResult.state.coordinates.toList rightResult.state.coordinates.toList
              leftResult.state rightResult.state leftResult.table
              (Finset.nodup_toList _) (Finset.nodup_toList _)
              (by
                intro coordinate hcoordinate
                have : coordinate ∈ leftResult.state.coordinates := by simpa using hcoordinate
                have := hstate.coordinates this
                simpa using this)
              hstate)
          intro leftFinal rightFinal hfinal
          cases rightFinal with
          | none =>
              cases leftFinal with
              | none => exact relTriple_pure_pure (by simp [CleanFinishFailureLE])
              | some leftFinal => exact relTriple_pure_pure (by simp [CleanFinishFailureLE])
          | some rightFinal =>
              cases leftFinal with
              | none =>
                  have hcontra := hfinal rfl
                  simp at hcontra
              | some leftFinal => exact relTriple_pure_pure (by simp [CleanFinishFailureLE])

theorem relTriple_any_pure_none_clean
    (run : ProbComp (Option (CleanRunResult α))) :
    RelTriple run (pure none : ProbComp (Option (CleanRunResult α))) CleanRunProbeLE := by
  have hbase : RelTriple (run >>= pure) (run >>= fun _ => pure none) CleanRunProbeLE := by
    apply relTriple_bind (relTriple_refl run)
    intro left right heq
    subst right
    exact relTriple_pure_pure (CleanRunProbeLE.failure_right left)
  have hleft : 𝒟[run] = 𝒟[run >>= pure] := by rw [bind_pure]
  have hright : 𝒟[run >>= fun _ => pure none] =
      𝒟[(pure none : ProbComp (Option (CleanRunResult α)))] :=
    OracleComp.DeferredSampling.evalDist_bind_const_neverFails run
      (probFailure_eq_zero (mx := run)) (pure none)
  exact relTriple_of_evalDist_eq_left hleft
    (relTriple_of_evalDist_eq_right hright hbase)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem relTriple_runCleanFromTable_probeStateLE
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (leftState rightState : LazyRevealProbe.State Coordinate)
    (leftFuel rightFuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hstate : ProbeStateLE leftState rightState)
    (hfuel : rightFuel ≤ leftFuel) :
    RelTriple
      (runCleanFromTable leftState leftFuel table computation)
      (runCleanFromTable rightState rightFuel table computation)
      CleanRunProbeLE := by
  induction computation using OracleComp.inductionOn generalizing
      leftState rightState leftFuel rightFuel with
  | pure value =>
      simp only [runCleanFromTable, OracleComp.construct_pure]
      apply relTriple_pure_pure
      exact ⟨rfl, rfl, hfuel, hstate⟩
  | query_bind query next ih =>
      cases query with
      | uniform n =>
          rw [runCleanFromTable_uniform_query_bind, runCleanFromTable_uniform_query_bind]
          apply relTriple_bind
            (relTriple_refl (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
          intro leftOutput rightOutput houtput
          subst rightOutput
          exact ih leftOutput leftState rightState leftFuel rightFuel hstate hfuel
      | hashOutput =>
          rw [runCleanFromTable_hashOutput_query_bind,
            runCleanFromTable_hashOutput_query_bind]
          apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
          intro leftOutput rightOutput houtput
          subst rightOutput
          exact ih leftOutput leftState rightState leftFuel rightFuel hstate hfuel
      | ensure coordinate =>
          rw [runCleanFromTable_ensure_query_bind, runCleanFromTable_ensure_query_bind]
          exact ih () (leftState.ensure coordinate) (rightState.ensure coordinate)
            leftFuel rightFuel (hstate.ensure coordinate) hfuel
      | probe coordinate candidate =>
          rw [runCleanFromTable_probe_query_bind, runCleanFromTable_probe_query_bind]
          cases rightFuel with
          | zero => exact relTriple_any_pure_none_clean _
          | succ rightRemaining =>
              have hleftNe : leftFuel ≠ 0 := by omega
              obtain ⟨leftRemaining, hleftFuel⟩ := Nat.exists_eq_succ_of_ne_zero hleftNe
              subst leftFuel
              have hremaining : rightRemaining ≤ leftRemaining :=
                Nat.le_of_succ_le_succ hfuel
              have hrevealed := hstate.revealed_iff coordinate
              by_cases hleftRevealed : coordinate ∈ leftState.revealed
              · have hrightRevealed : coordinate ∈ rightState.revealed :=
                  hrevealed.mp hleftRevealed
                simp only [hleftRevealed, hrightRevealed, ↓reduceIte]
                exact ih () leftState rightState leftRemaining rightRemaining hstate hremaining
              · have hrightRevealed : coordinate ∉ rightState.revealed := by
                  simpa [hrevealed] using hleftRevealed
                simp only [hleftRevealed, hrightRevealed, ↓reduceIte]
                exact ih () (leftState.addPending coordinate candidate)
                  (rightState.addPending coordinate candidate) leftRemaining rightRemaining
                  (hstate.addPending coordinate candidate) hremaining
      | peek coordinate =>
          rw [runCleanFromTable_peek_query_bind, runCleanFromTable_peek_query_bind]
          have hvalue : leftState.values coordinate = rightState.values coordinate := by
            rw [hstate.values]
          rw [hvalue]
          exact ih (rightState.values coordinate) leftState rightState leftFuel rightFuel
            hstate hfuel
      | publish coordinate =>
          rw [runCleanFromTable_publish_query_bind, runCleanFromTable_publish_query_bind]
          exact ih () (leftState.publish coordinate) (rightState.publish coordinate)
            leftFuel rightFuel (hstate.publish coordinate) hfuel
      | reveal coordinate =>
          rw [runCleanFromTable_reveal_query_bind, runCleanFromTable_reveal_query_bind]
          have hvalue : leftState.values coordinate = rightState.values coordinate := by
            rw [hstate.values]
          cases hrightValue : rightState.values coordinate with
          | some output =>
              have hleftValue : leftState.values coordinate = some output := by
                rw [hvalue, hrightValue]
              simp only [hleftValue]
              exact ih output leftState rightState leftFuel rightFuel hstate hfuel
          | none =>
              have hleftValue : leftState.values coordinate = none := by
                rw [hvalue, hrightValue]
              simp only [hleftValue]
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let output := table ⟨lay, tree, leafIdx, chainIdx⟩
                  by_cases hrightHit : rightState.hitAt
                      (.chainStart lay tree leafIdx chainIdx) output
                  · simp only [output, hrightHit, ↓reduceIte]
                    exact relTriple_any_pure_none_clean _
                  · have hleftHit : ¬leftState.hitAt
                        (.chainStart lay tree leafIdx chainIdx) output :=
                      hstate.not_hitAt_left _ _ hrightHit
                    simp only [output, hleftHit, hrightHit, ↓reduceIte]
                    exact ih output
                      (leftState.materialize (.chainStart lay tree leafIdx chainIdx) output)
                      (rightState.materialize (.chainStart lay tree leafIdx chainIdx) output)
                      leftFuel rightFuel
                      (hstate.materialize (.chainStart lay tree leafIdx chainIdx) output) hfuel
              | position position =>
                  apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
                  intro leftOutput rightOutput houtput
                  subst rightOutput
                  by_cases hrightHit : rightState.hitAt (.position position) leftOutput
                  · simp only [hrightHit, ↓reduceIte]
                    exact relTriple_any_pure_none_clean _
                  · have hleftHit : ¬leftState.hitAt (.position position) leftOutput :=
                      hstate.not_hitAt_left _ _ hrightHit
                    simp only [hleftHit, hrightHit, ↓reduceIte]
                    exact ih leftOutput
                      (leftState.materialize (.position position) leftOutput)
                      (rightState.materialize (.position position) leftOutput)
                      leftFuel rightFuel
                      (hstate.materialize (.position position) leftOutput) hfuel

theorem relTriple_runCleanFromTable_addProbeRight
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (leftState rightState : LazyRevealProbe.State Coordinate)
    (leftFuel rightFuel : Nat) (table : OtsSecretIndex → HashOutput)
    (coordinate : Coordinate) (candidate : Digest)
    (hstate : ProbeStateLE leftState rightState)
    (hroot : (⟨coordinate, candidate⟩ : Probe).IsLayerRoot)
    (hfuel : rightFuel ≤ leftFuel) :
    RelTriple
      (runCleanFromTable leftState leftFuel table computation)
      (runCleanFromTable rightState rightFuel table
        (LazyRevealProbe.probeQuery coordinate candidate >>= fun _ => computation))
      CleanRunProbeLE := by
  rw [LazyRevealProbe.probeQuery, runCleanFromTable_probe_query_bind]
  cases rightFuel with
  | zero => exact relTriple_any_pure_none_clean _
  | succ rightRemaining =>
      have hremaining : rightRemaining ≤ leftFuel := by omega
      have hrevealed := hstate.revealed_iff coordinate
      by_cases hleftRevealed : coordinate ∈ leftState.revealed
      · have hrightRevealed : coordinate ∈ rightState.revealed := hrevealed.mp hleftRevealed
        simp only [hrightRevealed, ↓reduceIte]
        exact relTriple_runCleanFromTable_probeStateLE computation leftState rightState
          leftFuel rightRemaining table hstate hremaining
      · have hrightRevealed : coordinate ∉ rightState.revealed := by
          simpa [hrevealed] using hleftRevealed
        simp only [hrightRevealed, ↓reduceIte]
        exact relTriple_runCleanFromTable_probeStateLE computation leftState
          (rightState.addPending coordinate candidate) leftFuel rightRemaining table
          (hstate.addPendingRight coordinate candidate hroot) hremaining

set_option maxRecDepth 100000 in
theorem relTriple_runCleanFromTable_afterPlan_rootAware
    (parameter : PublicParameter) (input : HashInput) (plan : PlannedHashQuery)
    (leftState rightState : LazyRevealProbe.State Coordinate)
    (leftFuel rightFuel : Nat) (table : OtsSecretIndex → HashOutput)
    (leftCache rightCache : SplitHashCache)
    (hstate : ProbeStateLE leftState rightState)
    (hfuel : rightFuel ≤ leftFuel) (hcache : leftCache = rightCache) :
    RelTriple
      (runCleanFromTable leftState leftFuel table
        ((probingHashQueryAfterPlan parameter input plan).run leftCache))
      (runCleanFromTable rightState rightFuel table
        ((probingHashQueryAfterRootAwarePlan parameter input plan).run rightCache))
      CleanRunProbeLE := by
  subst rightCache
  cases hplan : plan.candidate? with
  | some candidate =>
      rw [probingHashQueryAfterRootAwarePlan_eq_afterPlan_of_candidate parameter input plan
        candidate hplan]
      exact relTriple_runCleanFromTable_probeStateLE _ leftState rightState leftFuel rightFuel
        table hstate hfuel
  | none =>
      cases hdecode : decodeEncodingLayerRootCandidate? parameter input with
      | none =>
          have heq : probingHashQueryAfterRootAwarePlan parameter input plan =
              probingHashQueryAfterPlan parameter input plan := by
            unfold probingHashQueryAfterRootAwarePlan probingHashQueryAfterPlan
              executePlannedHashQuery rootAwareCandidateForPlan?
            rw [hplan, hdecode]
            cases plan.action <;> rfl
          rw [heq]
          exact relTriple_runCleanFromTable_probeStateLE _ leftState rightState leftFuel
            rightFuel table hstate hfuel
      | some candidate =>
          rw [probingHashQueryAfterRootAwarePlan_eq_probe_then_afterPlan parameter input plan
            candidate hplan hdecode]
          simpa [StateT.run_bind, probe, StateT.run_liftM] using
            (relTriple_runCleanFromTable_addProbeRight
              ((probingHashQueryAfterPlan parameter input plan).run leftCache)
              leftState rightState leftFuel rightFuel table candidate.coordinate
              candidate.candidate hstate
              (decodeEncodingLayerRootCandidate?_some_isLayerRoot hdecode) hfuel)

theorem relTriple_runCleanFromTable_bind_probeLE
    (left : OracleComp (LazyRevealProbe.World Coordinate) α)
    (leftNext : α → OracleComp (LazyRevealProbe.World Coordinate) β)
    (right : OracleComp (LazyRevealProbe.World Coordinate) α)
    (rightNext : α → OracleComp (LazyRevealProbe.World Coordinate) β)
    (leftState rightState : LazyRevealProbe.State Coordinate)
    (leftFuel rightFuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hleft : RelTriple
      (runCleanFromTable leftState leftFuel table left)
      (runCleanFromTable rightState rightFuel table right)
      CleanRunProbeLE)
    (hnext : ∀ leftResult rightResult,
      CleanRunProbeLE (some leftResult) (some rightResult) →
      RelTriple
        (runCleanFromTable leftResult.state leftResult.remaining leftResult.table
          (leftNext leftResult.value))
        (runCleanFromTable rightResult.state rightResult.remaining rightResult.table
          (rightNext rightResult.value))
        CleanRunProbeLE) :
    RelTriple
      (runCleanFromTable leftState leftFuel table (left >>= leftNext))
      (runCleanFromTable rightState rightFuel table (right >>= rightNext))
      CleanRunProbeLE := by
  rw [runCleanFromTable_bind, runCleanFromTable_bind]
  apply relTriple_bind hleft
  intro leftResult rightResult hrelation
  cases rightResult with
  | none =>
      cases leftResult with
      | none => exact relTriple_pure_pure trivial
      | some leftResult => exact relTriple_any_pure_none_clean _
  | some rightResult =>
      cases leftResult with
      | none => simp [CleanRunProbeLE] at hrelation
      | some leftResult => exact hnext leftResult rightResult hrelation

set_option maxRecDepth 100000 in
theorem relTriple_runCleanFromTable_probingHashQuery_rootAware
    (parameter : PublicParameter) (input : HashInput)
    (leftState rightState : LazyRevealProbe.State Coordinate)
    (leftFuel rightFuel : Nat) (table : OtsSecretIndex → HashOutput)
    (leftCache rightCache : SplitHashCache)
    (hstate : ProbeStateLE leftState rightState)
    (hfuel : rightFuel ≤ leftFuel) (hcache : leftCache = rightCache) :
    RelTriple
      (runCleanFromTable leftState leftFuel table
        ((probingHashQuery parameter input).run leftCache))
      (runCleanFromTable rightState rightFuel table
        ((rootAwareProbingHashQuery parameter input).run rightCache))
      CleanRunProbeLE := by
  subst rightCache
  rw [probingHashQuery_eq_plan_then_afterPlan]
  unfold rootAwareProbingHashQuery
  rw [StateT.run_bind, StateT.run_bind]
  apply relTriple_runCleanFromTable_bind_probeLE
  · exact relTriple_runCleanFromTable_probeStateLE
      ((planProbingHashQuery parameter input).run leftCache)
      leftState rightState leftFuel rightFuel table hstate hfuel
  · intro leftResult rightResult hrelation
    rcases hrelation with ⟨hvalue, htable, hremaining, hnextState⟩
    have hplan : leftResult.value.1 = rightResult.value.1 := congrArg Prod.fst hvalue
    have hnextCache : leftResult.value.2 = rightResult.value.2 := congrArg Prod.snd hvalue
    rw [← hplan, ← hnextCache, ← htable]
    exact relTriple_runCleanFromTable_afterPlan_rootAware parameter input leftResult.value.1
      leftResult.state rightResult.state leftResult.remaining rightResult.remaining
      leftResult.table leftResult.value.2 leftResult.value.2 hnextState hremaining rfl

theorem relTriple_runCleanFromTable_maskedExpanded_step_rootAware
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (query : (OracleWorld + SigningSpec).Domain)
    (leftState rightState : LazyRevealProbe.State Coordinate)
    (leftFuel rightFuel : Nat) (table : OtsSecretIndex → HashOutput)
    (leftCache rightCache : SplitHashCache)
    (hstate : ProbeStateLE leftState rightState)
    (hfuel : rightFuel ≤ leftFuel) (hcache : leftCache = rightCache) :
    RelTriple
      (runCleanFromTable leftState leftFuel table
        ((maskedExpandedAdversaryImpl parameter root ftsSecret query).run leftCache))
      (runCleanFromTable rightState rightFuel table
        ((rootAwareMaskedExpandedAdversaryImpl parameter root ftsSecret query).run rightCache))
      CleanRunProbeLE := by
  cases query with
  | inl worldQuery =>
      cases worldQuery with
      | inl n =>
          subst rightCache
          exact relTriple_runCleanFromTable_probeStateLE
            ((splitUniformImpl n).run leftCache) leftState rightState leftFuel rightFuel table
            hstate hfuel
      | inr input =>
          exact relTriple_runCleanFromTable_probingHashQuery_rootAware parameter input leftState
            rightState leftFuel rightFuel table leftCache rightCache hstate hfuel hcache
  | inr message =>
      subst rightCache
      exact relTriple_runCleanFromTable_probeStateLE
        ((maskedSign parameter root ftsSecret message).run leftCache)
        leftState rightState leftFuel rightFuel table hstate hfuel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem relTriple_runCleanFromTable_simulateQ_rootAware
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (leftState rightState : LazyRevealProbe.State Coordinate)
    (leftFuel rightFuel : Nat) (table : OtsSecretIndex → HashOutput)
    (leftCache rightCache : SplitHashCache)
    (hstate : ProbeStateLE leftState rightState)
    (hfuel : rightFuel ≤ leftFuel) (hcache : leftCache = rightCache) :
    RelTriple
      (runCleanFromTable leftState leftFuel table
        ((simulateQ (maskedExpandedAdversaryImpl parameter root ftsSecret)
          computation).run leftCache))
      (runCleanFromTable rightState rightFuel table
        ((simulateQ (rootAwareMaskedExpandedAdversaryImpl parameter root ftsSecret)
          computation).run rightCache))
      CleanRunProbeLE := by
  induction computation using OracleComp.inductionOn generalizing
      leftState rightState leftFuel rightFuel table leftCache rightCache with
  | pure value =>
      subst rightCache
      simp only [simulateQ_pure, StateT.run_pure]
      exact relTriple_runCleanFromTable_probeStateLE (pure (value, leftCache))
        leftState rightState leftFuel rightFuel table hstate hfuel
  | query_bind query next ih =>
      rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, StateT.run_bind]
      apply relTriple_runCleanFromTable_bind_probeLE
      · exact relTriple_runCleanFromTable_maskedExpanded_step_rootAware parameter root ftsSecret
          query leftState rightState leftFuel rightFuel table leftCache rightCache hstate hfuel
          hcache
      · intro leftResult rightResult hrelation
        rcases hrelation with ⟨hvalue, htable, hremaining, hnextState⟩
        have houtput : leftResult.value.1 = rightResult.value.1 := congrArg Prod.fst hvalue
        have hnextCache : leftResult.value.2 = rightResult.value.2 := congrArg Prod.snd hvalue
        rw [← houtput, ← hnextCache, ← htable]
        exact ih ((OracleSpec.query query).cont leftResult.value.1)
          leftResult.state rightResult.state
          leftResult.remaining rightResult.remaining leftResult.table leftResult.value.2
          leftResult.value.2 hnextState hremaining rfl

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem relTriple_runCleanFromTable_deferred_rootAware
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    RelTriple
      (runCleanFromTable LazyRevealProbe.State.empty fuel table
        (deferredCleanRetainedRun adversary parameter ftsSecret))
      (runCleanFromTable LazyRevealProbe.State.empty fuel table
        (rootAwareCleanRetainedRun adversary parameter ftsSecret))
      CleanRunProbeLE := by
  unfold deferredCleanRetainedRun rootAwareCleanRetainedRun
  apply relTriple_runCleanFromTable_bind_probeLE
  · exact relTriple_runCleanFromTable_probeStateLE
      (maskedPublishedTreeRoot.run emptySplitHashCache)
      LazyRevealProbe.State.empty LazyRevealProbe.State.empty fuel fuel table
      (ProbeStateLE.refl _) le_rfl
  · intro leftRoot rightRoot hrootRelation
    rcases hrootRelation with ⟨hrootValue, hrootTable, hrootRemaining, hrootState⟩
    have hroot : leftRoot.value.1 = rightRoot.value.1 := congrArg Prod.fst hrootValue
    have hrootCache : leftRoot.value.2 = rightRoot.value.2 := congrArg Prod.snd hrootValue
    rw [← hroot, ← hrootCache, ← hrootTable]
    have hleftRest : deferredCleanRetainedRest adversary parameter leftRoot.value.1 ftsSecret
        leftRoot.value.2 =
      (simulateQ (maskedExpandedAdversaryImpl parameter leftRoot.value.1 ftsSecret)
        (retainedGameRestComputation adversary
          ⟨leftRoot.value.1, parameter⟩)).run leftRoot.value.2 := by
      unfold deferredCleanRetainedRest
      rw [simulateQ_maskedExpanded_retainedGameRestComputation]
    apply relTriple_runCleanFromTable_bind_probeLE
    · rw [hleftRest]
      exact relTriple_runCleanFromTable_simulateQ_rootAware parameter leftRoot.value.1 ftsSecret
        (retainedGameRestComputation adversary ⟨leftRoot.value.1, parameter⟩)
        leftRoot.state rightRoot.state leftRoot.remaining rightRoot.remaining leftRoot.table
        leftRoot.value.2 leftRoot.value.2 hrootState hrootRemaining rfl
    · intro leftRest rightRest hrestRelation
      rcases hrestRelation with ⟨hrestValue, hrestTable, hrestRemaining, hrestState⟩
      have hrestOutput : leftRest.value.1 = rightRest.value.1 := congrArg Prod.fst hrestValue
      have hrestCache : leftRest.value.2 = rightRest.value.2 := congrArg Prod.snd hrestValue
      rw [← hrestOutput, ← hrestCache, ← hrestTable]
      exact relTriple_runCleanFromTable_probeStateLE
        (pure ((leftRoot.value.1, leftRest.value.1), leftRest.value.2))
        leftRest.state rightRest.state leftRest.remaining rightRest.remaining leftRest.table
        hrestState hrestRemaining

theorem relTriple_runThenFinalizeCleanFromTable_deferred_rootAware
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) :
    RelTriple
      (runCleanFromTable LazyRevealProbe.State.empty fuel table
        (deferredCleanRetainedRun adversary parameter ftsSecret) >>= finishCleanRunFromTable)
      (runCleanFromTable LazyRevealProbe.State.empty fuel table
        (rootAwareCleanRetainedRun adversary parameter ftsSecret) >>= finishCleanRunFromTable)
      CleanFinishFailureLE := by
  apply relTriple_bind
    (relTriple_runCleanFromTable_deferred_rootAware adversary parameter ftsSecret fuel table)
  intro leftRun rightRun hrun
  exact relTriple_finishCleanRunFromTable_probeLE leftRun rightRun hrun

theorem probEvent_runThenFinalizeCleanFromTable_deferred_le_rootAware
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) :
    Pr[= none | runCleanFromTable LazyRevealProbe.State.empty fuel table
        (deferredCleanRetainedRun adversary parameter ftsSecret) >>= finishCleanRunFromTable] ≤
      Pr[= none | runCleanFromTable LazyRevealProbe.State.empty fuel table
        (rootAwareCleanRetainedRun adversary parameter ftsSecret) >>=
          finishCleanRunFromTable] := by
  rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
  apply probEvent_le_of_relTriple
    (relTriple_runThenFinalizeCleanFromTable_deferred_rootAware adversary parameter ftsSecret
      fuel table)
  intro left right hrelation hleft
  exact hrelation hleft

noncomputable def sampledDeferredCleanThroughTable
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp (Option (CleanRunResult (RetainedGameResult × SplitHashCache))) := do
  let base ← sampleOtsHashTable
  let table := completedStartTable LazyRevealProbe.State.empty base
  let result ← runCleanFromTable LazyRevealProbe.State.empty fuel table
    (deferredCleanRetainedRun adversary parameter ftsSecret)
  finishCleanRunFromTable result

noncomputable def sampledRootAwareCleanThroughTable
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp (Option (CleanRunResult (RetainedGameResult × SplitHashCache))) := do
  let base ← sampleOtsHashTable
  let table := completedStartTable LazyRevealProbe.State.empty base
  let result ← runCleanFromTable LazyRevealProbe.State.empty fuel table
    (rootAwareCleanRetainedRun adversary parameter ftsSecret)
  finishCleanRunFromTable result

theorem sampledDeferredCleanThroughTable_eq
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    sampledDeferredCleanThroughTable adversary parameter ftsSecret fuel =
      sampledRunThenFinalizeClean LazyRevealProbe.State.empty fuel
        (deferredCleanRetainedRun adversary parameter ftsSecret) := by
  rfl

theorem sampledRootAwareCleanThroughTable_eq
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    sampledRootAwareCleanThroughTable adversary parameter ftsSecret fuel =
      sampledRunThenFinalizeClean LazyRevealProbe.State.empty fuel
        (rootAwareCleanRetainedRun adversary parameter ftsSecret) := by
  rfl

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 1000000 in
theorem probEvent_sampledDeferredClean_none_le_rootAware
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[= none | sampledRunThenFinalizeClean
        (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel
        (deferredCleanRetainedRun adversary parameter ftsSecret)] ≤
      Pr[= none | sampledRunThenFinalizeClean
        (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel
        (rootAwareCleanRetainedRun adversary parameter ftsSecret)] := by
  rw [← sampledDeferredCleanThroughTable_eq adversary parameter ftsSecret fuel,
    ← sampledRootAwareCleanThroughTable_eq adversary parameter ftsSecret fuel]
  unfold sampledDeferredCleanThroughTable sampledRootAwareCleanThroughTable
  rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
  apply probEvent_bind_le_bind_of_forall_le
  intro base _hbase
  dsimp only
  rw [show (fun result : Option
      (CleanRunResult (RetainedGameResult × SplitHashCache)) =>
        finishCleanRunFromTable result) = finishCleanRunFromTable by
      funext result
      rfl]
  have hbound := probEvent_runThenFinalizeCleanFromTable_deferred_le_rootAware adversary
    parameter ftsSecret fuel (completedStartTable LazyRevealProbe.State.empty base)
  rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput] at hbound
  exact hbound

end SphincsSecurity.Concrete.OtsProbeSimulation

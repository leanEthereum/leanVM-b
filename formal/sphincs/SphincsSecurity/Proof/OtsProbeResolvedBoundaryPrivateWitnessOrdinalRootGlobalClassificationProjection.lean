import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationSample

/-!
# First-hit diagnostic projection

The diagnostic finalizer does not create observations. This module removes it from each fixed
first-hit event, leaving only the retained materialized run that the stopped endpoint couplings
must analyze.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

def ObservedCleanRunOption.FirstExistingHiddenRootHitAt
    (ordinal : Nat) : Option (ObservedCleanRunResult α) → Prop
  | none => False
  | some result =>
      ∃ selected : Fin result.observations.length,
        selected.val = ordinal ∧ FirstExistingHiddenHitAt result ordinal ∧
          (result.observations.get selected).toProbe.IsLayerRoot

def ObservedCleanRunOption.FirstExistingHiddenNonRootHitAt
    (ordinal : Nat) : Option (ObservedCleanRunResult α) → Prop
  | none => False
  | some result =>
      ∃ selected : Fin result.observations.length,
        selected.val = ordinal ∧ FirstExistingHiddenHitAt result ordinal ∧
          ¬(result.observations.get selected).toProbe.IsLayerRoot

def ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt
    (table : OtsSecretIndex → HashOutput) (ordinal : Nat) :
    Option (ObservedCleanRunResult α) → Prop
  | none => False
  | some result =>
      (∃ finalResult, some finalResult ∈ support
        (finishObservedCleanRunFromTable (some result))) ∧
      ¬DeferredCompletable table (directDeferredContext result.state) ∧
      ObservedCleanRunOption.FirstExistingHiddenRootHitAt ordinal (some result)

def ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenNonRootHitAt
    (table : OtsSecretIndex → HashOutput) (ordinal : Nat) :
    Option (ObservedCleanRunResult α) → Prop
  | none => False
  | some result =>
      (∃ finalResult, some finalResult ∈ support
        (finishObservedCleanRunFromTable (some result))) ∧
      ¬DeferredCompletable table (directDeferredContext result.state) ∧
      ObservedCleanRunOption.FirstExistingHiddenNonRootHitAt ordinal (some result)

theorem before_eq_of_mem_finishObservedMaterializedDiagnostic
    (table : OtsSecretIndex → HashOutput)
    (result : Option (ObservedCleanRunResult α))
    (outcome : ObservedMaterializedDiagnostic α)
    (houtcome : outcome ∈ support (finishObservedMaterializedDiagnostic table result)) :
    outcome.before = result := by
  classical
  cases result with
  | none =>
      simp [finishObservedMaterializedDiagnostic] at houtcome
      subst outcome
      rfl
  | some result =>
      unfold finishObservedMaterializedDiagnostic at houtcome
      rw [mem_support_bind_iff] at houtcome
      obtain ⟨final, _hfinal, hreturn⟩ := houtcome
      simp only [mem_support_pure_iff] at hreturn
      subst outcome
      rfl

theorem successfulDoomed_data_of_mem_finishObservedMaterializedDiagnostic
    (table : OtsSecretIndex → HashOutput)
    (result : Option (ObservedCleanRunResult α))
    (outcome : ObservedMaterializedDiagnostic α)
    (houtcome : outcome ∈ support (finishObservedMaterializedDiagnostic table result))
    (hsuccess : outcome.SuccessfulDoomed) :
    ∃ before finalResult,
      result = some before ∧
      outcome.before = some before ∧
      outcome.final = some finalResult ∧
      some finalResult ∈ support (finishObservedCleanRunFromTable (some before)) ∧
      ¬DeferredCompletable table (directDeferredContext before.state) := by
  classical
  cases result with
  | none =>
      simp [finishObservedMaterializedDiagnostic] at houtcome
      subst outcome
      simp [ObservedMaterializedDiagnostic.SuccessfulDoomed] at hsuccess
  | some before =>
      unfold finishObservedMaterializedDiagnostic at houtcome
      rw [mem_support_bind_iff] at houtcome
      obtain ⟨final, hfinal, hreturn⟩ := houtcome
      simp only [mem_support_pure_iff] at hreturn
      subst outcome
      cases final with
      | none =>
          simp [ObservedMaterializedDiagnostic.SuccessfulDoomed] at hsuccess
      | some finalResult =>
          refine ⟨before, finalResult, rfl, rfl, rfl, hfinal, ?_⟩
          simpa [ObservedMaterializedDiagnostic.SuccessfulDoomed] using hsuccess.2

theorem probEvent_finishDiagnostic_successfulDoomed_firstExistingHiddenRootHitAt_le
    (table : OtsSecretIndex → HashOutput)
    (run : ProbComp (Option (ObservedCleanRunResult α))) (ordinal : Nat) :
    Pr[fun outcome => outcome.SuccessfulDoomed ∧
          outcome.FirstExistingHiddenRootHitAt ordinal |
        run >>= finishObservedMaterializedDiagnostic table] ≤
      Pr[ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt table ordinal |
        run] := by
  apply probEvent_bind_le_probEvent
  intro result _hresult hnot
  apply probEvent_eq_zero
  intro outcome houtcome hevent
  obtain ⟨before, finalResult, hresult, hbefore, _hfinalEq, hfinal, hdoomed⟩ :=
    successfulDoomed_data_of_mem_finishObservedMaterializedDiagnostic table result outcome
      houtcome hevent.1
  subst result
  obtain ⟨rootResult, selected, hrootBefore, hselected, hfirst, hroot⟩ := hevent.2
  have hsame : rootResult = before := Option.some.inj (hrootBefore.symm.trans hbefore)
  subst rootResult
  exact hnot ⟨⟨finalResult, hfinal⟩, hdoomed,
    ⟨selected, hselected, hfirst, hroot⟩⟩

theorem probEvent_finishDiagnostic_successfulDoomed_firstExistingHiddenNonRootHitAt_le
    (table : OtsSecretIndex → HashOutput)
    (run : ProbComp (Option (ObservedCleanRunResult α))) (ordinal : Nat) :
    Pr[fun outcome => outcome.SuccessfulDoomed ∧
          outcome.FirstExistingHiddenNonRootHitAt ordinal |
        run >>= finishObservedMaterializedDiagnostic table] ≤
      Pr[ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenNonRootHitAt table ordinal |
        run] := by
  apply probEvent_bind_le_probEvent
  intro result _hresult hnot
  apply probEvent_eq_zero
  intro outcome houtcome hevent
  obtain ⟨before, finalResult, hresult, hbefore, _hfinalEq, hfinal, hdoomed⟩ :=
    successfulDoomed_data_of_mem_finishObservedMaterializedDiagnostic table result outcome
      houtcome hevent.1
  subst result
  obtain ⟨nonRootResult, selected, hnonRootBefore, hselected, hfirst, hnonRoot⟩ := hevent.2
  have hsame : nonRootResult = before := Option.some.inj (hnonRootBefore.symm.trans hbefore)
  subst nonRootResult
  exact hnot ⟨⟨finalResult, hfinal⟩, hdoomed,
    ⟨selected, hselected, hfirst, hnonRoot⟩⟩

theorem probEvent_finishDiagnostic_firstExistingHiddenRootHitAt_le
    (table : OtsSecretIndex → HashOutput)
    (run : ProbComp (Option (ObservedCleanRunResult α))) (ordinal : Nat) :
    Pr[ObservedMaterializedDiagnostic.FirstExistingHiddenRootHitAt ordinal |
        run >>= finishObservedMaterializedDiagnostic table] ≤
      Pr[ObservedCleanRunOption.FirstExistingHiddenRootHitAt ordinal | run] := by
  apply probEvent_bind_le_probEvent
  intro result _hresult hnot
  apply probEvent_eq_zero
  intro outcome houtcome hroot
  obtain ⟨before, selected, hbefore, hselected, hfirst, hroot⟩ := hroot
  have heq := before_eq_of_mem_finishObservedMaterializedDiagnostic table result outcome houtcome
  rw [heq] at hbefore
  cases result with
  | none => simp at hbefore
  | some result =>
      have hresult : before = result := Option.some.inj hbefore.symm
      subst before
      exact hnot ⟨selected, hselected, hfirst, hroot⟩

theorem probEvent_finishDiagnostic_firstExistingHiddenNonRootHitAt_le
    (table : OtsSecretIndex → HashOutput)
    (run : ProbComp (Option (ObservedCleanRunResult α))) (ordinal : Nat) :
    Pr[ObservedMaterializedDiagnostic.FirstExistingHiddenNonRootHitAt ordinal |
        run >>= finishObservedMaterializedDiagnostic table] ≤
      Pr[ObservedCleanRunOption.FirstExistingHiddenNonRootHitAt ordinal | run] := by
  apply probEvent_bind_le_probEvent
  intro result _hresult hnot
  apply probEvent_eq_zero
  intro outcome houtcome hnonRoot
  obtain ⟨before, selected, hbefore, hselected, hfirst, hnonRoot⟩ := hnonRoot
  have heq := before_eq_of_mem_finishObservedMaterializedDiagnostic table result outcome houtcome
  rw [heq] at hbefore
  cases result with
  | none => simp at hbefore
  | some result =>
      have hresult : before = result := Option.some.inj hbefore.symm
      subst before
      exact hnot ⟨selected, hselected, hfirst, hnonRoot⟩

attribute [local irreducible]
  observedMaterializedRetainedRunFromTable finishObservedMaterializedDiagnostic in
theorem probEvent_sampledDiagnostic_firstExistingHiddenRootHitAt_le_raw
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel ordinal : Nat) :
    Pr[ObservedMaterializedDiagnostic.FirstExistingHiddenRootHitAt ordinal |
        sampledObservedMaterializedDiagnostic adversary parameter ftsSecret fuel] ≤
      Pr[ObservedCleanRunOption.FirstExistingHiddenRootHitAt ordinal | do
        let table ← sampleOtsHashTable
        observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table] := by
  unfold sampledObservedMaterializedDiagnostic
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro table
  gcongr
  exact probEvent_finishDiagnostic_firstExistingHiddenRootHitAt_le table
    (observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table) ordinal

attribute [local irreducible]
  observedMaterializedRetainedRunFromTable finishObservedMaterializedDiagnostic in
theorem probEvent_sampledDiagnostic_firstExistingHiddenNonRootHitAt_le_raw
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel ordinal : Nat) :
    Pr[ObservedMaterializedDiagnostic.FirstExistingHiddenNonRootHitAt ordinal |
        sampledObservedMaterializedDiagnostic adversary parameter ftsSecret fuel] ≤
      Pr[ObservedCleanRunOption.FirstExistingHiddenNonRootHitAt ordinal | do
        let table ← sampleOtsHashTable
        observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table] := by
  unfold sampledObservedMaterializedDiagnostic
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro table
  gcongr
  exact probEvent_finishDiagnostic_firstExistingHiddenNonRootHitAt_le table
    (observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table) ordinal

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
set_option linter.constructorNameAsVariable false in
attribute [local irreducible]
  observedMaterializedRetainedRunFromTable finishObservedMaterializedDiagnostic in
theorem probEvent_sampledDiagnostic_successfulDoomed_firstExistingHiddenRootHitAt_le_of_forall
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel ordinal : Nat)
    (bound : ENNReal)
    (hbound : ∀ table,
      Pr[ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt table ordinal |
          observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table] ≤
        bound) :
    Pr[fun outcome => outcome.SuccessfulDoomed ∧
          outcome.FirstExistingHiddenRootHitAt ordinal |
        sampledObservedMaterializedDiagnostic adversary parameter ftsSecret fuel] ≤ bound := by
  unfold sampledObservedMaterializedDiagnostic
  apply probEvent_bind_le_of_forall_le
  intro table _htable
  calc
    _ ≤ Pr[ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt table ordinal |
          observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table] :=
      probEvent_finishDiagnostic_successfulDoomed_firstExistingHiddenRootHitAt_le table
        (observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table) ordinal
    _ ≤ bound := hbound table

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
set_option linter.constructorNameAsVariable false in
attribute [local irreducible]
  observedMaterializedRetainedRunFromTable finishObservedMaterializedDiagnostic in
theorem probEvent_sampledDiagnostic_successfulDoomed_firstExistingHiddenNonRootHitAt_le_of_forall
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel ordinal : Nat)
    (bound : ENNReal)
    (hbound : ∀ table,
      Pr[ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenNonRootHitAt table ordinal |
          observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table] ≤
        bound) :
    Pr[fun outcome => outcome.SuccessfulDoomed ∧
          outcome.FirstExistingHiddenNonRootHitAt ordinal |
        sampledObservedMaterializedDiagnostic adversary parameter ftsSecret fuel] ≤ bound := by
  unfold sampledObservedMaterializedDiagnostic
  apply probEvent_bind_le_of_forall_le
  intro table _htable
  calc
    _ ≤ Pr[ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenNonRootHitAt table ordinal |
          observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table] :=
      probEvent_finishDiagnostic_successfulDoomed_firstExistingHiddenNonRootHitAt_le table
        (observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table) ordinal
    _ ≤ bound := hbound table

end SphincsSecurity.Concrete.OtsProbeSimulation

import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedChain

/-!
# Sampled stopped diagnostic projection

The diagnostic is classified by one first-hit ordinal before inspecting the coordinate kind. This
keeps the selected structural charge at one unit per ordinal. The chain-start alternative remains
attached to that same ordinal.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

def ObservedMaterializedDiagnostic.FirstExistingHiddenHitAt
    (ordinal : Nat) (outcome : ObservedMaterializedDiagnostic α) : Prop :=
  ∃ result, outcome.before = some result ∧
    SphincsSecurity.Concrete.OtsProbeSimulation.FirstExistingHiddenHitAt result ordinal

def ObservedCleanRunOption.SuccessfulFirstExistingHiddenHitAt
    (ordinal : Nat) : Option (ObservedCleanRunResult α) → Prop
  | none => False
  | some result =>
      (∃ finalResult, some finalResult ∈ support
        (finishObservedCleanRunFromTable (some result))) ∧
      SphincsSecurity.Concrete.OtsProbeSimulation.FirstExistingHiddenHitAt result ordinal

theorem SnapshotObservedFirstStoppedRel.selected_or_chain_of_successful_firstHit
    {table : OtsSecretIndex → HashOutput}
    {source : PrivateWitnessSnapshotOutput}
    {result : ObservedCleanRunResult (α × SplitHashCache)}
    (hrelation : SnapshotObservedFirstStoppedRel table source (some result))
    (finalResult : ObservedCleanRunResult (α × SplitHashCache))
    (hfinish : some finalResult ∈ support
      (finishObservedCleanRunFromTable (some result)))
    (ordinal : Nat)
    (hfirst : SphincsSecurity.Concrete.OtsProbeSimulation.FirstExistingHiddenHitAt
      result ordinal) :
    SelectedPrivateSnapshotHitAt source ordinal ∨
      FirstExistingHiddenChainStartHitAt result.observations ordinal := by
  have hfirstData := hfirst
  obtain ⟨selected, hselected, _hhit, _hbefore⟩ := hfirstData
  by_cases hroot : (result.observations.get selected).toProbe.IsLayerRoot
  · left
    apply hrelation.selected_of_successful_firstRoot finalResult hfinish ordinal hfirst
    intro other hother
    have heq : other = selected := Fin.ext (hother.trans hselected.symm)
    subst other
    exact hroot
  · rcases hrelation.selected_or_chain_of_successful_firstNonRoot finalResult hfinish ordinal
      hfirst with hselectedSource | hchain
    · exact Or.inl hselectedSource
    · exact Or.inr (hchain.at_of_firstExistingHiddenHitAt hfirst)

attribute [local irreducible]
  observedMaterializedRetainedRunFromTable finishObservedMaterializedDiagnostic in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_finishDiagnostic_successfulDoomed_firstExistingHiddenHitAt_le
    (table : OtsSecretIndex → HashOutput)
    (run : ProbComp (Option (ObservedCleanRunResult α))) (ordinal : Nat) :
    Pr[fun outcome => outcome.SuccessfulDoomed ∧
          outcome.FirstExistingHiddenHitAt ordinal |
        run >>= finishObservedMaterializedDiagnostic table] ≤
      Pr[ObservedCleanRunOption.SuccessfulFirstExistingHiddenHitAt ordinal | run] := by
  apply probEvent_bind_le_probEvent
  intro result _hresult hnot
  apply probEvent_eq_zero
  intro outcome houtcome hevent
  obtain ⟨before, finalResult, hresult, hbefore, _hfinalEq, hfinish, _hdoomed⟩ :=
    successfulDoomed_data_of_mem_finishObservedMaterializedDiagnostic table result outcome
      houtcome hevent.1
  obtain ⟨firstResult, hfirstBefore, hfirst⟩ := hevent.2
  have heq : firstResult = before := Option.some.inj (hfirstBefore.symm.trans hbefore)
  subst firstResult
  subst result
  exact hnot ⟨⟨finalResult, hfinish⟩, hfirst⟩

attribute [local irreducible]
  observedMaterializedRetainedRunFromTable finishObservedMaterializedDiagnostic in
set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_sampledDiagnostic_successfulDoomed_firstExistingHiddenHitAt_le_raw
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel ordinal : Nat) :
    Pr[fun outcome => outcome.SuccessfulDoomed ∧
          outcome.FirstExistingHiddenHitAt ordinal |
        sampledObservedMaterializedDiagnostic adversary parameter ftsSecret fuel] ≤
      Pr[ObservedCleanRunOption.SuccessfulFirstExistingHiddenHitAt ordinal | do
        let table ← sampleOtsHashTable
        observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table] := by
  change Pr[fun outcome => outcome.SuccessfulDoomed ∧
        outcome.FirstExistingHiddenHitAt ordinal |
      sampleOtsHashTable >>= fun table =>
        observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table >>=
          finishObservedMaterializedDiagnostic table] ≤
    Pr[ObservedCleanRunOption.SuccessfulFirstExistingHiddenHitAt ordinal |
      sampleOtsHashTable >>= fun table =>
        observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table]
  rw [probEvent_bind_eq_tsum (mx := sampleOtsHashTable)]
  rw [probEvent_bind_eq_tsum (mx := sampleOtsHashTable)]
  apply ENNReal.tsum_le_tsum
  intro table
  by_cases htable : table ∈ support sampleOtsHashTable
  · exact mul_le_mul' le_rfl
      (probEvent_finishDiagnostic_successfulDoomed_firstExistingHiddenHitAt_le
        (α := RetainedGameResult × SplitHashCache) table
        (observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table) ordinal)
  · simp [probOutput_eq_zero_of_not_mem_support htable]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_sampledSuccessfulFirstHit_le_selectedSnapshot_add_chainStartAt
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q ordinal : Nat)
    (hbound : ∀ root,
      (retainedGameRestComputation adversary ⟨root, parameter⟩).IsQueryBoundP
        IsOuterHash q)
    (hq : q ≤ 2 ^ securityBits) :
    Pr[ObservedCleanRunOption.SuccessfulFirstExistingHiddenHitAt ordinal | do
        let table ← sampleOtsHashTable
        observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table] ≤
      Pr[fun source => SelectedPrivateSnapshotHitAt source ordinal |
          sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] +
        Pr[fun observed => (match observed with
          | none => False
          | some result => FirstExistingHiddenChainStartHitAt result.observations ordinal) | do
          let table ← sampleOtsHashTable
          observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table] := by
  let source := sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q
  let observed := do
    let table ← sampleOtsHashTable
    observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table
  apply probEvent_le_failure_add_residual_of_relTriple observed source
    (fun observed source => ∃ table, SnapshotObservedFirstStoppedRel table source observed)
    (ObservedCleanRunOption.SuccessfulFirstExistingHiddenHitAt ordinal)
    (fun observed => match observed with
      | none => False
      | some result => FirstExistingHiddenChainStartHitAt result.observations ordinal)
    (fun source => SelectedPrivateSnapshotHitAt source ordinal)
    (relTriple_symm
      (relTriple_sampledGranularAllCanonical_observedMaterializedRetained_firstStopped adversary
        parameter ftsSecret q hbound hq))
  intro right left hrelation hevent hnotChain
  obtain ⟨table, hrelation⟩ := hrelation
  cases right with
  | none => simp [ObservedCleanRunOption.SuccessfulFirstExistingHiddenHitAt] at hevent
  | some result =>
      obtain ⟨⟨finalResult, hfinish⟩, hfirst⟩ := hevent
      rcases hrelation.selected_or_chain_of_successful_firstHit finalResult hfinish ordinal hfirst
        with hselected | hchain
      · exact hselected
      · exact (hnotChain hchain).elim

attribute [local irreducible] sampledObservedMaterializedDiagnostic in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem probEvent_sampledDiagnostic_successfulDoomed_le_sum_firstHits
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hq : q ≤ 2 ^ securityBits) :
    Pr[ObservedMaterializedDiagnostic.SuccessfulDoomed |
        sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] ≤
      ∑ ordinal : Fin (2 * q),
        Pr[fun outcome => outcome.SuccessfulDoomed ∧
            outcome.FirstExistingHiddenHitAt ordinal.val |
          sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] := by
  classical
  let run := sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)
  calc
    _ ≤ Pr[fun outcome => ∃ ordinal ∈ (Finset.univ : Finset (Fin (2 * q))),
          outcome.SuccessfulDoomed ∧ outcome.FirstExistingHiddenHitAt ordinal.val | run] := by
      apply probEvent_mono
      intro outcome houtcome hsuccess
      have hhit := hasExistingHiddenHit_of_mem_sampledDiagnostic_successfulDoomed adversary
        parameter ftsSecret q hq outcome houtcome hsuccess
      rcases ObservedMaterializedDiagnostic.firstExistingHidden_root_or_nonRoot hhit with
        hroot | hnonRoot
      · obtain ⟨ordinal, result, sourceOrdinal, hbefore, hordinal, hfirst, _hroot⟩ := hroot
        have hlength := observations_length_le_of_mem_sampledDiagnostic_before adversary parameter
          ftsSecret (2 * q) outcome result houtcome hbefore
        have hlt : ordinal < 2 * q := by omega
        let bounded : Fin (2 * q) := ⟨ordinal, hlt⟩
        have hfirstAt : FirstExistingHiddenHitAt result ordinal :=
          hordinal ▸ firstExistingHiddenHitAt_of_firstExistingHiddenHitOrdinal?_eq_some hfirst
        exact ⟨bounded, Finset.mem_univ bounded, hsuccess, result, hbefore, by
          simpa [bounded] using hfirstAt⟩
      · obtain ⟨ordinal, result, sourceOrdinal, hbefore, hordinal, hfirst, _hnonRoot⟩ :=
          hnonRoot
        have hlength := observations_length_le_of_mem_sampledDiagnostic_before adversary parameter
          ftsSecret (2 * q) outcome result houtcome hbefore
        have hlt : ordinal < 2 * q := by omega
        let bounded : Fin (2 * q) := ⟨ordinal, hlt⟩
        have hfirstAt : FirstExistingHiddenHitAt result ordinal :=
          hordinal ▸ firstExistingHiddenHitAt_of_firstExistingHiddenHitOrdinal?_eq_some hfirst
        exact ⟨bounded, Finset.mem_univ bounded, hsuccess, result, hbefore, by
          simpa [bounded] using hfirstAt⟩
    _ ≤ ∑ ordinal : Fin (2 * q),
          Pr[fun outcome => outcome.SuccessfulDoomed ∧
              outcome.FirstExistingHiddenHitAt ordinal.val | run] :=
      probEvent_exists_finset_le_sum Finset.univ run fun (ordinal : Fin (2 * q)) outcome =>
        outcome.SuccessfulDoomed ∧ outcome.FirstExistingHiddenHitAt ordinal.val
    _ = _ := by simp only [run]

end SphincsSecurity.Concrete.OtsProbeSimulation

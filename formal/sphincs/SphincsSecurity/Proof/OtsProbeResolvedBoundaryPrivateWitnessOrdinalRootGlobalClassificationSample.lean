import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationKernel

/-!
# Sampled sound global root classification

The fixed-table diagnostic relation is lifted through the opaque one-time table sampler here. The
probability projection keeps the fresh failure, successful doomed state and delayed source event as
three separate terms.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

attribute [local irreducible]
  observedMaterializedRetainedRunFromTable finishObservedMaterializedDiagnostic in
set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem hasExistingHiddenHit_of_mem_sampledDiagnostic_successfulDoomed
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hq : q ≤ 2 ^ securityBits)
    (outcome : ObservedMaterializedDiagnostic
      (RetainedGameResult × SplitHashCache))
    (houtcome : outcome ∈ support
      (sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)))
    (hsuccess : outcome.SuccessfulDoomed) :
    outcome.HasExistingHiddenHit := by
  change outcome ∈ support (sampleOtsHashTable >>= fun table =>
    observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table >>=
      finishObservedMaterializedDiagnostic table) at houtcome
  rw [mem_support_bind_iff] at houtcome
  obtain ⟨table, _htable, hfixed⟩ := houtcome
  exact hasExistingHiddenHit_of_mem_diagnosticFromTable_successfulDoomed adversary parameter
    ftsSecret q table hq outcome hfixed hsuccess

attribute [local irreducible] sampledObservedMaterializedDiagnostic in
set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_sampledDiagnostic_successfulDoomed_le_existingHiddenHit
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hq : q ≤ 2 ^ securityBits) :
    Pr[ObservedMaterializedDiagnostic.SuccessfulDoomed |
        sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] ≤
      Pr[ObservedMaterializedDiagnostic.HasExistingHiddenHit |
        sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] := by
  apply probEvent_mono
  intro outcome houtcome hsuccess
  exact hasExistingHiddenHit_of_mem_sampledDiagnostic_successfulDoomed adversary parameter
    ftsSecret q hq outcome houtcome hsuccess

attribute [local irreducible] sampledObservedMaterializedDiagnostic in
theorem probEvent_sampledDiagnostic_successfulDoomed_le_root_add_nonRoot
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hq : q ≤ 2 ^ securityBits) :
    Pr[ObservedMaterializedDiagnostic.SuccessfulDoomed |
        sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] ≤
      Pr[ObservedMaterializedDiagnostic.HasExistingHiddenRootHit |
          sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] +
        Pr[ObservedMaterializedDiagnostic.HasExistingHiddenNonRootHit |
          sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] := by
  exact (probEvent_sampledDiagnostic_successfulDoomed_le_existingHiddenHit adversary parameter
    ftsSecret q hq).trans
      (probEvent_diagnostic_existingHidden_le_root_add_nonRoot
        (sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)))

attribute [local irreducible]
  observedMaterializedRetainedRunFromTable finishObservedMaterializedDiagnostic in
set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem observations_length_le_of_mem_sampledDiagnostic_before
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (outcome : ObservedMaterializedDiagnostic
      (RetainedGameResult × SplitHashCache))
    (result : ObservedCleanRunResult (RetainedGameResult × SplitHashCache))
    (houtcome : outcome ∈ support
      (sampledObservedMaterializedDiagnostic adversary parameter ftsSecret fuel))
    (hbefore : outcome.before = some result) :
    result.observations.length ≤ fuel := by
  change outcome ∈ support (sampleOtsHashTable >>= fun table =>
    observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table >>=
      finishObservedMaterializedDiagnostic table) at houtcome
  rw [mem_support_bind_iff] at houtcome
  obtain ⟨table, _htable, hfixed⟩ := houtcome
  exact observations_length_le_of_mem_diagnosticFromTable_before adversary parameter ftsSecret
    fuel table outcome result hfixed hbefore

attribute [local irreducible] sampledObservedMaterializedDiagnostic in
set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_sampledDiagnostic_existingHidden_le_sum_firstOrdinals
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[ObservedMaterializedDiagnostic.HasExistingHiddenHit |
        sampledObservedMaterializedDiagnostic adversary parameter ftsSecret fuel] ≤
      ∑ ordinal : Fin fuel,
        (Pr[ObservedMaterializedDiagnostic.FirstExistingHiddenRootHitOrdinal ordinal.val |
            sampledObservedMaterializedDiagnostic adversary parameter ftsSecret fuel] +
          Pr[ObservedMaterializedDiagnostic.FirstExistingHiddenNonRootHitOrdinal ordinal.val |
            sampledObservedMaterializedDiagnostic adversary parameter ftsSecret fuel]) := by
  classical
  let run := sampledObservedMaterializedDiagnostic adversary parameter ftsSecret fuel
  calc
    _ ≤ Pr[fun outcome => ∃ ordinal ∈ (Finset.univ : Finset (Fin fuel)),
          outcome.FirstExistingHiddenRootHitOrdinal ordinal.val ∨
            outcome.FirstExistingHiddenNonRootHitOrdinal ordinal.val | run] := by
      apply probEvent_mono
      intro outcome houtcome hhit
      rcases outcome.firstExistingHidden_root_or_nonRoot hhit with hroot | hnonRoot
      · obtain ⟨ordinal, result, sourceOrdinal, hbefore, hordinal, hfirst, hroot⟩ := hroot
        have hlength := observations_length_le_of_mem_sampledDiagnostic_before adversary parameter
          ftsSecret fuel outcome result houtcome hbefore
        have hlt : ordinal < fuel := by omega
        let bounded : Fin fuel := ⟨ordinal, hlt⟩
        exact ⟨bounded, Finset.mem_univ bounded, Or.inl
          ⟨result, sourceOrdinal, hbefore, hordinal, hfirst, hroot⟩⟩
      · obtain ⟨ordinal, result, sourceOrdinal, hbefore, hordinal, hfirst, hnonRoot⟩ :=
          hnonRoot
        have hlength := observations_length_le_of_mem_sampledDiagnostic_before adversary parameter
          ftsSecret fuel outcome result houtcome hbefore
        have hlt : ordinal < fuel := by omega
        let bounded : Fin fuel := ⟨ordinal, hlt⟩
        exact ⟨bounded, Finset.mem_univ bounded, Or.inr
          ⟨result, sourceOrdinal, hbefore, hordinal, hfirst, hnonRoot⟩⟩
    _ ≤ ∑ ordinal : Fin fuel,
          Pr[fun outcome =>
            outcome.FirstExistingHiddenRootHitOrdinal ordinal.val ∨
              outcome.FirstExistingHiddenNonRootHitOrdinal ordinal.val | run] :=
      probEvent_exists_finset_le_sum Finset.univ run fun (ordinal : Fin fuel) outcome =>
        outcome.FirstExistingHiddenRootHitOrdinal ordinal.val ∨
          outcome.FirstExistingHiddenNonRootHitOrdinal ordinal.val
    _ ≤ ∑ ordinal : Fin fuel,
          (Pr[ObservedMaterializedDiagnostic.FirstExistingHiddenRootHitOrdinal ordinal.val | run] +
            Pr[ObservedMaterializedDiagnostic.FirstExistingHiddenNonRootHitOrdinal ordinal.val |
              run]) := by
      apply Finset.sum_le_sum
      intro ordinal _hordinal
      exact probEvent_or_le _ _ _
    _ = _ := by simp only [run]

attribute [local irreducible] sampledObservedMaterializedDiagnostic in
set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_sampledDiagnostic_successfulDoomed_le_sum_successfulFirstOrdinals
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hq : q ≤ 2 ^ securityBits) :
    Pr[ObservedMaterializedDiagnostic.SuccessfulDoomed |
        sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] ≤
      ∑ ordinal : Fin (2 * q),
        (Pr[fun outcome => outcome.SuccessfulDoomed ∧
              outcome.FirstExistingHiddenRootHitAt ordinal.val |
            sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] +
          Pr[fun outcome => outcome.SuccessfulDoomed ∧
              outcome.FirstExistingHiddenNonRootHitAt ordinal.val |
            sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)]) := by
  classical
  let run := sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)
  calc
    _ ≤ Pr[fun outcome => ∃ ordinal ∈ (Finset.univ : Finset (Fin (2 * q))),
          (outcome.SuccessfulDoomed ∧
              outcome.FirstExistingHiddenRootHitAt ordinal.val) ∨
            (outcome.SuccessfulDoomed ∧
              outcome.FirstExistingHiddenNonRootHitAt ordinal.val) | run] := by
      apply probEvent_mono
      intro outcome houtcome hsuccess
      have hhit := hasExistingHiddenHit_of_mem_sampledDiagnostic_successfulDoomed adversary
        parameter ftsSecret q hq outcome houtcome hsuccess
      rcases outcome.firstExistingHidden_root_or_nonRoot hhit with hroot | hnonRoot
      · obtain ⟨ordinal, result, sourceOrdinal, hbefore, hordinal, hfirst, hroot⟩ := hroot
        have hlength := observations_length_le_of_mem_sampledDiagnostic_before adversary parameter
          ftsSecret (2 * q) outcome result houtcome hbefore
        have hlt : ordinal < 2 * q := by omega
        let bounded : Fin (2 * q) := ⟨ordinal, hlt⟩
        have hrootAt : outcome.FirstExistingHiddenRootHitAt ordinal :=
          outcome.firstExistingHiddenRootHitAt_of_ordinal
            ⟨result, sourceOrdinal, hbefore, hordinal, hfirst, hroot⟩
        exact ⟨bounded, Finset.mem_univ bounded, Or.inl ⟨hsuccess, hrootAt⟩⟩
      · obtain ⟨ordinal, result, sourceOrdinal, hbefore, hordinal, hfirst, hnonRoot⟩ :=
          hnonRoot
        have hlength := observations_length_le_of_mem_sampledDiagnostic_before adversary parameter
          ftsSecret (2 * q) outcome result houtcome hbefore
        have hlt : ordinal < 2 * q := by omega
        let bounded : Fin (2 * q) := ⟨ordinal, hlt⟩
        have hnonRootAt : outcome.FirstExistingHiddenNonRootHitAt ordinal :=
          outcome.firstExistingHiddenNonRootHitAt_of_ordinal
            ⟨result, sourceOrdinal, hbefore, hordinal, hfirst, hnonRoot⟩
        exact ⟨bounded, Finset.mem_univ bounded, Or.inr ⟨hsuccess, hnonRootAt⟩⟩
    _ ≤ ∑ ordinal : Fin (2 * q),
          Pr[fun outcome =>
            (outcome.SuccessfulDoomed ∧
                outcome.FirstExistingHiddenRootHitAt ordinal.val) ∨
              (outcome.SuccessfulDoomed ∧
                outcome.FirstExistingHiddenNonRootHitAt ordinal.val) | run] :=
      probEvent_exists_finset_le_sum Finset.univ run fun (ordinal : Fin (2 * q)) outcome =>
        (outcome.SuccessfulDoomed ∧
            outcome.FirstExistingHiddenRootHitAt ordinal.val) ∨
          (outcome.SuccessfulDoomed ∧
            outcome.FirstExistingHiddenNonRootHitAt ordinal.val)
    _ ≤ ∑ ordinal : Fin (2 * q),
          (Pr[fun outcome => outcome.SuccessfulDoomed ∧
                outcome.FirstExistingHiddenRootHitAt ordinal.val | run] +
            Pr[fun outcome => outcome.SuccessfulDoomed ∧
                outcome.FirstExistingHiddenNonRootHitAt ordinal.val | run]) := by
      apply Finset.sum_le_sum
      intro ordinal _hordinal
      exact probEvent_or_le _ _ _
    _ = _ := by simp only [run]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem relTriple_sampledGranularAllCanonical_diagnosticRootRel
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ root,
      (retainedGameRestComputation adversary ⟨root, parameter⟩).IsQueryBoundP
        IsOuterHash q) :
    RelTriple
      (sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q)
      (sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q))
      SnapshotObservedDiagnosticRootRel := by
  unfold sampledGranularAllCanonicalPrivateWitnessSnapshot
    sampledObservedMaterializedDiagnostic
  apply relTriple_bind (relTriple_refl sampleOtsHashTable)
  intro leftTable rightTable htable
  subst rightTable
  exact relTriple_granularAllCanonical_diagnosticRootRel adversary parameter ftsSecret q
    leftTable hbound

theorem probEvent_sampledCanonical_root_le_diagnostic
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ root,
      (retainedGameRestComputation adversary ⟨root, parameter⟩).IsQueryBoundP
        IsOuterHash q) :
    Pr[fun output =>
        WitnessFirstUsesSomeLayerRoot (erasePrivateWitnessSnapshotOutput output) |
      sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] ≤
      Pr[fun outcome => outcome.final = none |
        sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] +
      Pr[ObservedMaterializedDiagnostic.SuccessfulDoomed |
        sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] +
      Pr[WitnessFirstUsesSomeDelayedLayerRootSnapshot |
        sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] := by
  let source := sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q
  let diagnostic :=
    sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)
  have hsplit :
      Pr[fun output =>
          WitnessFirstUsesSomeLayerRoot (erasePrivateWitnessSnapshotOutput output) | source] ≤
        Pr[ObservedMaterializedDiagnostic.Bad | diagnostic] +
          Pr[WitnessFirstUsesSomeDelayedLayerRootSnapshot | source] := by
    apply probEvent_le_failure_add_residual_of_relTriple source diagnostic
      SnapshotObservedDiagnosticRootRel
      (fun output =>
        WitnessFirstUsesSomeLayerRoot (erasePrivateWitnessSnapshotOutput output))
      WitnessFirstUsesSomeDelayedLayerRootSnapshot
      ObservedMaterializedDiagnostic.Bad
      (relTriple_sampledGranularAllCanonical_diagnosticRootRel adversary parameter ftsSecret q
        hbound)
    intro sourceOutput diagnosticOutput hrelation hroot hnotDelayed
    rcases hrelation with hbad | himplication
    · exact hbad
    · exact False.elim (hnotDelayed (himplication hroot))
  calc
    _ ≤ Pr[ObservedMaterializedDiagnostic.Bad | diagnostic] +
          Pr[WitnessFirstUsesSomeDelayedLayerRootSnapshot | source] := hsplit
    _ ≤ (Pr[fun outcome => outcome.final = none | diagnostic] +
          Pr[ObservedMaterializedDiagnostic.SuccessfulDoomed | diagnostic]) +
          Pr[WitnessFirstUsesSomeDelayedLayerRootSnapshot | source] := by
      gcongr
      exact probEvent_diagnosticBad_le_finalNone_add_successfulDoomed diagnostic
    _ = _ := by
      simp only [source, diagnostic]

end SphincsSecurity.Concrete.OtsProbeSimulation

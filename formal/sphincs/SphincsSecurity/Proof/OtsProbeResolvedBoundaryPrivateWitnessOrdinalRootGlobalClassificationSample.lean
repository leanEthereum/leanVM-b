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

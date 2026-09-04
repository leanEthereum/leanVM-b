import SphincsSecurity.Proof.OtsProbeJointTop

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option linter.constructorNameAsVariable false

attribute [local irreducible] maskedPublishedTreeRoot
  sampledGranularAllCanonicalBoundaryWitnessSnapshot
  sampledGranularAllCanonicalPrivateWitnessSnapshot sampledObservedMaterializedDiagnostic

attribute [local irreducible] observedMaterializedRetainedRunFromTable in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem tracked_of_mem_diagnosticFromTable_before
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (outcome : ObservedMaterializedDiagnostic
      (RetainedGameResult × SplitHashCache))
    (result : ObservedCleanRunResult (RetainedGameResult × SplitHashCache))
    (houtcome : outcome ∈ support
      (observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table >>=
        finishObservedMaterializedDiagnostic table))
    (hbefore : outcome.before = some result) :
    CleanProbeObservationsTrackedBy result.observations result.state := by
  rw [mem_support_bind_iff] at houtcome
  obtain ⟨before?, hbeforeSupport, hfinish⟩ := houtcome
  cases before? with
  | none =>
      have houtcomeEq : outcome = ⟨none, none, false⟩ := by
        simpa [finishObservedMaterializedDiagnostic] using hfinish
      rw [houtcomeEq] at hbefore
      simp at hbefore
  | some before =>
      unfold finishObservedMaterializedDiagnostic at hfinish
      rw [mem_support_bind_iff] at hfinish
      obtain ⟨final?, _hfinal, hreturn⟩ := hfinish
      simp only [support_pure, Set.mem_singleton_iff] at hreturn
      have hbeforeEq : outcome.before = some before := by
        simpa using congrArg ObservedMaterializedDiagnostic.before hreturn
      have heq : before = result := Option.some.inj (hbeforeEq.symm.trans hbefore)
      subst result
      simpa only [ObservedMaterializedOutputTracked] using
        observedMaterializedOutputTracked_of_mem_retainedRunFromTable adversary parameter
          ftsSecret fuel table (some before) hbeforeSupport

attribute [local irreducible] observedMaterializedRetainedRunFromTable in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem tracked_of_mem_sampledDiagnostic_before
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (outcome : ObservedMaterializedDiagnostic
      (RetainedGameResult × SplitHashCache))
    (result : ObservedCleanRunResult (RetainedGameResult × SplitHashCache))
    (houtcome : outcome ∈ support
      (sampledObservedMaterializedDiagnostic adversary parameter ftsSecret fuel))
    (hbefore : outcome.before = some result) :
    CleanProbeObservationsTrackedBy result.observations result.state := by
  unfold sampledObservedMaterializedDiagnostic at houtcome
  change outcome ∈ support (sampleOtsHashTable >>= fun table =>
    observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table >>=
      finishObservedMaterializedDiagnostic table) at houtcome
  rw [mem_support_bind_iff] at houtcome
  obtain ⟨table, _htable, hfixed⟩ := houtcome
  exact tracked_of_mem_diagnosticFromTable_before adversary parameter ftsSecret
    fuel table outcome result hfixed hbefore


set_option maxRecDepth 100000 in
theorem witnessSnapshot_mem_support_of_mem_joint
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (output : BoundaryWitnessSnapshotOutput)
    (houtput : output ∈ support
      (sampledGranularAllCanonicalBoundaryWitnessSnapshot adversary parameter ftsSecret fuel)) :
    output.witnessSnapshot ∈ support
      (sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret fuel) := by
  apply (mem_support_iff_of_evalDist_eq
    (evalDist_witnessSnapshot_sampledGranularAllCanonicalBoundaryWitnessSnapshot adversary
      parameter ftsSecret fuel) output.witnessSnapshot).1
  rw [support_map]
  exact ⟨output, houtput, rfl⟩

set_option maxRecDepth 100000 in
theorem sourceSnapshotStopInvariant_of_mem_joint
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (output : BoundaryWitnessSnapshotOutput)
    (houtput : output ∈ support
      (sampledGranularAllCanonicalBoundaryWitnessSnapshot adversary parameter ftsSecret fuel)) :
    SourceSnapshotStopInvariant output.witnessSnapshot := by
  have hsource := witnessSnapshot_mem_support_of_mem_joint adversary parameter ftsSecret fuel
    output houtput
  unfold sampledGranularAllCanonicalPrivateWitnessSnapshot at hsource
  rw [mem_support_bind_iff] at hsource
  obtain ⟨table, _, hfixed⟩ := hsource
  exact sourceSnapshotStopInvariant_of_mem_granularAllCanonical adversary parameter table
    ftsSecret fuel output.witnessSnapshot hfixed

set_option maxRecDepth 100000 in
theorem relTriple_sampledJointSnapshot_diagnostic
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q) :
    RelTriple
      (sampledGranularAllCanonicalBoundaryWitnessSnapshot adversary parameter ftsSecret q)
      (sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q))
      (fun source diagnostic => ∃ table, BoundarySnapshotDiagnosticRel table source diagnostic) := by
  unfold sampledGranularAllCanonicalBoundaryWitnessSnapshot sampledObservedMaterializedDiagnostic
  apply relTriple_bind (relTriple_refl sampleOtsHashTable)
  intro leftTable rightTable heq
  subst rightTable
  apply relTriple_post_mono
    (relTriple_granularAllJointSnapshot_diagnostic adversary parameter ftsSecret q leftTable
      (hbound leftTable))
  intro source diagnostic hrelation
  exact ⟨leftTable, hrelation⟩

def JointSnapshotResidual (source : BoundaryWitnessSnapshotOutput) : Prop :=
  WitnessFirstUsesSomeDelayedLayerRootSnapshot source.witnessSnapshot ∨
    WitnessFirstUsesSomeNonLayerRoot (erasePrivateWitnessSnapshotOutput source.witnessSnapshot)

set_option maxRecDepth 100000 in
theorem relTriple_sampledJointSnapshot_failure_classification
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q) :
    RelTriple
      (sampledGranularAllCanonicalBoundaryWitnessSnapshot adversary parameter ftsSecret q)
      (sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q))
      (fun source diagnostic => diagnostic.Bad ∨
        (source.outcome.failed = true → JointSnapshotResidual source)) := by
  have hbase := relTriple_sampledJointSnapshot_diagnostic adversary parameter ftsSecret q hbound
  have hleft := SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
    (fun output => output ∈ support
      (sampledGranularAllCanonicalBoundaryWitnessSnapshot adversary parameter ftsSecret q))
    (fun _ houtput => houtput)
  have hboth := SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleft
  apply relTriple_post_mono hboth
  intro source diagnostic hfacts
  obtain ⟨⟨⟨table, hrelation⟩, hsource⟩, hdiagnostic⟩ := hfacts
  rcases hrelation with hbad | ⟨⟨result, aligned, hbefore, hprefix, haligned, hstored⟩, hprivate⟩
  · exact Or.inl hbad
  · right
    intro hfailed
    have hcovered := privateWitnessCovered_erase_of_mem_sampledGranularAllCanonical adversary
      parameter ftsSecret q source.witnessSnapshot
      (witnessSnapshot_mem_support_of_mem_joint adversary parameter ftsSecret q source hsource)
    have hwitness : (erasePrivateWitnessSnapshotOutput source.witnessSnapshot).1.isSome = true :=
      hprivate hfailed
    rcases witnessFirstUsesSome_root_or_nonRoot hcovered hwitness with hroot | hnonRoot
    · have hvalue : SnapshotObservedPrefixValueRel table source.witnessSnapshot diagnostic.before :=
        Or.inr ⟨result, aligned, hbefore, hprefix, haligned, hstored⟩
      have hrootRel := hvalue.to_rootRel
        (sourceSnapshotStopInvariant_of_mem_joint adversary parameter ftsSecret q source hsource)
        (fun before hbefore => tracked_of_mem_sampledDiagnostic_before adversary parameter
          ftsSecret (2 * q) diagnostic before hdiagnostic hbefore)
      rcases hrootRel with hnone | hdelayed
      · rw [hbefore] at hnone
        cases hnone
      · exact Or.inl (hdelayed hroot)
    · exact Or.inr hnonRoot

set_option maxRecDepth 100000 in
theorem probEvent_sampledJointSnapshot_failed_le_diagnostic_add_residual
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q) :
    Pr[fun output => output.outcome.failed = true |
        sampledGranularAllCanonicalBoundaryWitnessSnapshot adversary parameter ftsSecret q] ≤
      Pr[ObservedMaterializedDiagnostic.Bad |
        sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] +
      Pr[JointSnapshotResidual |
        sampledGranularAllCanonicalBoundaryWitnessSnapshot adversary parameter ftsSecret q] := by
  apply probEvent_le_failure_add_residual_of_relTriple _ _
    (fun source diagnostic => diagnostic.Bad ∨
      (source.outcome.failed = true → JointSnapshotResidual source)) _ _ _
    (relTriple_sampledJointSnapshot_failure_classification adversary parameter ftsSecret q hbound)
  intro source diagnostic hrelation hfailed hnotResidual
  rcases hrelation with hbad | hresidual
  · exact hbad
  · exact (hnotResidual (hresidual hfailed)).elim

end SphincsSecurity.Concrete.OtsProbeSimulation

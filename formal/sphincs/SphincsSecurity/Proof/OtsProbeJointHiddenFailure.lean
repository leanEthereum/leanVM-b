import SphincsSecurity.Proof.OtsProbeJointDisjointCharge

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local irreducible] sampledGranularAllCanonicalBoundaryWitnessSnapshot
  sampledGranularAllCanonicalPrivateWitnessSnapshot
  sampledObservedMaterializedDiagnostic observedMaterializedRetainedRunFromTable
  sampledActualRetainedOtsHashTable

set_option maxRecDepth 100000

theorem existingHiddenHit_of_aligned_privateWitness
    {output : PrivateWitnessPlanOutput} {result : ObservedCleanRunResult α}
    (witness : PrivateHitWitness) (sourceOrdinal : Fin output.2.length)
    (hfirst : firstPrivateWitnessOrdinal? witness output.2 = some sourceOrdinal)
    (halign : output.2.IsPrefix (result.observations.map CleanProbeObservation.toProbe))
    (htracked : CleanProbeObservationsTrackedBy result.observations result.state)
    (hstored : result.state.values (.position witness.position) = some witness.output)
    (hselectedHidden : ∀ (observationOrdinal : Fin result.observations.length),
      sourceOrdinal.val = observationOrdinal.val →
      (result.observations.get observationOrdinal).revealedAtProbe = false) :
    result.HasExistingHiddenHit := by
  have hlength : output.2.length ≤ result.observations.length := by simpa using halign.length_le
  let observationOrdinal : Fin result.observations.length :=
    ⟨sourceOrdinal.val, sourceOrdinal.isLt.trans_le hlength⟩
  have hprobe : (result.observations.get observationOrdinal).toProbe = output.2.get sourceOrdinal := by
    rw [List.get_eq_getElem, List.get_eq_getElem]
    change (result.observations[sourceOrdinal.val]).toProbe = output.2[sourceOrdinal.val]
    rw [halign.getElem sourceOrdinal.isLt, List.getElem_map]
  have hmatch := privateWitnessAtOrdinal_of_firstPrivateWitnessOrdinal?_eq_some hfirst
  have hcoordinate : (result.observations.get observationOrdinal).coordinate = .position witness.position :=
    (congrArg Probe.coordinate hprobe).trans hmatch.1
  have hcandidate : (result.observations.get observationOrdinal).candidate = truncateHash witness.output :=
    (congrArg Probe.candidate hprobe).trans hmatch.2.symm
  have hhidden := hselectedHidden observationOrdinal rfl
  have htrackedAt := htracked (result.observations.get observationOrdinal) (List.get_mem _ _)
  cases hvalue : (result.observations.get observationOrdinal).valueAtProbe with
  | none =>
      have hfinal : result.state.values (result.observations.get observationOrdinal).coordinate = some witness.output := by
        rw [hcoordinate]
        exact hstored
      exact False.elim ((CleanProbeObservation.resolvedSafe_of_trackedBy htrackedAt
        hvalue hhidden witness.output hfinal) hcandidate.symm)
  | some stored =>
      have hstoredAtFinal := htrackedAt.1 stored hvalue
      rw [hcoordinate] at hstoredAtFinal
      have heq : stored = witness.output := Option.some.inj (hstoredAtFinal.symm.trans hstored)
      subst stored
      exact ⟨result.observations.get observationOrdinal, List.get_mem _ _, hhidden,
        witness.output, hvalue, hcandidate.symm⟩

def ObservedMaterializedDiagnostic.SuccessfulHiddenHit
    (outcome : ObservedMaterializedDiagnostic α) : Prop :=
  outcome.final.isSome = true ∧ outcome.HasExistingHiddenHit

namespace BoundaryDiagnosticCoupling

variable {adversary : Adversary} {parameter : PublicParameter}
  {ftsSecret : Index → FtsTree → FtsLeaf → Digest} {q : Nat}
  (joint : BoundaryDiagnosticCoupling adversary parameter ftsSecret q)

theorem residualFailure_has_existingHiddenHit (pair : BoundaryDiagnosticPair)
    (hpair : pair ∈ support joint.law) (hresidual : ResidualFailure pair) :
    pair.2.HasExistingHiddenHit := by
  obtain ⟨table, hrelation, _, _⟩ := joint.aligned pair hpair
  rcases hrelation with hbad | ⟨⟨result, aligned, hbefore, hprefix, haligned, hstored⟩, hprivate⟩
  · exact (hresidual.2 hbad).elim
  · have hsource := joint.source_mem_support pair hpair
    have hcovered := privateWitnessCovered_erase_of_mem_sampledGranularAllCanonical adversary parameter ftsSecret q
      pair.1.witnessSnapshot (witnessSnapshot_mem_support_of_mem_joint adversary parameter ftsSecret q pair.1 hsource)
    have hwitnessSome := hprivate hresidual.1
    cases hwitness : pair.1.witnessSnapshot.1 with
    | none => simp [hwitness] at hwitnessSome
    | some witness =>
        have hwitness' : (erasePrivateWitnessSnapshotOutput pair.1.witnessSnapshot).1 = some witness := hwitness
        obtain ⟨sourceOrdinal, hfirst, _⟩ := firstPrivateWitnessOrdinal?_eq_some_of_candidateListHits witness
          (erasePrivateWitnessSnapshotOutput pair.1.witnessSnapshot).2 (hcovered witness hwitness')
        let trimmed : ObservedCleanRunResult (RetainedGameResult × SplitHashCache) :=
          { result with observations := aligned }
        have htracked : CleanProbeObservationsTrackedBy trimmed.observations trimmed.state := by
          intro observation hobservation
          exact tracked_of_mem_sampledDiagnostic_before adversary parameter ftsSecret (2 * q) pair.2 result
            (joint.diagnostic_mem_support pair hpair) hbefore observation (hprefix.subset hobservation)
        have halign : (erasePrivateWitnessSnapshotOutput pair.1.witnessSnapshot).2.IsPrefix
            (trimmed.observations.map CleanProbeObservation.toProbe) := by
          change pair.1.witnessSnapshot.2.map PlannedProbeSnapshot.toProbe <+:
            aligned.map CleanProbeObservation.toProbe
          rw [haligned.map_toProbe_eq]
        have hhidden := selectedObservationHidden_of_sourceSnapshotStopInvariant
          (sourceSnapshotStopInvariant_of_mem_joint adversary parameter ftsSecret q pair.1 hsource) haligned
        have hhit := existingHiddenHit_of_aligned_privateWitness witness sourceOrdinal hfirst halign htracked
          (hstored witness hwitness) (fun ordinal heq => hhidden witness sourceOrdinal ordinal hwitness' heq hfirst)
        obtain ⟨observation, hobservation, hhit⟩ := hhit
        exact ⟨result, hbefore, observation, hprefix.subset hobservation, hhit⟩

theorem failed_le_finalNone_or_successfulHiddenHit (hq : q ≤ 2 ^ 126)
    (pair : BoundaryDiagnosticPair) (hpair : pair ∈ support joint.law) (hfailed : pair.1.outcome.failed = true) :
    pair.2.final = none ∨ pair.2.SuccessfulHiddenHit := by
  cases hfinal : pair.2.final with
  | none => exact Or.inl rfl
  | some result =>
      right
      refine ⟨by simp [hfinal], ?_⟩
      by_cases hdoomed : pair.2.wasDoomed = true
      · exact Range125.hasExistingHiddenHit_of_mem_sampledDiagnostic_successfulDoomed adversary parameter ftsSecret q hq
          pair.2 (joint.diagnostic_mem_support pair hpair) ⟨by simp [hfinal], hdoomed⟩
      · apply joint.residualFailure_has_existingHiddenHit pair hpair
        exact ⟨hfailed, by simp [ObservedMaterializedDiagnostic.Bad, hfinal, hdoomed]⟩

include joint in
theorem probEvent_failed_le_finalNone_add_successfulHiddenHit (hq : q ≤ 2 ^ 126) :
    Pr[fun source => source.outcome.failed = true |
      sampledGranularAllCanonicalBoundaryWitnessSnapshot adversary parameter ftsSecret q] ≤
      Pr[fun outcome => outcome.final = none | sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] +
        Pr[ObservedMaterializedDiagnostic.SuccessfulHiddenHit |
          sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] := by
  rw [← joint.probEvent_source, ← joint.probEvent_diagnostic (fun outcome => outcome.final = none),
    ← joint.probEvent_diagnostic ObservedMaterializedDiagnostic.SuccessfulHiddenHit]
  exact (probEvent_mono (joint.failed_le_finalNone_or_successfulHiddenHit hq)).trans (probEvent_or_le _ _ _)

end BoundaryDiagnosticCoupling

theorem probEvent_sampledActualRetained_verifyProbe_le_charge_add_successfulHiddenHit126
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ table root,
      (simulateQ (SphincsSecurity.expandedAdversaryImpl
        (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ 126) :
    Pr[fun result => WinningRetainedVerifyProbeWitness parameter (extendStartTable result.1) ftsSecret result.2 |
      sampledActualRetainedOtsHashTable adversary parameter ftsSecret] ≤
      materializedRetainedCharge adversary parameter ftsSecret (2 * q) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
        Pr[ObservedMaterializedDiagnostic.SuccessfulHiddenHit |
          sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] := by
  let joint := boundaryDiagnosticCoupling adversary parameter ftsSecret q hbound
  exact (probEvent_sampledActualRetained_verifyProbe_le_jointBoundaryFailed adversary parameter ftsSecret q).trans
    ((joint.probEvent_failed_le_finalNone_add_successfulHiddenHit hq).trans
      (add_le_add (probEvent_sampledDiagnostic_final_none_le_charge adversary parameter ftsSecret (2 * q) q hbound (by omega)) le_rfl))

theorem probEvent_sampledActualRetained_verifyProbe_le_charge_add_successfulHiddenHit126_of_hashQueryBound
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 126)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    Pr[fun result => WinningRetainedVerifyProbeWitness parameter (extendStartTable result.1) ftsSecret result.2 |
      sampledActualRetainedOtsHashTable adversary parameter ftsSecret] ≤
      materializedRetainedCharge adversary parameter ftsSecret (2 * q) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
        Pr[ObservedMaterializedDiagnostic.SuccessfulHiddenHit |
          sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] :=
  probEvent_sampledActualRetained_verifyProbe_le_charge_add_successfulHiddenHit126 adversary parameter ftsSecret q
    (fun table root => isQueryBoundP_expandedRetained_all_tables_roots adversary q hq parameter hparameter table ftsSecret hfts root) hqMax

end SphincsSecurity.Concrete.OtsProbeSimulation

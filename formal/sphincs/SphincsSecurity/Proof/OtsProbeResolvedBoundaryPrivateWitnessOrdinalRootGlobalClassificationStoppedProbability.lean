import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedSelection

/-!
# Probability interface for stopped structural ordinals

Only source ordinals below the outer hash-query bound can occur. This removes the comparison
interpreter's extra fuel from the union and packages the remaining quantitative obligation as one
fixed-ordinal selected-snapshot estimate.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local irreducible] maskedPublishedTreeRoot
set_option maxRecDepth 1000000
set_option linter.constructorNameAsVariable false

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem snapshots_length_le_of_mem_granularAllCanonical
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ root,
      (retainedGameRestComputation adversary ⟨root, parameter⟩).IsQueryBoundP
        IsOuterHash q)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret q)) :
    output.2.length ≤ q := by
  classical
  unfold granularAllCanonicalPrivateWitnessSnapshot runDirectWitnessSnapshotObserve at houtput
  rw [mem_support_bind_iff] at houtput
  obtain ⟨result, _hresult, hfinish⟩ := houtput
  cases result with
  | stoppedFuel =>
      simp [finishDirectWitnessSnapshotObserve] at hfinish
      subst output
      simp
  | stoppedOrdinary =>
      simp [finishDirectWitnessSnapshotObserve] at hfinish
      subst output
      simp
  | stoppedPrivate witness =>
      simp [finishDirectWitnessSnapshotObserve] at hfinish
      subst output
      simp
  | done resolved =>
      simp only [finishDirectWitnessSnapshotObserve] at hfinish
      unfold canonicalizeDirectWitnessSnapshotObserve at hfinish
      let canonical := canonicalizeMaterializedValues table resolved.context
      change output ∈ support
        (if hhit : PrivateStructuralHit canonical then
          pure (some (privateHitWitnessOf canonical hhit), [])
        else if PublishedValues resolved.context.state then
          classifyDirectWitnessSnapshotObserve table
            (granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve adversary
              parameter table ftsSecret)
            canonical resolved.remaining resolved.value []
        else pure (none, [])) at hfinish
      by_cases hhit : PrivateStructuralHit canonical
      · simp [hhit] at hfinish
        subst output
        simp
      · simp only [hhit, ↓reduceDIte] at hfinish
        by_cases hpublished : PublishedValues resolved.context.state
        · simp only [hpublished, ↓reduceIte] at hfinish
          unfold classifyDirectWitnessSnapshotObserve at hfinish
          simp only [hhit, ↓reduceDIte] at hfinish
          by_cases hcompletable : DeferredCompletable table canonical
          · simp only [hcompletable, ↓reduceIte] at hfinish
            have herased : erasePrivateWitnessSnapshotOutput output ∈ support
                (granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve adversary
                  parameter table ftsSecret canonical resolved.remaining resolved.value []) := by
              have hmap :=
                map_erase_granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve
                  adversary parameter table ftsSecret canonical resolved.remaining resolved.value
                  []
              have hmap' :
                  erasePrivateWitnessSnapshotOutput <$>
                      granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve
                        adversary parameter table ftsSecret canonical resolved.remaining
                        resolved.value [] =
                    granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve adversary
                      parameter table ftsSecret canonical resolved.remaining resolved.value [] := by
                simpa using hmap
              rw [← hmap', support_map]
              exact ⟨output, hfinish, rfl⟩
            have hlength :=
              support_granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve_length_le
                adversary parameter table ftsSecret canonical resolved.remaining resolved.value
                [] q (hbound resolved.value.1) (erasePrivateWitnessSnapshotOutput output) herased
            simpa [erasePrivateWitnessSnapshotOutput] using hlength
          · simp [hcompletable] at hfinish
            subst output
            simp
        · simp [hpublished] at hfinish
          subst output
          simp

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem snapshots_length_le_of_mem_sampledGranularAllCanonical
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ root,
      (retainedGameRestComputation adversary ⟨root, parameter⟩).IsQueryBoundP
        IsOuterHash q)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q)) :
    output.2.length ≤ q := by
  unfold sampledGranularAllCanonicalPrivateWitnessSnapshot at houtput
  rw [mem_support_bind_iff] at houtput
  obtain ⟨table, _htable, hrest⟩ := houtput
  exact snapshots_length_le_of_mem_granularAllCanonical adversary parameter table ftsSecret q
    hbound output hrest

set_option maxHeartbeats 2000000 in
theorem probEvent_selectedPrivateSnapshotHitAt_eq_zero_of_q_le_ordinal
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q ordinal : Nat)
    (hbound : ∀ root,
      (retainedGameRestComputation adversary ⟨root, parameter⟩).IsQueryBoundP
        IsOuterHash q)
    (hordinal : q ≤ ordinal) :
    Pr[fun source => SelectedPrivateSnapshotHitAt source ordinal |
        sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] = 0 := by
  classical
  apply probEvent_eq_zero
  intro source hsource hselected
  obtain ⟨selected, hselectedOrdinal, _⟩ := hselected
  unfold sampledGranularAllCanonicalPrivateWitnessSnapshot at hsource
  rw [mem_support_bind_iff] at hsource
  obtain ⟨table, _htable, hsource⟩ := hsource
  have hlength : source.2.length ≤ q :=
    snapshots_length_le_of_mem_granularAllCanonical
      (adversary := adversary) (parameter := parameter) (table := table)
      (ftsSecret := ftsSecret) (q := q) (hbound := hbound) (output := source)
      (houtput := hsource)
  have : ordinal < q := by
    rw [← hselectedOrdinal]
    exact selected.isLt.trans_le hlength
  omega

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_sampledDiagnostic_successfulDoomed_le_of_selected_ordinals
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ root,
      (retainedGameRestComputation adversary ⟨root, parameter⟩).IsQueryBoundP
        IsOuterHash q)
    (hq : q ≤ 2 ^ securityBits)
    (hordinal : ∀ ordinal : Fin q,
      Pr[fun source => SelectedPrivateSnapshotHitAt source ordinal.val |
          sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] ≤
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹) :
    Pr[ObservedMaterializedDiagnostic.SuccessfulDoomed |
        sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] ≤
      (q : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  classical
  let diagnostic :=
    sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)
  let source :=
    sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q
  calc
    _ ≤ ∑ ordinal : Fin (2 * q),
        Pr[fun outcome => outcome.SuccessfulDoomed ∧
            outcome.FirstExistingHiddenHitAt ordinal.val | diagnostic] :=
      probEvent_sampledDiagnostic_successfulDoomed_le_sum_firstHits adversary parameter ftsSecret
        q hq
    _ ≤ ∑ ordinal : Fin (2 * q),
        Pr[fun selected => SelectedPrivateSnapshotHitAt selected ordinal.val | source] := by
      apply Finset.sum_le_sum
      intro ordinal _hordinal
      calc
        _ ≤ Pr[ObservedCleanRunOption.SuccessfulFirstExistingHiddenHitAt ordinal.val | do
              let table ← sampleOtsHashTable
              observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q)
                table] :=
          probEvent_sampledDiagnostic_successfulDoomed_firstExistingHiddenHitAt_le_raw adversary
            parameter ftsSecret (2 * q) ordinal.val
        _ ≤ _ := probEvent_sampledSuccessfulFirstHit_le_selectedSnapshot adversary parameter
          ftsSecret q ordinal.val hbound hq
    _ = ∑ ordinal : Fin q,
        Pr[fun selected => SelectedPrivateSnapshotHitAt selected ordinal.val | source] := by
      simp only [Finset.sum_fin_eq_sum_range]
      rw [show 2 * q = q + q by omega, Finset.sum_range_add]
      have hfirst :
          (∑ ordinal ∈ Finset.range q, if h : ordinal < q + q then
              Pr[fun selected => SelectedPrivateSnapshotHitAt selected ordinal | source]
            else 0) =
            ∑ ordinal ∈ Finset.range q, if h : ordinal < q then
              Pr[fun selected => SelectedPrivateSnapshotHitAt selected ordinal | source]
            else 0 := by
        apply Finset.sum_congr rfl
        intro ordinal hordinalMem
        have hlt : ordinal < q := Finset.mem_range.1 hordinalMem
        have hlt' : ordinal < q + q := hlt.trans_le (Nat.le_add_right q q)
        simp [hlt, hlt']
      have hzero :
          (∑ ordinal ∈ Finset.range q, if h : q + ordinal < q + q then
              Pr[fun selected => SelectedPrivateSnapshotHitAt selected (q + ordinal) | source]
            else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro ordinal hordinalMem
        have hlt : ordinal < q := Finset.mem_range.1 hordinalMem
        simp only [show q + ordinal < q + q by omega, ↓reduceDIte]
        exact probEvent_selectedPrivateSnapshotHitAt_eq_zero_of_q_le_ordinal adversary parameter
          ftsSecret q (q + ordinal) hbound (by omega)
      rw [hfirst, hzero, add_zero]
    _ ≤ ∑ _ordinal : Fin q, ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
      apply Finset.sum_le_sum
      intro ordinal _hordinal
      exact hordinal ordinal
    _ = _ := by simp

set_option maxHeartbeats 2000000 in
theorem probEvent_sampledDiagnostic_bad_le_of_selected_ordinals
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ root,
      (retainedGameRestComputation adversary ⟨root, parameter⟩).IsQueryBoundP
        IsOuterHash q)
    (hq : q ≤ 2 ^ securityBits)
    (hordinal : ∀ ordinal : Fin q,
      Pr[fun source => SelectedPrivateSnapshotHitAt source ordinal.val |
          sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] ≤
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹) :
    Pr[ObservedMaterializedDiagnostic.Bad |
        sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] ≤
      ((3 * q : Nat) : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  let diagnostic :=
    sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)
  calc
    _ ≤ Pr[fun outcome => outcome.final = none | diagnostic] +
          Pr[ObservedMaterializedDiagnostic.SuccessfulDoomed | diagnostic] :=
      probEvent_diagnosticBad_le_finalNone_add_successfulDoomed diagnostic
    _ ≤ ((2 * q : Nat) : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
          (q : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
      apply add_le_add
      · exact probEvent_sampledObservedMaterializedDiagnostic_final_none_le adversary parameter
          ftsSecret (2 * q) q hbound (by omega)
      · exact probEvent_sampledDiagnostic_successfulDoomed_le_of_selected_ordinals adversary
          parameter ftsSecret q hbound hq hordinal
    _ = _ := by
      push_cast
      ring

end SphincsSecurity.Concrete.OtsProbeSimulation

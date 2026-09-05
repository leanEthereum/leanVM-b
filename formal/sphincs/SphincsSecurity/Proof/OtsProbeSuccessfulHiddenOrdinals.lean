import SphincsSecurity.Proof.OtsProbeJointHiddenFailure

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local irreducible] sampledObservedMaterializedDiagnostic
  sampledGranularAllCanonicalPrivateWitnessSnapshot observedMaterializedRetainedRunFromTable

set_option maxRecDepth 100000

theorem probEvent_finishDiagnostic_successfulHidden_firstHit_le
    (table : OtsSecretIndex → HashOutput)
    (run : ProbComp (Option (ObservedCleanRunResult α))) (ordinal : Nat) :
    Pr[fun outcome => outcome.SuccessfulHiddenHit ∧ outcome.FirstExistingHiddenHitAt ordinal |
      run >>= finishObservedMaterializedDiagnostic table] ≤
      Pr[ObservedCleanRunOption.SuccessfulFirstExistingHiddenHitAt ordinal | run] := by
  classical
  apply probEvent_bind_le_probEvent
  intro before _hbefore hnot
  apply probEvent_eq_zero
  intro outcome houtcome hevent
  cases before with
  | none =>
      have heq : outcome = ⟨none, none, false⟩ := by simpa [finishObservedMaterializedDiagnostic] using houtcome
      subst outcome
      simp [ObservedMaterializedDiagnostic.SuccessfulHiddenHit] at hevent
  | some before =>
      unfold finishObservedMaterializedDiagnostic at houtcome
      rw [mem_support_bind_iff] at houtcome
      obtain ⟨final, hfinal, hreturn⟩ := houtcome
      simp only [mem_support_pure_iff] at hreturn
      subst outcome
      obtain ⟨⟨hsome, _⟩, firstResult, hfirstBefore, hfirst⟩ := hevent
      have heq : firstResult = before := (Option.some.inj hfirstBefore).symm
      subst firstResult
      cases final with
      | none => simp at hsome
      | some final => exact hnot ⟨⟨final, hfinal⟩, hfirst⟩

theorem probEvent_sampledDiagnostic_successfulHidden_firstHit_le_raw
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel ordinal : Nat) :
    Pr[fun outcome => outcome.SuccessfulHiddenHit ∧ outcome.FirstExistingHiddenHitAt ordinal |
      sampledObservedMaterializedDiagnostic adversary parameter ftsSecret fuel] ≤
      Pr[ObservedCleanRunOption.SuccessfulFirstExistingHiddenHitAt ordinal | do
        let table ← sampleOtsHashTable
        observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table] := by
  unfold sampledObservedMaterializedDiagnostic
  rw [probEvent_bind_eq_tsum (mx := sampleOtsHashTable), probEvent_bind_eq_tsum (mx := sampleOtsHashTable)]
  exact ENNReal.tsum_le_tsum fun table => mul_le_mul' le_rfl
    (probEvent_finishDiagnostic_successfulHidden_firstHit_le table
      (observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table) ordinal)

theorem probEvent_sampledDiagnostic_successfulHidden_firstHit_le_selectedSnapshot126
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q ordinal : Nat)
    (hbound : ∀ table root,
      (simulateQ (SphincsSecurity.expandedAdversaryImpl
        (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ 126) :
    Pr[fun outcome => outcome.SuccessfulHiddenHit ∧ outcome.FirstExistingHiddenHitAt ordinal |
      sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] ≤
      Pr[fun source => SelectedPrivateSnapshotHitAt source ordinal |
        sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] :=
  (probEvent_sampledDiagnostic_successfulHidden_firstHit_le_raw adversary parameter ftsSecret (2 * q) ordinal).trans
    (Range125.probEvent_sampledSuccessfulFirstHit_le_selectedSnapshot adversary parameter ftsSecret q ordinal hbound hq)

theorem probEvent_sampledDiagnostic_successfulHidden_le_sum_firstHits126
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ table root,
      (simulateQ (SphincsSecurity.expandedAdversaryImpl
        (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ 126) :
    Pr[ObservedMaterializedDiagnostic.SuccessfulHiddenHit |
      sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] ≤
      ∑ ordinal : Fin q, Pr[fun outcome => outcome.SuccessfulHiddenHit ∧ outcome.FirstExistingHiddenHitAt ordinal.val |
        sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] := by
  classical
  let run := sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)
  have hcover : ∀ outcome ∈ support run, outcome.SuccessfulHiddenHit →
      ∃ ordinal : Fin q, outcome.SuccessfulHiddenHit ∧ outcome.FirstExistingHiddenHitAt ordinal.val := by
    intro outcome houtcome hsuccess
    obtain ⟨before, hbefore, hhit⟩ := hsuccess.2
    obtain ⟨selected, hselected, _⟩ := firstExistingHiddenHitOrdinal?_eq_some_of_hasExistingHiddenHit before hhit
    have hfirst : outcome.FirstExistingHiddenHitAt selected.val :=
      ⟨before, hbefore, firstExistingHiddenHitAt_of_firstExistingHiddenHitOrdinal?_eq_some hselected⟩
    have hlt : selected.val < q := by
      by_contra hnot
      have hzero : Pr[fun result => result.SuccessfulHiddenHit ∧ result.FirstExistingHiddenHitAt selected.val | run] = 0 := by
        apply le_antisymm _ zero_le
        exact (probEvent_sampledDiagnostic_successfulHidden_firstHit_le_selectedSnapshot126
          adversary parameter ftsSecret q selected.val hbound hq).trans_eq
          (probEvent_selectedPrivateSnapshotHitAt_eq_zero_of_q_le_ordinal
            adversary parameter ftsSecret q selected.val hbound (by omega))
      exact (probEvent_ne_zero_iff.mpr ⟨outcome, houtcome, hsuccess, hfirst⟩) hzero
    exact ⟨⟨selected.val, hlt⟩, hsuccess, hfirst⟩
  calc
    _ ≤ Pr[fun outcome => ∃ ordinal ∈ (Finset.univ : Finset (Fin q)),
        outcome.SuccessfulHiddenHit ∧ outcome.FirstExistingHiddenHitAt ordinal.val | run] := by
      apply probEvent_mono
      intro outcome houtcome hsuccess
      obtain ⟨ordinal, hordinal⟩ := hcover outcome houtcome hsuccess
      exact ⟨ordinal, Finset.mem_univ _, hordinal⟩
    _ ≤ ∑ ordinal : Fin q, Pr[fun outcome => outcome.SuccessfulHiddenHit ∧
        outcome.FirstExistingHiddenHitAt ordinal.val | run] :=
      probEvent_exists_finset_le_sum Finset.univ run fun (ordinal : Fin q) outcome =>
        outcome.SuccessfulHiddenHit ∧ outcome.FirstExistingHiddenHitAt ordinal.val


theorem probEvent_sampledDiagnostic_successfulHidden_le_sum_selectedSnapshots126
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ table root,
      (simulateQ (SphincsSecurity.expandedAdversaryImpl
        (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ 126) :
    Pr[ObservedMaterializedDiagnostic.SuccessfulHiddenHit |
      sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] ≤
      ∑ ordinal : Fin q, Pr[fun source => SelectedPrivateSnapshotHitAt source ordinal.val |
        sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] := by
  exact (probEvent_sampledDiagnostic_successfulHidden_le_sum_firstHits126 adversary parameter ftsSecret q hbound hq).trans
    (Finset.sum_le_sum fun ordinal _ =>
      probEvent_sampledDiagnostic_successfulHidden_firstHit_le_selectedSnapshot126
        adversary parameter ftsSecret q ordinal.val hbound hq)

end SphincsSecurity.Concrete.OtsProbeSimulation

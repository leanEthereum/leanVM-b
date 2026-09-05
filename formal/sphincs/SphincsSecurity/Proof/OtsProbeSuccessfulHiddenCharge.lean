import SphincsSecurity.Proof.OtsProbeSuccessfulHiddenOrdinals

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local irreducible] sampledObservedMaterializedDiagnostic observedMaterializedRetainedRunFromTable

set_option maxRecDepth 100000

theorem successful_data_of_mem_finishDiagnostic
    (table : OtsSecretIndex → HashOutput) (before : Option (ObservedCleanRunResult α))
    (outcome : ObservedMaterializedDiagnostic α)
    (houtcome : outcome ∈ support (finishObservedMaterializedDiagnostic table before))
    (hsuccess : outcome.final.isSome = true) :
    ∃ result final, before = some result ∧ outcome.before = some result ∧
      some final ∈ support (finishObservedCleanRunFromTable (some result)) := by
  classical
  cases before with
  | none =>
      have heq : outcome = ⟨none, none, false⟩ := by simpa [finishObservedMaterializedDiagnostic] using houtcome
      subst outcome
      simp at hsuccess
  | some before =>
      unfold finishObservedMaterializedDiagnostic at houtcome
      rw [mem_support_bind_iff] at houtcome
      obtain ⟨final, hfinal, hreturn⟩ := houtcome
      simp only [mem_support_pure_iff] at hreturn
      subst outcome
      cases final with
      | none => simp at hsuccess
      | some final => exact ⟨before, final, rfl, rfl, hfinal⟩

theorem probEvent_finishDiagnostic_successfulHidden_firstRoot_le
    (table : OtsSecretIndex → HashOutput)
    (run : ProbComp (Option (ObservedCleanRunResult α))) (ordinal : Nat) :
    Pr[fun outcome => outcome.SuccessfulHiddenHit ∧ outcome.FirstExistingHiddenRootHitAt ordinal |
      run >>= finishObservedMaterializedDiagnostic table] ≤
      Pr[ObservedCleanRunOption.SuccessfulFirstExistingHiddenRootHitAt table ordinal | run] := by
  apply probEvent_bind_le_probEvent
  intro result _hresult hnot
  apply probEvent_eq_zero
  intro outcome houtcome hevent
  obtain ⟨before, final, hresult, hbefore, hfinal⟩ :=
    successful_data_of_mem_finishDiagnostic table result outcome houtcome hevent.1.1
  subst result
  obtain ⟨rootResult, selected, hrootBefore, hselected, hfirst, hroot⟩ := hevent.2
  have heq : rootResult = before := Option.some.inj (hrootBefore.symm.trans hbefore)
  subst rootResult
  exact hnot ⟨⟨final, hfinal⟩, selected, hselected, hfirst, hroot⟩

theorem probEvent_finishDiagnostic_successfulHidden_firstNonRoot_le
    (table : OtsSecretIndex → HashOutput)
    (run : ProbComp (Option (ObservedCleanRunResult α))) (ordinal : Nat) :
    Pr[fun outcome => outcome.SuccessfulHiddenHit ∧ outcome.FirstExistingHiddenNonRootHitAt ordinal |
      run >>= finishObservedMaterializedDiagnostic table] ≤
      Pr[ObservedCleanRunOption.SuccessfulFirstExistingHiddenNonRootHitAt table ordinal | run] := by
  apply probEvent_bind_le_probEvent
  intro result _hresult hnot
  apply probEvent_eq_zero
  intro outcome houtcome hevent
  obtain ⟨before, final, hresult, hbefore, hfinal⟩ :=
    successful_data_of_mem_finishDiagnostic table result outcome houtcome hevent.1.1
  subst result
  obtain ⟨rootResult, selected, hrootBefore, hselected, hfirst, hroot⟩ := hevent.2
  have heq : rootResult = before := Option.some.inj (hrootBefore.symm.trans hbefore)
  subst rootResult
  exact hnot ⟨⟨final, hfinal⟩, selected, hselected, hfirst, hroot⟩

theorem firstExistingHiddenHitAt_root_or_nonRoot
    (outcome : ObservedMaterializedDiagnostic α) (ordinal : Nat)
    (hfirst : outcome.FirstExistingHiddenHitAt ordinal) :
    outcome.FirstExistingHiddenRootHitAt ordinal ∨ outcome.FirstExistingHiddenNonRootHitAt ordinal := by
  obtain ⟨result, hbefore, hfirst⟩ := hfirst
  have hfirstData := hfirst
  obtain ⟨selected, hselected, _, _⟩ := hfirstData
  by_cases hroot : (result.observations.get selected).toProbe.IsLayerRoot
  · exact Or.inl ⟨result, selected, hbefore, hselected, hfirst, hroot⟩
  · exact Or.inr ⟨result, selected, hbefore, hselected, hfirst, hroot⟩

theorem probEvent_sampledDiagnostic_successfulHidden_firstHit_le_selectedCharge126
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q ordinal : Nat) (hordinal : ordinal < q)
    (hbound : ∀ table root,
      (simulateQ (SphincsSecurity.expandedAdversaryImpl
        (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ 126) :
    Pr[fun outcome => outcome.SuccessfulHiddenHit ∧ outcome.FirstExistingHiddenHitAt ordinal |
      sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] ≤
      (∑' table, Pr[= table | sampleOtsHashTable] * hiddenSelectionCharge
        (permissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter ftsSecret (2 * q) table)) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  have hfuel : 2 * q < Fintype.card Digest := by norm_num [digestBits] at hq ⊢; omega
  apply (probEvent_mono (q := fun outcome =>
    (outcome.SuccessfulHiddenHit ∧ outcome.FirstExistingHiddenRootHitAt ordinal) ∨
      (outcome.SuccessfulHiddenHit ∧ outcome.FirstExistingHiddenNonRootHitAt ordinal)) ?_).trans
  · apply (probEvent_or_le _ _ _).trans
    unfold sampledObservedMaterializedDiagnostic
    simp only [probEvent_bind_eq_tsum sampleOtsHashTable, ← ENNReal.tsum_add, ← mul_add]
    rw [← ENNReal.tsum_mul_right]
    apply ENNReal.tsum_le_tsum
    intro table
    rw [mul_assoc]
    apply mul_le_mul' le_rfl
    exact (add_le_add (probEvent_finishDiagnostic_successfulHidden_firstRoot_le table _ ordinal)
      (probEvent_finishDiagnostic_successfulHidden_firstNonRoot_le table _ ordinal)).trans
        (probEvent_diagnosticOrdinal_pair_le_selectedCharge126 ordinal adversary parameter table ftsSecret q
          hordinal hfuel (hbound table) hq)
  · intro outcome _hevent hevent
    rcases firstExistingHiddenHitAt_root_or_nonRoot outcome ordinal hevent.2 with hroot | hnonRoot
    · exact Or.inl ⟨hevent.1, hroot⟩
    · exact Or.inr ⟨hevent.1, hnonRoot⟩

theorem probEvent_sampledDiagnostic_successfulHidden_le_selectionCharge126
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
      sampledHiddenSelectionCharge adversary parameter ftsSecret q * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  apply (probEvent_sampledDiagnostic_successfulHidden_le_sum_firstHits126 adversary parameter ftsSecret q hbound hq).trans
  rw [sampledHiddenSelectionCharge, Finset.sum_mul]
  exact Finset.sum_le_sum fun ordinal _ =>
    probEvent_sampledDiagnostic_successfulHidden_firstHit_le_selectedCharge126 adversary parameter ftsSecret q
      ordinal.val ordinal.isLt hbound hq

theorem probEvent_sampledActualRetained_verifyProbe_le_twoCharges126
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
      (materializedRetainedCharge adversary parameter ftsSecret (2 * q) +
        sampledHiddenSelectionCharge adversary parameter ftsSecret q) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  apply (probEvent_sampledActualRetained_verifyProbe_le_charge_add_successfulHiddenHit126 adversary parameter ftsSecret q hbound hq).trans
  rw [add_mul]
  exact add_le_add le_rfl (probEvent_sampledDiagnostic_successfulHidden_le_selectionCharge126 adversary parameter ftsSecret q hbound hq)

theorem probEvent_sampledActualRetained_verifyProbe_le_twoCharges126_of_hashQueryBound
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 126)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    Pr[fun result => WinningRetainedVerifyProbeWitness parameter (extendStartTable result.1) ftsSecret result.2 |
      sampledActualRetainedOtsHashTable adversary parameter ftsSecret] ≤
      (materializedRetainedCharge adversary parameter ftsSecret (2 * q) +
        sampledHiddenSelectionCharge adversary parameter ftsSecret q) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ :=
  probEvent_sampledActualRetained_verifyProbe_le_twoCharges126 adversary parameter ftsSecret q
    (fun table root => isQueryBoundP_expandedRetained_all_tables_roots adversary q hq parameter hparameter table ftsSecret hfts root) hqMax

end SphincsSecurity.Concrete.OtsProbeSimulation

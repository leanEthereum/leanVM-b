import SphincsSecurity.Proof.OtsProbeNativeCandidateComponents

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

noncomputable def nativeMaterializedCharge
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (input : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) (_fuel : Nat) (_cache : SplitHashCache) : ENNReal :=
  match input with
  | .inl (.inr input) => materializedCandidateAllowance table context
      (purePlanProbingHashQuery parameter input context.state).candidate?
  | _ => 0

theorem nativeMaterializedCharge_le_hashIndicator
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (input : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) :
    nativeMaterializedCharge parameter table input context fuel cache ≤ if IsOuterHash input then 1 else 0 := by
  cases input with
  | inl input =>
      cases input with
      | inl n => simp [nativeMaterializedCharge, IsOuterHash]
      | inr input => exact materializedCandidateAllowance_le_one table context _
  | inr message => simp [nativeMaterializedCharge, IsOuterHash]

theorem nativeMaterializedCharge_eq_zero_of_chainsPublished
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (input : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hpublic : MaterializedChainsPublished context) : nativeMaterializedCharge parameter table input context fuel cache = 0 := by
  cases input with
  | inl input =>
      cases input with
      | inl n => rfl
      | inr input => exact materializedCandidateAllowance_plan_eq_zero_of_chainsPublished parameter input table context hpublic
  | inr message => rfl

theorem nativeMaterializedTraceCharge_le_hashLength
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput) (history : List CanonicalQuerySelection) :
    canonicalTraceCharge (nativeMaterializedCharge parameter table) history ≤ (nativeHashQueryHistory history).length := by
  induction history with
  | nil => simp [canonicalTraceCharge, nativeHashQueryHistory]
  | cons head tail ih =>
      simp only [canonicalTraceCharge, List.map_cons, List.sum_cons, CanonicalQuerySelection.charge] at ih ⊢
      have hstep := add_le_add (nativeMaterializedCharge_le_hashIndicator parameter table head.input head.context head.fuel head.cache) ih
      by_cases hhash : IsOuterHash head.input <;>
        simpa [nativeHashQueryHistory, hhash, add_comm] using hstep

theorem nativeMaterializedTraceCharge_eq_zero_of_chainsPublished
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (history : List CanonicalQuerySelection) (hpublic : ∀ selection ∈ history, MaterializedChainsPublished selection.context) :
    canonicalTraceCharge (nativeMaterializedCharge parameter table) history = 0 := by
  induction history with
  | nil => rfl
  | cons head tail ih =>
      simp only [canonicalTraceCharge, List.map_cons, List.sum_cons, CanonicalQuerySelection.charge]
      rw [nativeMaterializedCharge_eq_zero_of_chainsPublished parameter table head.input head.context head.fuel head.cache
        (hpublic head (by simp)), zero_add]
      simpa only [canonicalTraceCharge, CanonicalQuerySelection.charge] using
        ih (fun selection hselection => hpublic selection (by simp [hselection]))

theorem nativeChainTraceAfterRoot_hash_length_le
    (targets : Finset Position) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel q : Nat)
    (continuation : Digest → OracleComp (OracleWorld + SigningSpec) α)
    (hbound : ∀ root, (continuation root).IsQueryBoundP IsOuterHash q)
    (trace : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection)
    (htrace : trace ∈ support (nativeChainTraceAfterRoot targets parameter table ftsSecret fuel continuation)) :
    (nativeHashQueryHistory trace.2).length ≤ q := by
  rw [nativeChainTraceAfterRoot, mem_support_bind_iff] at htrace
  obtain ⟨root, _, htrace⟩ := htrace
  cases root with
  | none =>
      simp only [mem_support_pure_iff] at htrace
      subst trace
      simp [nativeHashQueryHistory]
  | some root =>
      exact runNativeQueryTrace_hash_length_le parameter root.value.1 ftsSecret (continuation root.value.1)
        root.context root.remaining root.table root.value.2 q (hbound root.value.1) trace htrace

theorem expected_nativeMaterializedTraceCharge_afterRoot_le
    (targets : Finset Position) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel q : Nat)
    (continuation : Digest → OracleComp (OracleWorld + SigningSpec) α)
    (hbound : ∀ root, (continuation root).IsQueryBoundP IsOuterHash q) :
    (∑' trace, Pr[= trace | nativeChainTraceAfterRoot targets parameter table ftsSecret fuel continuation] *
      canonicalTraceCharge (nativeMaterializedCharge parameter table) trace.2) ≤
      (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  calc
    _ ≤ (q : ENNReal) * Pr[fun trace => ¬NativeChainsPublished trace |
        nativeChainTraceAfterRoot targets parameter table ftsSecret fuel continuation] := by
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left]
      apply ENNReal.tsum_le_tsum
      intro trace
      by_cases htrace : trace ∈ support (nativeChainTraceAfterRoot targets parameter table ftsSecret fuel continuation)
      · by_cases hpublic : NativeChainsPublished trace
        · rw [nativeMaterializedTraceCharge_eq_zero_of_chainsPublished parameter table trace.2 hpublic.2]
          simp [hpublic]
        · simp only [hpublic, not_false_eq_true, ite_true]
          rw [mul_comm (q : ENNReal)]
          apply mul_le_mul_right
          exact (nativeMaterializedTraceCharge_le_hashLength parameter table trace.2).trans
            (by exact_mod_cast nativeChainTraceAfterRoot_hash_length_le targets parameter table ftsSecret fuel q continuation hbound trace htrace)
      · simp [probOutput_eq_zero_of_not_mem_support htrace]
    _ ≤ _ := mul_le_mul_right (probEvent_nativeChainTraceAfterRoot_failure_le_inv216 targets parameter table ftsSecret fuel continuation) _

theorem canonicalGuessCharge_eq_native_components_of_safe
    (targets : Finset Position) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (input : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hsafe : 0 < fuel ∧ context.state.pending.card + 1 < Fintype.card Digest)
    (hcoverage : ∀ hashInput, input = .inl (.inr hashInput) → ∀ target digest,
      (purePlanProbingHashQuery parameter hashInput context.state).candidate? = some ⟨.position target, digest⟩ → target ∈ targets) :
    canonicalGuessCharge parameter table input context fuel cache =
      nativeStartCharge parameter table input context fuel cache +
        (∑ target ∈ targets, nativeMissingStructuralCharge target parameter table input context fuel cache) +
        nativeMaterializedCharge parameter table input context fuel cache := by
  simp only [canonicalGuessCharge, if_pos hsafe]
  cases input with
  | inl input =>
      cases input with
      | inl n => simp [nativeStartCharge, nativeMissingStructuralCharge, nativeMaterializedCharge]
      | inr input => exact candidateFailureAllowance_eq_native_components targets table context _ (hcoverage input rfl)
  | inr message => simp [nativeStartCharge, nativeMissingStructuralCharge, nativeMaterializedCharge]

theorem expected_nativeMaterializedCharge_afterRoot_le
    (targets : Finset Position) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel q : Nat)
    (continuation : Digest → OracleComp (OracleWorld + SigningSpec) α)
    (hbound : ∀ root, (continuation root).IsQueryBoundP IsOuterHash q) :
    (∑' root, Pr[= root | runResolvedFromTable (ensuredInitialContext targets) fuel table
      (maskedPublishedTreeRoot.run emptySplitHashCache)] *
      match root with
      | none => 0
      | some root => expectedLiveNativeContextCharge (maskedChronologicalExpandedAdversaryImpl parameter root.value.1 ftsSecret)
          (nativeMaterializedCharge parameter table) (continuation root.value.1)
          root.context root.remaining root.table root.value.2) ≤
      (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  have hbound := expected_nativeMaterializedTraceCharge_afterRoot_le targets parameter table ftsSecret fuel q continuation hbound
  rw [nativeChainTraceAfterRoot, tsum_probOutput_bind_mul] at hbound
  convert hbound using 1
  apply tsum_congr
  intro root
  cases root with
  | none => simp [canonicalTraceCharge]
  | some root => rw [expectedNativeTraceCharge_eq]

end SphincsSecurity.Concrete.OtsProbeSimulation

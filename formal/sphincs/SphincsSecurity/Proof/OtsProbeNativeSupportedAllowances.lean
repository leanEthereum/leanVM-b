import SphincsSecurity.Proof.OtsProbeNativeTraceSafety

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] maskedPublishedTreeRoot instFintypePosition
set_option backward.isDefEq.respectTransparency false

theorem expected_nativeMaterializedRetainedTraceCharge_le
    (targets : Finset Position) (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) (fuel : Nat) :
    (∑' trace, Pr[= trace | nativeChainTraceAfterRoot targets parameter table ftsSecret fuel (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩)] *
      canonicalTraceCharge (nativeMaterializedCharge parameter table) trace.2) ≤
      (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  calc
    _ ≤ (q : ENNReal) * Pr[fun trace => ¬NativeChainsPublished trace |
        nativeChainTraceAfterRoot targets parameter table ftsSecret fuel (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩)] := by
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left]
      apply ENNReal.tsum_le_tsum
      intro trace
      by_cases htrace : trace ∈ support (nativeChainTraceAfterRoot targets parameter table ftsSecret fuel (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩))
      · by_cases hpublic : NativeChainsPublished trace
        · rw [nativeMaterializedTraceCharge_eq_zero_of_chainsPublished parameter table trace.2 hpublic.2]
          simp [hpublic]
        · simp only [hpublic, not_false_eq_true, ite_true]
          rw [mul_comm (q : ENNReal)]
          apply mul_le_mul_right
          exact (nativeMaterializedTraceCharge_le_hashLength parameter table trace.2).trans
            (by exact_mod_cast (by
              rw [← canonicalTraceHashCount_eq_nativeHashLength]
              exact nativeRetainedTraceAfterRoot_hashCount_le targets adversary q hq parameter hparameter table ftsSecret hfts fuel trace htrace :
                (nativeHashQueryHistory trace.2).length ≤ q))
      · simp [probOutput_eq_zero_of_not_mem_support htrace]
    _ ≤ _ := mul_le_mul_right (probEvent_nativeChainTraceAfterRoot_failure_le_inv216 targets parameter table ftsSecret fuel (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩)) _

theorem expected_nativeMaterializedRetainedCharge_le
    (targets : Finset Position) (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) (fuel : Nat) :
    (∑' root, Pr[= root | runResolvedFromTable (ensuredInitialContext targets) fuel table
      (maskedPublishedTreeRoot.run emptySplitHashCache)] *
      match root with
      | none => 0
      | some root => expectedLiveNativeContextCharge (maskedChronologicalExpandedAdversaryImpl parameter root.value.1 ftsSecret)
          (nativeMaterializedCharge parameter table) (retainedGameRestComputation adversary ⟨root.value.1, parameter⟩)
          root.context root.remaining root.table root.value.2) ≤
      (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  have hbound := expected_nativeMaterializedRetainedTraceCharge_le targets adversary q hq parameter hparameter table ftsSecret hfts fuel
  rw [nativeChainTraceAfterRoot, tsum_probOutput_bind_mul] at hbound
  convert hbound using 1
  apply tsum_congr
  intro root
  cases root with
  | none => simp [canonicalTraceCharge]
  | some root => rw [expectedNativeTraceCharge_eq]

theorem canonicalTraceCharge_eq_native_components_of_safe
    (targets : Finset Position) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput) (history : List CanonicalQuerySelection)
    (hsafe : ∀ entry ∈ history, 0 < entry.fuel ∧ entry.context.state.pending.card + 1 < Fintype.card Digest)
    (hcoverage : ∀ entry ∈ history, ∀ input, entry.input = .inl (.inr input) → ∀ target digest,
      (purePlanProbingHashQuery parameter input entry.context.state).candidate? = some ⟨.position target, digest⟩ → target ∈ targets) :
    canonicalTraceCharge (canonicalGuessCharge parameter table) history =
      canonicalTraceCharge (nativeStartCharge parameter table) history +
        (∑ target ∈ targets, canonicalTraceCharge (nativeMissingStructuralCharge target parameter table) history) +
        canonicalTraceCharge (nativeMaterializedCharge parameter table) history := by
  induction history with
  | nil => simp [canonicalTraceCharge]
  | cons head tail ih =>
      have hhead := canonicalGuessCharge_eq_native_components_of_safe targets parameter table head.input head.context head.fuel head.cache
        (hsafe head (by simp)) (hcoverage head (by simp))
      have htail := ih (fun entry hentry => hsafe entry (by simp [hentry]))
        (fun entry hentry => hcoverage entry (by simp [hentry]))
      simp only [canonicalTraceCharge, List.map_cons, List.sum_cons, CanonicalQuerySelection.charge] at htail ⊢
      rw [hhead, htail, Finset.sum_add_distrib]
      ac_rfl

theorem nativeRetainedTraceCharge_eq_components_of_querySpace
    (targets : Finset Position) (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqSpace : q + 1 < Fintype.card Digest)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets)
    (trace : Option (ResolvedRunResult (RetainedRestResult × SplitHashCache)) × List CanonicalQuerySelection)
    (htrace : trace ∈ support (nativeChainTraceAfterRoot targets parameter table ftsSecret (q + 1)
      (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩))) :
    canonicalTraceCharge (canonicalGuessCharge parameter table) trace.2 =
      canonicalTraceCharge (nativeStartCharge parameter table) trace.2 +
        (∑ target : Position, canonicalTraceCharge (nativeMissingStructuralCharge target parameter table) trace.2) +
        canonicalTraceCharge (nativeMaterializedCharge parameter table) trace.2 := by
  exact canonicalTraceCharge_eq_native_components_of_safe Finset.univ parameter table trace.2
    (nativeRetainedTraceAfterRoot_entry_safe_of_querySpace targets adversary q hq hqSpace parameter hparameter table ftsSecret hfts trace htrace)
    (by intro entry hentry input heq target digest hcandidate; exact Finset.mem_univ target)

theorem nativeRetainedTraceCharge_eq_components
    (targets : Finset Position) (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 126)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets)
    (trace : Option (ResolvedRunResult (RetainedRestResult × SplitHashCache)) × List CanonicalQuerySelection)
    (htrace : trace ∈ support (nativeChainTraceAfterRoot targets parameter table ftsSecret (q + 1)
      (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩))) :
    canonicalTraceCharge (canonicalGuessCharge parameter table) trace.2 =
      canonicalTraceCharge (nativeStartCharge parameter table) trace.2 +
        (∑ target : Position, canonicalTraceCharge (nativeMissingStructuralCharge target parameter table) trace.2) +
        canonicalTraceCharge (nativeMaterializedCharge parameter table) trace.2 := by
  exact nativeRetainedTraceCharge_eq_components_of_querySpace targets adversary q hq
    (by
      have hspace : 2 ^ 126 + 1 < Fintype.card Digest := by norm_num [digestBits]
      omega) parameter hparameter table ftsSecret hfts trace htrace

theorem expected_nativeRetainedGuessCharge_le_missing_add_erasure_of_querySpace
    (targets : Finset Position) (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqSpace : q + 1 < Fintype.card Digest)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    (∑' trace, Pr[= trace | nativeChainTraceAfterRoot targets parameter table ftsSecret (q + 1)
      (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩)] *
      canonicalTraceCharge (canonicalGuessCharge parameter table) trace.2) ≤
    (∑' trace, Pr[= trace | nativeChainTraceAfterRoot targets parameter table ftsSecret (q + 1)
      (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩)] *
      (canonicalTraceCharge (nativeStartCharge parameter table) trace.2 +
        ∑ target : Position, canonicalTraceCharge (nativeMissingStructuralCharge target parameter table) trace.2)) +
      (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  let traceRun := nativeChainTraceAfterRoot targets parameter table ftsSecret (q + 1)
    (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩)
  have heq : (∑' trace, Pr[= trace | traceRun] * canonicalTraceCharge (canonicalGuessCharge parameter table) trace.2) =
      ∑' trace, Pr[= trace | traceRun] *
        ((canonicalTraceCharge (nativeStartCharge parameter table) trace.2 +
          ∑ target : Position, canonicalTraceCharge (nativeMissingStructuralCharge target parameter table) trace.2) +
          canonicalTraceCharge (nativeMaterializedCharge parameter table) trace.2) := by
    apply tsum_congr
    intro trace
    by_cases htrace : trace ∈ support traceRun
    · rw [nativeRetainedTraceCharge_eq_components_of_querySpace targets adversary q hq hqSpace parameter hparameter table ftsSecret hfts trace htrace]
    · simp [probOutput_eq_zero_of_not_mem_support htrace]
  change _ ≤ _ + _
  rw [heq]
  simp only [mul_add, ENNReal.tsum_add]
  apply add_le_add le_rfl
  exact expected_nativeMaterializedRetainedTraceCharge_le targets adversary q hq parameter hparameter table ftsSecret hfts (q + 1)

theorem expected_nativeRetainedGuessCharge_le_missing_add_erasure
    (targets : Finset Position) (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 126)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    (∑' trace, Pr[= trace | nativeChainTraceAfterRoot targets parameter table ftsSecret (q + 1)
      (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩)] *
      canonicalTraceCharge (canonicalGuessCharge parameter table) trace.2) ≤
    (∑' trace, Pr[= trace | nativeChainTraceAfterRoot targets parameter table ftsSecret (q + 1)
      (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩)] *
      (canonicalTraceCharge (nativeStartCharge parameter table) trace.2 +
        ∑ target : Position, canonicalTraceCharge (nativeMissingStructuralCharge target parameter table) trace.2)) +
      (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  exact expected_nativeRetainedGuessCharge_le_missing_add_erasure_of_querySpace targets adversary q hq
    (by
      have hspace : 2 ^ 126 + 1 < Fintype.card Digest := by norm_num [digestBits]
      omega) parameter hparameter table ftsSecret hfts

end SphincsSecurity.Concrete.OtsProbeSimulation

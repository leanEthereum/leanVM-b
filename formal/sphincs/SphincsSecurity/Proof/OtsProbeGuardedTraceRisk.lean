import SphincsSecurity.Proof.OtsProbeGuardedStartRisk

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local irreducible] maskedPublishedTreeRoot sampleOtsHashTable
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
theorem valid_no_privateHit_of_mem_canonicalQueryTrace
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (result : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection)
    (hrun : result ∈ support (runCanonicalQueryTrace parameter root ftsSecret computation context fuel table cache)) :
    ∀ entry ∈ result.2, entry.context.Valid ∧ ¬PrivateStructuralHit entry.context := by
  induction computation using OracleComp.inductionOn generalizing context fuel table cache result with
  | pure value =>
      simp only [runCanonicalQueryTrace, OracleComp.construct_pure] at hrun
      split_ifs at hrun <;> simp only [mem_support_pure_iff] at hrun <;> subst result <;> simp
  | query_bind input next ih =>
      rw [runCanonicalQueryTrace_query_bind] at hrun
      split_ifs at hrun with hcomplete
      · have hcurrent : context.Valid ∧ ¬PrivateStructuralHit context := by
          refine ⟨valid_of_resolvedCore_completable table context hconsistent hstarts hcomplete, ?_⟩
          obtain ⟨completion, hcompletion⟩ := hcomplete
          exact hcompletion.not_privateStructuralHit
        rw [mem_support_bind_iff] at hrun
        obtain ⟨stepOption, hstep, hrun⟩ := hrun
        cases stepOption with
        | none =>
            simp only [pure_bind, mem_support_pure_iff] at hrun
            subst result
            intro entry hentry
            simp only [List.mem_singleton] at hentry
            subst entry
            exact hcurrent
        | some step =>
            rw [mem_support_bind_iff] at hrun
            obtain ⟨tail, htail, hpure⟩ := hrun
            simp only [mem_support_pure_iff] at hpure
            subst result
            have hcore := resolvedCore_of_mem_canonicalChronologicalAdversaryImpl parameter root table ftsSecret
              input context fuel cache step hconsistent hstarts hstep
            intro entry hentry
            rcases List.mem_cons.mp hentry with heq | htailEntry
            · subst entry
              exact hcurrent
            · rw [hcore.1] at htail
              exact ih step.value.1 step.context step.remaining table step.value.2 hcore.2.1 hcore.2.2
                tail htail entry htailEntry
      · simp only [mem_support_pure_iff] at hrun
        subst result
        simp

theorem valid_no_privateHit_of_mem_canonicalRetainedQueryTrace
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (result : Option (ResolvedRunResult (RetainedGameResult × SplitHashCache)) × List CanonicalQuerySelection)
    (hrun : result ∈ support (canonicalRetainedQueryTrace adversary parameter table ftsSecret fuel)) :
    ∀ entry ∈ result.2, entry.context.Valid ∧ ¬PrivateStructuralHit entry.context := by
  rw [canonicalRetainedQueryTrace, mem_support_bind_iff] at hrun
  obtain ⟨rootOption, hroot, hrun⟩ := hrun
  cases rootOption with
  | none =>
      simp only [mem_support_pure_iff] at hrun
      subst result
      simp
  | some root =>
      rw [mem_support_bind_iff] at hrun
      obtain ⟨rest, hrest, hpure⟩ := hrun
      simp only [mem_support_pure_iff] at hpure
      subst result
      have hcore := resolvedCore_of_mem_runResolvedFromTable
        (maskedPublishedTreeRoot.run emptySplitHashCache)
        { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
        fuel table root (by intro coordinate output hvalue; simp [LazyRevealProbe.State.empty] at hvalue)
        (by intro index output hvalue; simp [LazyRevealProbe.State.empty] at hvalue) hroot
      rw [hcore.1] at hrest
      exact valid_no_privateHit_of_mem_canonicalQueryTrace parameter root.value.1 ftsSecret
        (retainedGameRestComputation adversary ⟨root.value.1, parameter⟩)
        root.context root.remaining table root.value.2 hcore.2.1 hcore.2.2 rest hrest

theorem expected_guarded_chainStart_allowance_le_of_coupled_retainedTrace
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 126)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) (fuel : Nat)
    (left : Option (ResolvedRunResult (RetainedGameResult × SplitHashCache)) × List CanonicalQuerySelection)
    (right : (RetainedGameResult × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot)
    (hleft : left ∈ support (canonicalRetainedQueryTrace adversary parameter table ftsSecret fuel))
    (hright : right ∈ support (prehitRetainedQueryTrace adversary parameter table ftsSecret))
    (hrelation : CanonicalQueryTraceRel parameter table left right)
    (ordinal : Nat) (entry : CanonicalQuerySelection) (hentry : left.2[ordinal]? = some entry)
    (index : OtsSecretIndex) (digest : Digest) (hmissing : entry.context.state.values index.coordinate = none) :
    (∑' base, Pr[= base | sampleOtsHashTable] *
      if DeferredCompletable (completedStartTable entry.context.state base) entry.context then
        candidateFailureAllowance (completedStartTable entry.context.state base) entry.context
          (some ⟨index.coordinate, digest⟩)
      else 0) ≤
      ((unmaterializedCandidateCharge (materializedDeferredState entry.context)
        (some ⟨index.coordinate, digest⟩) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) * (4 / 3) *
      Pr[fun base => DeferredCompletable (completedStartTable entry.context.state base) entry.context |
        sampleOtsHashTable] := by
  have hclean := valid_no_privateHit_of_mem_canonicalRetainedQueryTrace adversary parameter table ftsSecret fuel
    left hleft entry (List.mem_iff_getElem?.mpr ⟨ordinal, hentry⟩)
  have hcard := pending_card_le_of_coupled_canonicalRetainedTrace adversary q hq parameter hparameter table ftsSecret
    hfts fuel left right hleft hright hrelation ordinal entry hentry
  exact expected_guarded_chainStart_allowance_le_four_thirds entry.context index digest hmissing
    hclean.1 hclean.2 (hcard.trans hqMax)

end SphincsSecurity.Concrete.OtsProbeSimulation

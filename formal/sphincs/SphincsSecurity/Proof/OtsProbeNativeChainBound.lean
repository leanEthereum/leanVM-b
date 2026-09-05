import SphincsSecurity.Proof.OtsProbeNativeChainTrace
import SphincsSecurity.Proof.OtsProbeStartErasureBound

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

noncomputable def nativeChainTraceAfterRoot
    (targets : Finset Position) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (continuation : Digest → OracleComp (OracleWorld + SigningSpec) α) :
    ProbComp (Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection) := do
  let root ← runResolvedFromTable (ensuredInitialContext targets) fuel table
    (maskedPublishedTreeRoot.run emptySplitHashCache)
  match root with
  | none => pure (none, [])
  | some root =>
      runNativeQueryTrace parameter root.value.1 ftsSecret (continuation root.value.1)
        root.context root.remaining root.table root.value.2

theorem relTriple_nativeChainTraceAfterRoot
    (targets : Finset Position) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (continuation : Digest → OracleComp (OracleWorld + SigningSpec) α) :
    RelTriple (nativeChainTraceAfterRoot targets parameter table ftsSecret fuel continuation)
      ((simulateQ romImpl (concreteAfterRootComputation parameter table ftsSecret continuation)).run ∅)
      NativeChainTraceRel := by
  have hroot := reachableResolvedCouples_maskedPublishedTreeRoot parameter table (ensuredInitialContext targets)
    fuel emptySplitHashCache ∅ (ensuredInitialContext_resolvedInvariant targets parameter table)
    (ensuredInitialContext_visible targets parameter table) (ensuredInitialContext_published targets)
  have hsupported := FtsProbeSimulation.relTriple_and_left_support hroot
    (fun left => ∀ result, left = some result → MaterializedChainsPublished result.context) (by
      intro left hleft result heq
      subst left
      exact materializedChainsPublished_of_mem_initializedRoot targets fuel table result hleft)
  rw [nativeChainTraceAfterRoot, concreteAfterRootComputation, simulateQ_bind, StateT.run_bind,
    simulateQ_romImpl_liftM]
  apply relTriple_bind hsupported
  intro left right hrel
  rw [← simulateQ_unloggedMapped_eq_expanded]
  cases left with
  | none =>
      apply relTriple_nativeChainTrace_of_public
      intro trace htrace
      simp only [mem_support_pure_iff] at htrace
      subst trace
      exact ⟨by simp, by simp⟩
  | some result =>
      dsimp only
      have hchain := hrel.2 result rfl
      rcases hrel.1 with hclean | hdoomed
      · rcases right with ⟨root, actualCache⟩
        have hvalue : result.value.1 = root := hclean.2.1
        subst root
        rw [hclean.1]
        exact relTriple_nativeTrace_chainPublication parameter result.value.1 table ftsSecret (continuation result.value.1)
          result.context result.remaining result.value.2 actualCache hclean.2.2.1 hclean.2.2.2.1 hclean.2.2.2.2 hchain
      · rw [runNativeQueryTrace_of_not_completable parameter result.value.1 ftsSecret (continuation result.value.1)
          result.context result.remaining result.table result.value.2 (by rw [hdoomed.1]; exact hdoomed.2.2.2)]
        apply relTriple_nativeChainTrace_of_public
        intro trace htrace
        simp only [mem_support_pure_iff] at htrace
        subst trace
        exact ⟨by simp, by simp⟩

theorem probEvent_nativeChainTraceAfterRoot_failure_le_inv216
    (targets : Finset Position) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (continuation : Digest → OracleComp (OracleWorld + SigningSpec) α) :
    Pr[fun trace => ¬NativeChainsPublished trace | nativeChainTraceAfterRoot targets parameter table ftsSecret fuel continuation] ≤
      ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  apply (probEvent_le_of_relTriple (relTriple_nativeChainTraceAfterRoot targets parameter table ftsSecret fuel continuation)
    (p := fun trace => ¬NativeChainsPublished trace) (q := fun result => AnyEncodingInputsExhausted result.2) ?_).trans
      (probEvent_anyEncodingInputsExhausted_le_inv216 (concreteAfterRootComputation parameter table ftsSecret continuation))
  intro trace result hrel hfailure
  exact hrel.resolve_left hfailure

def NativeMaterializedCandidateRisk (parameter : PublicParameter)
    (trace : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection) : Prop :=
  ∃ selection ∈ trace.2, ∃ input candidate,
    selection.input = .inl (.inr input) ∧
    (purePlanProbingHashQuery parameter input selection.context.state).candidate? = some candidate ∧
    selection.context.state.values candidate.coordinate ≠ none ∧
    candidateFailureAllowance selection.table selection.context (some candidate) ≠ 0

theorem NativeMaterializedCandidateRisk.not_chainsPublished
    {parameter : PublicParameter}
    {trace : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection}
    (hrisk : NativeMaterializedCandidateRisk parameter trace) : ¬NativeChainsPublished trace := by
  obtain ⟨selection, hselection, input, candidate, _, hplan, hknown, hnonzero⟩ := hrisk
  intro hpublic
  exact hnonzero ((hpublic.2 selection hselection).candidate_allowance_eq_zero_of_known
    parameter input candidate selection.table hplan hknown)

theorem probEvent_nativeMaterializedCandidateRisk_afterRoot_le_inv216
    (targets : Finset Position) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (continuation : Digest → OracleComp (OracleWorld + SigningSpec) α) :
    Pr[NativeMaterializedCandidateRisk parameter | nativeChainTraceAfterRoot targets parameter table ftsSecret fuel continuation] ≤
      ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  apply (probEvent_mono fun _ _ hrisk => hrisk.not_chainsPublished).trans
    (probEvent_nativeChainTraceAfterRoot_failure_le_inv216 targets parameter table ftsSecret fuel continuation)

noncomputable def sampledNativeChainTrace (targets : Finset Position) (adversary : Adversary) (fuel : Nat) :
    ProbComp (Option (ResolvedRunResult (RetainedGameResult × SplitHashCache)) × List CanonicalQuerySelection) := do
  let parameter ← sampleParameter
  let table ← sampleOtsHashTable
  let ftsSecret ← sampleFtsSecrets
  nativeChainTraceAfterRoot targets parameter table ftsSecret fuel fun root =>
    (fun rest => (root, rest)) <$> retainedGameRestComputation adversary ⟨root, parameter⟩

theorem probEvent_sampledNativeChainTrace_failure_le_inv216
    (targets : Finset Position) (adversary : Adversary) (fuel : Nat) :
    Pr[fun trace => ¬NativeChainsPublished trace | sampledNativeChainTrace targets adversary fuel] ≤
      ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  unfold sampledNativeChainTrace
  apply probEvent_bind_le_of_forall_le
  intro parameter _
  apply probEvent_bind_le_of_forall_le
  intro table _
  apply probEvent_bind_le_of_forall_le
  intro ftsSecret _
  exact probEvent_nativeChainTraceAfterRoot_failure_le_inv216 targets parameter table ftsSecret fuel _

end SphincsSecurity.Concrete.OtsProbeSimulation

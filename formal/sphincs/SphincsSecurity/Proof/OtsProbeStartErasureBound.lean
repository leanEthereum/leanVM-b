import SphincsSecurity.Proof.OtsProbeStartErasureTrace

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000

noncomputable def canonicalStartErasureAfterRoot
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (continuation : Digest → OracleComp (OracleWorld + SigningSpec) α) :
    ProbComp (Option (ResolvedRunResult (α × SplitHashCache)) × Bool) := do
  let root ← runResolvedFromTable
    { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
    fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)
  match root with
  | none => pure (none, false)
  | some root =>
      runCanonicalStartErasureTrace parameter root.value.1 table ftsSecret (continuation root.value.1)
        root.context root.remaining root.value.2 false

noncomputable def concreteAfterRootComputation
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (continuation : Digest → OracleComp (OracleWorld + SigningSpec) α) : OracleComp OracleWorld α := do
  let root ← liftM (treeRoot parameter topLayer rootTree
    (fun leafIdx chainIdx => truncateHash (table ⟨topLayer, rootTree, leafIdx, chainIdx⟩)) : OracleComp HashSpec Digest)
  simulateQ (expandedAdversaryImpl
    ⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩)
    (continuation root)

theorem simulateQ_unloggedMapped_eq_expanded (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    simulateQ (unloggedMappedAdversaryImpl secretKey) computation =
      simulateQ romImpl (simulateQ (expandedAdversaryImpl secretKey) computation) := by
  have hhandler : unloggedMappedAdversaryImpl secretKey = romImpl ∘ₛ expandedAdversaryImpl secretKey := by
    funext input
    exact unloggedMappedAdversaryImpl_eq_simulateQ_expanded secretKey input
  rw [hhandler, QueryImpl.simulateQ_compose]

theorem relTriple_canonicalStartErasureAfterRoot
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (continuation : Digest → OracleComp (OracleWorld + SigningSpec) α) :
    RelTriple (canonicalStartErasureAfterRoot parameter table ftsSecret fuel continuation)
      ((simulateQ romImpl (concreteAfterRootComputation parameter table ftsSecret continuation)).run ∅)
      (StartErasureTraceRel parameter table) := by
  have hroot := reachableResolvedCouples_maskedPublishedTreeRoot parameter table
    { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
    fuel emptySplitHashCache ∅ (resolvedContextInvariant_empty parameter table)
    (visibleResolvedComputationsCached_empty parameter table emptyDeferredStructuralValues ∅) publishedValues_empty
  have hsupported := FtsProbeSimulation.relTriple_and_left_support hroot
    (fun left => ∀ result, left = some result → CanonicalMaterializedValues table result.context) (by
      intro left hleft result heq
      subst left
      exact canonicalMaterializedValues_of_mem_maskedPublishedTreeRoot parameter table fuel result hleft)
  rw [canonicalStartErasureAfterRoot, concreteAfterRootComputation, simulateQ_bind, StateT.run_bind,
    simulateQ_romImpl_liftM]
  apply relTriple_bind hsupported
  intro left right hrel
  rw [← simulateQ_unloggedMapped_eq_expanded]
  cases left with
  | none =>
      exact relTriple_stoppedStartErasureTrace parameter right.1 table ftsSecret (continuation right.1) right.2 false (by simp)
  | some result =>
      have hcanonical := hrel.2 result rfl
      rcases hrel.1 with hclean | hdoomed
      · rcases right with ⟨root, actualCache⟩
        have hvalue : result.value.1 = root := hclean.2.1
        subst root
        exact relTriple_runCanonicalStartErasureTrace parameter result.value.1 table ftsSecret (continuation result.value.1)
          result.context result.remaining result.value.2 actualCache false hclean.2.2.1 hclean.2.2.2.1 hclean.2.2.2.2
          hcanonical (by simp)
      · dsimp only
        rw [runCanonicalStartErasureTrace_of_not_completable parameter result.value.1 table ftsSecret
          (continuation result.value.1) result.context result.remaining result.value.2 false hdoomed.2.2.2]
        exact relTriple_stoppedStartErasureTrace parameter right.1 table ftsSecret (continuation right.1) right.2 false (by simp)

theorem probEvent_canonicalStartErasureAfterRoot_le_inv216
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (continuation : Digest → OracleComp (OracleWorld + SigningSpec) α) :
    Pr[fun result => result.2 = true | canonicalStartErasureAfterRoot parameter table ftsSecret fuel continuation] ≤
      ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  apply (probEvent_le_of_relTriple (relTriple_canonicalStartErasureAfterRoot parameter table ftsSecret fuel continuation)
    (p := fun result => result.2 = true) (q := fun result => AnyEncodingInputsExhausted result.2) ?_).trans
      (probEvent_anyEncodingInputsExhausted_le_inv216 (concreteAfterRootComputation parameter table ftsSecret continuation))
  intro left right hrel hflag
  exact hrel.2.2 hflag

noncomputable def sampledCanonicalStartErasureTrace (adversary : Adversary) (fuel : Nat) :
    ProbComp (Option (ResolvedRunResult (RetainedGameResult × SplitHashCache)) × Bool) := do
  let parameter ← sampleParameter
  let table ← sampleOtsHashTable
  let ftsSecret ← sampleFtsSecrets
  canonicalStartErasureAfterRoot parameter table ftsSecret fuel fun root =>
    (fun rest => (root, rest)) <$> retainedGameRestComputation adversary ⟨root, parameter⟩

theorem probEvent_sampledCanonicalStartErasureTrace_le_inv216 (adversary : Adversary) (fuel : Nat) :
    Pr[fun result => result.2 = true | sampledCanonicalStartErasureTrace adversary fuel] ≤
      ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  unfold sampledCanonicalStartErasureTrace
  apply probEvent_bind_le_of_forall_le
  intro parameter _
  apply probEvent_bind_le_of_forall_le
  intro table _
  apply probEvent_bind_le_of_forall_le
  intro ftsSecret _
  exact probEvent_canonicalStartErasureAfterRoot_le_inv216 parameter table ftsSecret fuel _

end SphincsSecurity.Concrete.OtsProbeSimulation

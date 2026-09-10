import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeEnsuredInitialization
import SphincsSecurity.Proof.OtsProbeNativeQueryTrace
import SphincsSecurity.Proof.OtsProbeRootMaterializationHash
import SphincsSecurity.Proof.OtsProbeRootMaterializationSigner

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem rootMaterializationPreserving_chronologicalQuery
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : (OracleWorld + SigningSpec).Domain) :
    RootMaterializationPreserving (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input) := by
  cases input with
  | inl query =>
      cases query with
      | inl n => exact rootMaterializationPreserving_splitUniformImpl n
      | inr input => exact rootMaterializationPreserving_probingHashQuery parameter input
  | inr message => exact rootMaterializationPreserving_chronologicalSign parameter root ftsSecret message

theorem rootMaterializationPreserving_maskedPublishedTreeRoot :
    RootMaterializationPreserving maskedPublishedTreeRoot := by
  rw [maskedPublishedTreeRoot_eq]
  apply (rootMaterializationPreserving_maskedTreeRoot topLayer rootTree).bind
  intro value
  exact (rootMaterializationPreserving_publishCoordinate _).bind (fun _ => .pure value)

theorem layerRootsMaterialized_ensuredInitialContext (targets : Finset Position) :
    LayerRootsMaterialized (ensuredInitialContext targets) := by
  intro target _ hknown
  exact False.elim (hknown rfl)

attribute [local irreducible] maskedChronologicalRetainedGameAfterFtsSecrets maskedPublishedTreeRoot

theorem layerRootsMaterialized_runNativeQueryTrace
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (trace : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection)
    (hmat : LayerRootsMaterialized context) (hclosed : DeferredComputationsClosed context)
    (htrace : trace ∈ support (runNativeQueryTrace parameter root ftsSecret computation context fuel table cache)) :
    (∀ result, trace.1 = some result → LayerRootsMaterialized result.context) ∧
      ∀ selection ∈ trace.2, LayerRootsMaterialized selection.context := by
  induction computation using OracleComp.inductionOn generalizing context fuel table cache trace with
  | pure value =>
      simp only [runNativeQueryTrace, OracleComp.construct_pure] at htrace
      split_ifs at htrace <;> simp only [mem_support_pure_iff] at htrace <;> subst trace
      · exact ⟨fun result heq => Option.some.inj heq ▸ hmat, fun _ hmem => False.elim (List.not_mem_nil hmem)⟩
      · simp
  | query_bind input next ih =>
      rw [runNativeQueryTrace_query_bind] at htrace
      by_cases hcomplete : DeferredCompletable table context
      · rw [if_pos hcomplete, mem_support_bind_iff] at htrace
        obtain ⟨middle, hmiddle, htail⟩ := htrace
        cases middle with
        | none =>
            simp only [pure_bind, mem_support_pure_iff] at htail
            subst trace
            exact ⟨by simp, by simpa using hmat⟩
        | some middle =>
            simp only [mem_support_bind_iff] at htail
            obtain ⟨tail, htail, hreturn⟩ := htail
            simp only [mem_support_pure_iff] at hreturn
            subst trace
            have hmiddleMat := rootMaterializationPreserving_chronologicalQuery parameter root ftsSecret input
              context fuel table cache middle hmat hclosed hmiddle
            have hmiddleClosed := hclosed.of_mem_runResolved _ context fuel table middle hmiddle
            have htailMat := ih middle.value.1 middle.context middle.remaining middle.table middle.value.2 tail
              hmiddleMat hmiddleClosed htail
            refine ⟨htailMat.1, ?_⟩
            intro selection hmem
            rcases List.mem_cons.mp hmem with rfl | hmem
            · exact hmat
            · exact htailMat.2 selection hmem
      · rw [if_neg hcomplete] at htrace
        simp only [mem_support_pure_iff] at htrace
        subst trace
        simp

end SphincsSecurity.Concrete.OtsProbeSimulation

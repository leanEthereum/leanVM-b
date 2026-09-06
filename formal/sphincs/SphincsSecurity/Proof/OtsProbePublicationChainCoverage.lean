import SphincsSecurity.Proof.OtsProbeLayerChainCoverage
import SphincsSecurity.Proof.OtsProbePublicationBody

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem materializedChainsPublished_of_successful_publishSignatureBody
    (randomness : Randomness) (index : Index) (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (layers : Layer → Option ChronologicalLayerPart)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (Option PublishedSignatureBody × SplitHashCache))
    (hpublic : ChainsPublishedOutside (fun coordinate => ∀ lay, ChainOutsideLayerPart coordinate index lay (layers lay)) context)
    (hresult : some result ∈ support (runResolvedFromTable context fuel table
      ((publishSignatureBody randomness index ftsPath layers).run cache)))
    (hsuccess : result.value.1 ≠ none) : MaterializedChainsPublished result.context := by
  cases hparts : traverseOption layers with
  | none =>
      simp [publishSignatureBody, hparts, runResolvedFromTable] at hresult
      subst result
      exact False.elim (hsuccess rfl)
  | some parts =>
      rw [publishSignatureBody, hparts, StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
      obtain ⟨publishedOption, hpublished, hreturn⟩ := hresult
      cases publishedOption with
      | none => simp at hreturn
      | some published =>
          simp [runResolvedFromTable] at hreturn
          subst result
          intro coordinate hchain hknown
          by_cases hselected : ∃ lay chainIdx, coordinate =
              chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx ((parts lay).encoding chainIdx)
          · obtain ⟨lay, chainIdx, heq⟩ := hselected
            rw [heq]
            exact resolvedPublishes_sequenceFin _ _ lay
              (resolvedPublishes_revealLayerValues index lay (parts lay).encoding chainIdx)
              context fuel table cache published hpublished
          · have hother : ∀ lay chainIdx, coordinate ≠
                chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx ((parts lay).encoding chainIdx) := by
              intro lay chainIdx heq
              exact hselected ⟨lay, chainIdx, heq⟩
            have hafter := resolvedPreservesCoordinate_sequenceFin coordinate _
              (fun lay => resolvedPreservesChain_revealLayerValues coordinate hchain index lay (parts lay).encoding (hother lay))
              context fuel table cache published hpublished
            apply hafter.2.mpr
            apply hpublic coordinate hchain
            · intro lay
              rw [traverseOption_eq_some_apply layers parts hparts lay]
              exact hother lay
            · rwa [hafter.1] at hknown

end SphincsSecurity.Concrete.OtsProbeSimulation

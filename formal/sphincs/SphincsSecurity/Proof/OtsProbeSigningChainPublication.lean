import SphincsSecurity.Proof.OtsProbeSigningChainValues

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec

attribute [local irreducible] maskedSignLayer
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

theorem materializedChainsPublished_of_signLayers_and_publish
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (layerResult : ResolvedRunResult ((Layer → Option ChronologicalLayerPart) × SplitHashCache))
    (result : ResolvedRunResult (Option Signature × SplitHashCache))
    (hpublic : MaterializedChainsPublished context)
    (hlayers : some layerResult ∈ support (runResolvedFromTable context fuel table
      ((maskedChronologicalSignLayers parameter ftsSecret index).run cache)))
    (hresult : some result ∈ support (runResolvedFromTable layerResult.context layerResult.remaining layerResult.table
      ((publishChronologicalSignature ftsSecret randomness index leaves ftsPath layerResult.value.1).run layerResult.value.2)))
    (hsuccess : result.value.1 ≠ none) : MaterializedChainsPublished result.context := by
  classical
  cases hparts : traverseOption layerResult.value.1 with
  | none =>
      simp [publishChronologicalSignature, hparts, runResolvedFromTable] at hresult
      subst result
      exact False.elim (hsuccess rfl)
  | some parts =>
      rw [publishChronologicalSignature, hparts, StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
      obtain ⟨publishedOption, hpublished, hreturn⟩ := hresult
      cases publishedOption with
      | none => simp at hreturn
      | some published =>
          simp [runResolvedFromTable] at hreturn
          subst result
          intro coordinate hchain hvalue
          by_cases hselected : ∃ lay chainIdx, coordinate =
              chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx ((parts lay).encoding chainIdx)
          · obtain ⟨lay, chainIdx, heq⟩ := hselected
            rw [heq]
            exact resolvedPublishes_sequenceFin _ _ lay
              (resolvedPublishes_revealLayerValues index lay (parts lay).encoding chainIdx)
              layerResult.context layerResult.remaining layerResult.table layerResult.value.2 published hpublished
          · have hother : ∀ lay chainIdx, coordinate ≠
                chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx ((parts lay).encoding chainIdx) := by
              intro lay chainIdx heq
              exact hselected ⟨lay, chainIdx, heq⟩
            have hafter := resolvedPreservesCoordinate_sequenceFin coordinate _
              (fun lay => resolvedPreservesChain_revealLayerValues coordinate hchain index lay (parts lay).encoding (hother lay))
              layerResult.context layerResult.remaining layerResult.table layerResult.value.2 published hpublished
            have hbefore := resolvedPreservesChain_maskedChronologicalSignLayers coordinate hchain parameter ftsSecret index
              context fuel table cache layerResult hlayers (by
                intro lay
                rw [traverseOption_eq_some_apply layerResult.value.1 parts hparts lay]
                exact hother lay)
            have hinitial : context.state.values coordinate ≠ none := by
              rwa [hafter.1, hbefore] at hvalue
            exact hafter.2.mpr ((revealed_subset_of_mem_runResolvedFromTable _ context fuel table layerResult hlayers)
              (hpublic coordinate hchain hinitial))

theorem materializedChainsPublished_of_mem_successful_signAfterDigest
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (Option Signature × SplitHashCache))
    (hpublic : MaterializedChainsPublished context)
    (hresult : some result ∈ support (runResolvedFromTable context fuel table
      ((maskedPublishedChronologicalSignAfterDigest parameter ftsSecret randomness index leaves).run cache)))
    (hsuccess : result.value.1 ≠ none) : MaterializedChainsPublished result.context := by
  rw [maskedPublishedChronologicalSignAfterDigest_eq, StateT.run_bind, runResolvedFromTable_bind,
    mem_support_bind_iff] at hresult
  obtain ⟨pathOption, hpath, hrest⟩ := hresult
  cases pathOption with
  | none => simp at hrest
  | some path =>
      have hpathPublic : MaterializedChainsPublished path.context := by
        intro coordinate hchain hvalue
        have hpreserved := resolvedPreservesCoordinate_simulateQ_ordinaryHashImpl coordinate _
          context fuel table cache path hpath
        exact hpreserved.2.mpr (hpublic coordinate hchain (by rwa [hpreserved.1] at hvalue))
      dsimp only at hrest
      rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hrest
      obtain ⟨layerOption, hlayers, hpublish⟩ := hrest
      cases layerOption with
      | none => simp at hpublish
      | some layers =>
          exact materializedChainsPublished_of_signLayers_and_publish parameter ftsSecret randomness index leaves
            path.value.1 path.context path.remaining path.table path.value.2 layers result hpathPublic hlayers hpublish hsuccess

theorem materializedChainsPublished_of_mem_successful_sign
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (Option Signature × SplitHashCache))
    (hpublic : MaterializedChainsPublished context)
    (hresult : some result ∈ support (runResolvedFromTable context fuel table
      ((maskedPublishedChronologicalSign parameter root ftsSecret message).run cache)))
    (hsuccess : result.value.1 ≠ none) : MaterializedChainsPublished result.context := by
  rw [maskedPublishedChronologicalSign, StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨digestOption, hdigest, hrest⟩ := hresult
  cases digestOption with
  | none => simp at hrest
  | some digest =>
      cases hselected : digest.value.1 with
      | none =>
          simp [hselected, runResolvedFromTable] at hrest
          subst result
          exact False.elim (hsuccess rfl)
      | some selected =>
          rcases selected with ⟨randomness, index, leaves⟩
          have hdigestPublic : MaterializedChainsPublished digest.context := by
            intro coordinate hchain hvalue
            have hpreserved := resolvedPreservesCoordinate_simulateQ_ordinaryRomImpl coordinate _
              context fuel table cache digest hdigest
            exact hpreserved.2.mpr (hpublic coordinate hchain (by rwa [hpreserved.1] at hvalue))
          apply materializedChainsPublished_of_mem_successful_signAfterDigest parameter ftsSecret randomness index leaves
            digest.context digest.remaining digest.table digest.value.2 result hdigestPublic _ hsuccess
          simpa only [hselected] using hrest

end SphincsSecurity.Concrete.OtsProbeSimulation

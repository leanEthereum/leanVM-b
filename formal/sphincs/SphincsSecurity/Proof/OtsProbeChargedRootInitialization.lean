import SphincsSecurity.Proof.OtsProbeChargedRootOccurrence
import SphincsSecurity.Proof.OtsProbeSigningStartValues

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem ResolvedOrdinaryCachePreserving.of_administrative
    {computation : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α} {value : α}
    (h : ResolvedAdministrative computation value) : ResolvedOrdinaryCachePreserving computation := by
  intro context fuel table cache result hresult
  obtain ⟨finalContext, hrun, _⟩ := h context cache fuel table
  rw [hrun] at hresult
  simp only [mem_support_pure_iff, Option.some.injEq] at hresult
  subst result
  rfl

theorem resolvedOrdinaryCachePreserving_maskedPublishedTreeRoot :
    ResolvedOrdinaryCachePreserving maskedPublishedTreeRoot := by
  unfold maskedPublishedTreeRoot
  exact (ResolvedOrdinaryCachePreserving.of_administrative
    (resolvedAdministrative_ensureTreeNode topLayer rootTree (layerHeight topLayer) 0)).bind fun _ =>
      resolvedOrdinaryCachePreserving_revealPublishedCoordinate _

theorem resolvedPreservesCoordinate_maskedTreeRoot_of_ne
    (position : Position) (lay : Layer) (tree : TreeIndex) (hne : position ≠ layerRootPosition lay tree) :
    ResolvedPreservesCoordinate (.position position) (maskedTreeRoot lay tree) := by
  have hpos : 0 < layerHeight lay := by
    unfold layerHeight
    split <;> norm_num [maxLayerHeight]
  have hlevel : layerHeight lay - 1 < maxLayerHeight := by
    have hle := layerHeight_le lay
    omega
  have hcoordinate : Coordinate.position position ≠
      .position (.node lay tree ⟨layerHeight lay - 1, hlevel⟩ (leafOfNat 0)) := by
    intro heq
    apply hne
    apply Coordinate.position.inj at heq
    simpa [layerRootPosition, leafOfNat] using heq
  unfold maskedTreeRoot
  rw [show layerHeight lay = (layerHeight lay - 1) + 1 by omega, maskedTreeNode]
  exact (resolvedPreservesCoordinate_ensureTreeNode (.position position) lay tree
    (layerHeight lay - 1 + 1) 0).bind fun _ => by
      rw [dif_pos hlevel]
      exact resolvedPreservesCoordinate_revealCoordinate_of_ne _ _ hcoordinate

theorem resolvedPreservesCoordinate_maskedPublishedTreeRoot_of_ne
    (position : Position) (hne : position ≠ layerRootPosition topLayer rootTree) :
    ResolvedPreservesCoordinate (.position position) maskedPublishedTreeRoot := by
  rw [maskedPublishedTreeRoot_eq]
  exact (resolvedPreservesCoordinate_maskedTreeRoot_of_ne position topLayer rootTree hne).bind fun _ =>
    (resolvedPreservesCoordinate_publish_of_ne (.position position) (.position (layerRootPosition topLayer rootTree))
      (fun heq => hne (Coordinate.position.inj heq))).bind fun _ => resolvedPreservesCoordinate_pure _ _

attribute [local irreducible] maskedPublishedTreeRoot

theorem initializedNativeRoot_fresh_facts
    (parameter : PublicParameter) (targets : Finset Position) (target : Position) (hmem : target ∈ targets)
    (hroot : IsLayerRoot target) (hne : target ≠ layerRootPosition topLayer rootTree)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult (Digest × SplitHashCache))
    (hresult : some result ∈ support (runResolvedFromTable (ensuredInitialContext targets) fuel table
      (maskedPublishedTreeRoot.run emptySplitHashCache))) :
    result.context.Valid ∧ DeferredCompletable table result.context ∧
      .position target ∈ result.context.state.ensured ∧
      result.context.state.values (.position target) = none ∧ result.context.values target = none ∧
      result.context.state.pendingAt (.position target) = ∅ ∧
      ∀ digest, NoEncodingRootGuessCached parameter target digest result.value.2 := by
  have hcore := resolvedCore_of_mem_runResolvedFromTable (maskedPublishedTreeRoot.run emptySplitHashCache)
    (ensuredInitialContext targets) fuel table result (ensuredInitialContext_valid targets).valuesConsistent
    (startTableAgrees_of_deferredCompletable (ensuredInitialContext_completable targets table)) hresult
  have hcovered := valid_pendingCovered_of_mem_runResolvedFromTable_of_probeFree _ _ fuel table result []
    (maskedPublishedTreeRoot_probeFree emptySplitHashCache) (ensuredInitialContext_valid targets)
    (by intro entry hentry; simp [ensuredInitialContext, LazyRevealProbe.State.empty] at hentry) hresult
  have hcomplete := deferredCompletable_of_no_pending table result.context hcore.2.1 hcore.2.2 hcovered.2
  have hstate : result.context.state.values (.position target) = none :=
    (resolvedPreservesCoordinate_maskedPublishedTreeRoot_of_ne target hne (ensuredInitialContext targets)
      fuel table emptySplitHashCache result hresult).1
  have hmat := rootMaterializationPreserving_maskedPublishedTreeRoot (ensuredInitialContext targets) fuel table
    emptySplitHashCache result (layerRootsMaterialized_ensuredInitialContext targets) (ensuredInitialContext_computed targets) hresult
  have haux : result.context.values target = none := by
    by_contra hknown
    exact hmat target hroot hknown hstate
  have hensured := ensuredLE_of_mem_runResolvedFromTable _ _ fuel table result hresult
  have hpending : result.context.state.pendingAt (.position target) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro digest hhit
    have hentry : (.position target, digest) ∈ result.context.state.pending :=
      (LazyRevealProbe.State.mem_pendingAt_iff _ _ _).mp hhit
    exact List.not_mem_nil (hcovered.2 _ hentry)
  refine ⟨hcovered.1, hcomplete, hensured (ensuredInitialContext_mem_ensured targets target hmem), hstate, haux, hpending, ?_⟩
  have hcache := resolvedOrdinaryCachePreserving_maskedPublishedTreeRoot (ensuredInitialContext targets) fuel table
    emptySplitHashCache result hresult
  intro digest input _
  change ordinaryQueryCache result.value.2 input = none
  rw [hcache]
  rfl

theorem probEvent_chargedRootCut_after_keygen_hit_le_trace_occurrence
    (parameter : PublicParameter) (targets : Finset Position) (target : Position) (hmem : target ∈ targets)
    (hroot : IsLayerRoot target) (hne : target ≠ layerRootPosition topLayer rootTree)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (computation : Digest → OracleComp (OracleWorld + SigningSpec) α)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult (Digest × SplitHashCache))
    (hresult : some result ∈ support (runResolvedFromTable (ensuredInitialContext targets) fuel table
      (maskedPublishedTreeRoot.run emptySplitHashCache))) (ordinal : Nat) (hbudget : ordinal ≤ 2 ^ 126) :
    Pr[fun b => b = false | originalChargedRootCutObservation parameter result.value.1 target ftsSecret
      (computation result.value.1) result.context result.remaining table result.value.2 ∅ ordinal
      (fun pair => pair.2 = some (truncateHash pair.1))] ≤
    Pr[fun trace => chargedNativeRootTraceCutCandidate parameter target trace.1 ≠ none |
      runNativeQueryTrace parameter result.value.1 ftsSecret (outerHashQueryCutAt (computation result.value.1) ordinal)
        result.context result.remaining table result.value.2] *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  obtain ⟨hvalid, hcomplete, hensured, hstate, hvalue, hpending, hcache⟩ :=
    initializedNativeRoot_fresh_facts parameter targets target hmem hroot hne fuel table result hresult
  exact probEvent_originalChargedRootCutObservation_hit_le_trace_occurrence parameter result.value.1 target hroot ftsSecret
    (computation result.value.1) result.context result.remaining table result.value.2 ∅ hvalid hcomplete hensured hstate hvalue
    (by rw [hpending]) (fun digest _ => hcache digest) ordinal (by simpa using hbudget)

end SphincsSecurity.Concrete.OtsProbeSimulation

import SphincsSecurity.Proof.JointProbeOriginalFtsWitness

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational
open OtsProbeSimulation (OtsSecretIndex ResolvedRunResult)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

noncomputable def sharedRoot (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q fuel : Nat) :=
  AdaptiveRevealProbe.runDetailed ftsTable AdaptiveRevealProbe.State.empty q
    (runJointResolved ((jointSourceNativeBlock OtsProbeSimulation.maskedPublishedTreeRoot).run
      (OtsProbeSimulation.emptySplitHashCache, emptySplitHashCache))
      (OtsProbeSimulation.ensuredInitialContext ∅) fuel otsTable)

noncomputable def originalRoot (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) :
    ProbComp (Digest × QueryCache HashSpec) :=
  (simulateQ romImpl (liftM (treeRoot parameter topLayer rootTree
    (fun leafIdx chainIdx => truncateHash (otsTable ⟨topLayer, rootTree, leafIdx, chainIdx⟩)) : OracleComp HashSpec Digest) :
      OracleComp OracleWorld Digest)).run ∅

theorem relTriple_sharedRoot_original
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q fuel : Nat) :
    RelTriple (sharedRoot otsTable ftsTable q fuel) (originalRoot parameter otsTable) (fun left right =>
      JointOriginalRunRel parameter otsTable ftsTable left right ∧
        left ∈ support (sharedRoot otsTable ftsTable q fuel) ∧ right ∈ support (originalRoot parameter otsTable)) := by
  have hjoint := jointResolvedCoupledAt_nativeBlock parameter ftsTable AdaptiveRevealProbe.State.empty q
    OtsProbeSimulation.maskedPublishedTreeRoot (cacheMapCommutes_native_maskedPublishedTreeRoot parameter ftsTable)
    (OtsProbeSimulation.ensuredInitialContext ∅) fuel otsTable (OtsProbeSimulation.emptySplitHashCache, emptySplitHashCache)
    (by simp [AdaptiveRevealProbe.tableHits, AdaptiveRevealProbe.State.empty])
  have hcache : OtsProbeSimulation.replaceOrdinaryCache OtsProbeSimulation.emptySplitHashCache ∅ =
      OtsProbeSimulation.emptySplitHashCache := by
    funext key
    cases key <;> rfl
  simp only [JointResolvedCoupledAt, mergedCache_empty, hcache] at hjoint
  have hnative := OtsProbeSimulation.reachableResolvedCouples_maskedPublishedTreeRoot parameter otsTable
    (OtsProbeSimulation.ensuredInitialContext ∅) fuel OtsProbeSimulation.emptySplitHashCache ∅
    (OtsProbeSimulation.ensuredInitialContext_resolvedInvariant ∅ parameter otsTable)
    (OtsProbeSimulation.ensuredInitialContext_visible ∅ parameter otsTable)
    (OtsProbeSimulation.ensuredInitialContext_published ∅)
  have hbase := relTriple_post_mono (relTriple_trans_exists hjoint hnative)
    (R' := JointOriginalRunRel parameter otsTable ftsTable) (by
      rintro left right ⟨native, hleft, hright⟩
      rcases hleft with hhit | heq
      · exact Or.inl hhit
      · exact Or.inr (heq ▸ hright))
  have hs := relTriple_and_right_support (relTriple_and_left_support hbase _ (fun _ h => h))
  unfold sharedRoot originalRoot
  rw [simulateQ_romImpl_liftM]
  exact relTriple_post_mono hs (fun _ _ h => ⟨h.1.1, h.1.2, h.2⟩)

noncomputable def rootCoupling
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q fuel : Nat) :=
  Classical.choose ((relTriple_iff_relWP).mp (relTriple_sharedRoot_original parameter otsTable ftsTable q fuel))

theorem rootCoupling_support
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q fuel : Nat)
    (pair) (hpair : pair ∈ support (rootCoupling parameter otsTable ftsTable q fuel).1) :
    JointOriginalRunRel parameter otsTable ftsTable pair.1 pair.2 ∧
      pair.1 ∈ support (sharedRoot otsTable ftsTable q fuel) ∧ pair.2 ∈ support (originalRoot parameter otsTable) :=
  Classical.choose_spec ((relTriple_iff_relWP).mp (relTriple_sharedRoot_original parameter otsTable ftsTable q fuel)) pair hpair

noncomputable def rootFrame (otsTable : OtsSecretIndex → HashOutput) (q : Nat) :
    AdaptiveRevealProbe.DetailedResult Coordinate (Option (ResolvedRunResult (Digest × JointSourceCache))) → Option Frame
  | .done false state (some entry) =>
      if OtsProbeSimulation.DeferredCompletable otsTable entry.context then
        some ⟨state, q, entry.context, entry.remaining, entry.value.2⟩
      else none
  | _ => none

noncomputable def initializeRoot
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q fuel : Nat) :
    SPMF (Option Frame × (Digest × QueryCache HashSpec)) :=
  (fun pair => (rootFrame otsTable q pair.1, pair.2)) <$> (rootCoupling parameter otsTable ftsTable q fuel).1

theorem initializeRoot_original
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q fuel : Nat) :
    Prod.snd <$> initializeRoot parameter otsTable ftsTable q fuel = evalDist (originalRoot parameter otsTable) := by
  rw [initializeRoot, Functor.map_map]
  exact (rootCoupling parameter otsTable ftsTable q fuel).2.map_snd

theorem initializeRoot_valid
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q fuel : Nat)
    (pair) (hpair : pair ∈ support (initializeRoot parameter otsTable ftsTable q fuel))
    (frame : Frame) (hframe : pair.1 = some frame) :
    RootSupport otsTable ftsTable q fuel pair.2.1 frame ∧ frame.Valid parameter otsTable ftsTable pair.2.2 := by
  rw [initializeRoot, support_map] at hpair
  obtain ⟨raw, hraw, rfl⟩ := hpair
  have hs := rootCoupling_support parameter otsTable ftsTable q fuel raw hraw
  rcases raw with ⟨left, actual⟩
  cases left with
  | stopped hit => simp [rootFrame] at hframe
  | done hit state entry =>
      cases hit with
      | true => simp [rootFrame] at hframe
      | false =>
          cases entry with
          | none => simp [rootFrame] at hframe
          | some entry =>
              by_cases hc : OtsProbeSimulation.DeferredCompletable otsTable entry.context
              · simp only [rootFrame, if_pos hc, Option.some.injEq] at hframe
                subst frame
                let projected : ResolvedRunResult (Digest × OtsProbeSimulation.SplitHashCache) :=
                  { entry with value := (entry.value.1,
                    OtsProbeSimulation.replaceOrdinaryCache entry.value.2.1 (mergedCache parameter ftsTable entry.value.2.2)) }
                have hi := hs.1.of_completable (entry := projected) rfl
                  (by simp [projectJointResolvedCache, cleanJointResolved, projected]) hc
                have hsynced := invariants_jointSourceNativeBlock parameter ftsTable AdaptiveRevealProbe.State.empty state q
                  OtsProbeSimulation.maskedPublishedTreeRoot (cacheMapCommutes_native_maskedPublishedTreeRoot parameter ftsTable)
                  (OtsProbeSimulation.ensuredInitialContext ∅) fuel otsTable (OtsProbeSimulation.emptySplitHashCache, emptySplitHashCache)
                  entry (revealedSynced_empty parameter ftsTable) hs.2.1
                refine ⟨⟨rfl, ?_⟩, ?_⟩
                · have ht : entry.table = otsTable := hi.1
                  have hv : entry.value.1 = actual.1 := hi.2.1
                  have he : (⟨entry.context, entry.remaining, (actual.1, entry.value.2), otsTable⟩ :
                      ResolvedRunResult (Digest × JointSourceCache)) = entry := by rw [← ht, ← hv]
                  change AdaptiveRevealProbe.DetailedResult.done false state (some _) ∈ support (sharedRoot otsTable ftsTable q fuel)
                  rw [he]
                  exact hs.2.1
                · exact ⟨by simp [hsynced.1, AdaptiveRevealProbe.tableHits, AdaptiveRevealProbe.State.empty],
                    hsynced.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2⟩
              · simp [rootFrame, hc] at hframe

theorem initializeRoot_original_support
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q fuel : Nat)
    (pair) (hpair : pair ∈ support (initializeRoot parameter otsTable ftsTable q fuel)) :
    pair.2 ∈ support (originalRoot parameter otsTable) := by
  rw [initializeRoot, support_map] at hpair
  obtain ⟨raw, hraw, rfl⟩ := hpair
  exact (rootCoupling_support parameter otsTable ftsTable q fuel raw hraw).2.2

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

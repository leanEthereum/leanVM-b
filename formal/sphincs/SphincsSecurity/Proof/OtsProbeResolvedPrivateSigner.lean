import SphincsSecurity.Proof.OtsProbeResolvedPrivateObserver

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp

attribute [local irreducible] maskedSignLayer

theorem evalDist_runDeferredChronologicalLayersAndPublish_canonicalObserve_eq_selectionOnly
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (next : Option Signature → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context) :
    evalDist (runDeferredChronologicalLayersAndPublish parameter table ftsSecret randomness
        index leaves ftsPath context fuel cache >>=
          finishObserve (canonicalContinuationObserve table next)) =
      evalDist (runSelectionOnlyLayersAndPublish parameter table ftsSecret randomness index
        leaves ftsPath context fuel cache >>=
          finishObserve (canonicalContinuationObserve table next)) := by
  calc
    _ = evalDist (runDeferredLayersAndPublish parameter table ftsSecret randomness index leaves
          ftsPath deferredLayerSchedule context fuel cache >>=
            finishObserve (canonicalContinuationObserve table next)) :=
      evalDist_runDeferredChronologicalLayersAndPublish_observe_eq_deferred parameter table
        ftsSecret randomness index leaves ftsPath context fuel cache
          (canonicalContinuationObserve table next)
    _ = _ := evalDist_runDeferredLayersAndPublish_observe_eq_selectionOnly parameter table
      ftsSecret randomness index leaves ftsPath context fuel cache hvalid hcompletable

set_option maxRecDepth 100000 in
theorem evalDist_runDeferredChronologicalSignAfterDigest_canonicalObserve_eq_selectionOnly
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (next : Option Signature → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context) :
    evalDist (runDeferredChronologicalSignAfterDigest parameter table ftsSecret randomness
        index leaves context fuel cache >>=
          finishObserve (canonicalContinuationObserve table next)) =
      evalDist (runSelectionOnlySignAfterDigest parameter table ftsSecret randomness index
        leaves context fuel cache >>=
          finishObserve (canonicalContinuationObserve table next)) := by
  unfold runDeferredChronologicalSignAfterDigest runSelectionOnlySignAfterDigest
  simp only [bind_assoc]
  apply evalDist_bind_congr
  intro ftsOption hfts
  cases ftsOption with
  | none => simp [finishObserve]
  | some ftsResult =>
      have hftsInvariants :=
        valid_completable_of_mem_runResolvedFromTable_of_finalizationMaterializedCouples table
          (simulateQ ordinaryHashImpl
            (ftsOpen parameter index leaves (ftsSecret index)))
          (finalizationMaterializedCouples_simulateQ ordinaryHashImpl
            (finalizationMaterializedCouples_ordinaryHashImpl table)
            (ftsOpen parameter index leaves (ftsSecret index)))
          context fuel cache ftsResult hvalid hcompletable hfts
      exact
        evalDist_runDeferredChronologicalLayersAndPublish_canonicalObserve_eq_selectionOnly
          parameter table ftsSecret randomness index leaves ftsResult.value.1 ftsResult.context
            ftsResult.remaining ftsResult.value.2 next hftsInvariants.1 hftsInvariants.2

set_option maxRecDepth 100000 in
theorem evalDist_runDeferredChronologicalSign_canonicalObserve_eq_selectionOnly
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (next : Option Signature → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context) :
    evalDist (runDeferredChronologicalSign parameter root table ftsSecret message context fuel
        cache >>= finishObserve (canonicalContinuationObserve table next)) =
      evalDist (runSelectionOnlySign parameter root table ftsSecret message context fuel cache >>=
        finishObserve (canonicalContinuationObserve table next)) := by
  unfold runDeferredChronologicalSign runSelectionOnlySign
  simp only [bind_assoc]
  apply evalDist_bind_congr
  intro selectedOption hselected
  cases selectedOption with
  | none => simp [finishObserve]
  | some selected =>
      cases hvalue : selected.value.1 with
      | none => simp [hvalue, finishObserve]
      | some digestResult =>
          rcases digestResult with ⟨randomness, selectedIndex, leaves⟩
          simp only [hvalue]
          let secretKey : SecretKey :=
            ⟨parameter, root, fun _ _ _ _ => 0, ftsSecret⟩
          have hselectedInvariants :=
            valid_completable_of_mem_runResolvedFromTable_of_finalizationMaterializedCouples table
              (simulateQ ordinaryRomImpl
                (signDigestLoop digestAttemptLimit secretKey message))
              (finalizationMaterializedCouples_simulateQ ordinaryRomImpl
                (finalizationMaterializedCouples_ordinaryRomImpl table)
                (signDigestLoop digestAttemptLimit secretKey message))
              context fuel cache selected hvalid hcompletable (by
                simpa only [secretKey] using hselected)
          exact
            evalDist_runDeferredChronologicalSignAfterDigest_canonicalObserve_eq_selectionOnly
              parameter table ftsSecret randomness selectedIndex leaves selected.context
                selected.remaining selected.value.2 next hselectedInvariants.1
                  hselectedInvariants.2

set_option maxRecDepth 100000 in
theorem evalDist_runDeferredChronologicalSign_canonicalObserve_eq_maskedSign
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (next : Option Signature → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context) :
    evalDist (runDeferredChronologicalSign parameter root table ftsSecret message context fuel
        cache >>= finishObserve (canonicalContinuationObserve table next)) =
      evalDist (runResolvedObserve (canonicalContinuationObserve table next) context fuel table
        ((maskedSign parameter root ftsSecret message).run cache)) := by
  calc
    _ = evalDist (runSelectionOnlySign parameter root table ftsSecret message context fuel cache >>=
          finishObserve (canonicalContinuationObserve table next)) :=
      evalDist_runDeferredChronologicalSign_canonicalObserve_eq_selectionOnly parameter root
        table ftsSecret message context fuel cache next hvalid hcompletable
    _ = evalDist (runResolvedFromTable context fuel table
          ((maskedSign parameter root ftsSecret message).run cache) >>=
            finishObserve (canonicalContinuationObserve table next)) := by
      rw [evalDist_bind, evalDist_bind,
        evalDist_runSelectionOnlySign_eq_resolved parameter root table ftsSecret message context
          fuel cache hvalid.valuesConsistent
            (startTableAgrees_of_deferredCompletable hcompletable)]
    _ = _ := rfl

end SphincsSecurity.Concrete.OtsProbeSimulation

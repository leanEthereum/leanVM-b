import SphincsSecurity.Proof.FtsProbeJointDigestOrigin
import SphincsSecurity.Proof.FtsProbeJointSignerCache
import SphincsSecurity.Proof.OtsProbeHistoryOrdinaryRom

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] signDigestLoop

theorem successfulDigestRun_of_nativeHistory
    (secretKey : SecretKey) (message : Message) (attempts : Nat)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache)
    (entry : OtsProbeSimulation.HistoryResolvedPrefix
      (Option (Randomness × Index × (DigestTree → FtsLeaf)) × OtsProbeSimulation.SplitHashCache))
    (finalCache : QueryCache HashSpec) (f : QueryImpl HashSpec Id)
    (hresult : some entry ∈ support (OtsProbeSimulation.runResolvedHistoryPrefix
      (OtsProbeSimulation.eraseProbeQueries
        ((simulateQ OtsProbeSimulation.ordinaryRomImpl (signDigestLoop attempts secretKey message)).run cache))
      context fuel history))
    (hselected : entry.value.1 = some (randomness, index, leaves))
    (hle : OtsProbeSimulation.ordinaryQueryCache entry.value.2 ≤ finalCache)
    (hf : finalCache.AgreesWithFn f) :
    SuccessfulDigestRun f finalCache secretKey message randomness index leaves := by
  have hactual := OtsProbeSimulation.mem_support_ordinaryRom_of_historyPrefix
    (signDigestLoop attempts secretKey message) context fuel history cache entry hresult
  rw [hselected] at hactual
  have hreplay := replayRom_of_mem_support (signDigestLoop attempts secretKey message)
    (OtsProbeSimulation.ordinaryQueryCache cache) (some (randomness, index, leaves))
    (OtsProbeSimulation.ordinaryQueryCache entry.value.2) hactual f (fun input output hcached => hf (hle hcached))
  exact successfulDigestLoop_of_mem_support f secretKey message attempts randomness index leaves
    (OtsProbeSimulation.ordinaryQueryCache cache) (OtsProbeSimulation.ordinaryQueryCache entry.value.2)
    finalCache hreplay hle hf

def PublishedNativeDigestRunCoordinate
    (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec) (secretKey : SecretKey) (message : Message)
    (result : NativePublicationResult) (coordinate : Coordinate) : Prop :=
  ∃ entry signature index leaves,
    result = some entry ∧ entry.value.1 = some signature ∧
    SuccessfulDigestRun f cache secretKey message signature.randomness index leaves ∧
    SelectedCoordinate index leaves coordinate

theorem revealedOnlyFrom_maskedJointSign_finalCache
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → Digest) (message : Message)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache finalCache : SplitHashCache) (result : NativePublicationResult)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state ftsCache)
    (f : QueryImpl HashSpec Id)
    (hf : (mergedCache parameter table finalCache).AgreesWithFn f)
    (hresult : .done false finalState (result, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel
        ((maskedJointSign parameter root message context fuel history cache).run ftsCache))) :
    RevealedOnlyFrom state finalState
      (PublishedNativeDigestRunCoordinate f (mergedCache parameter table finalCache) (jointDigestKey parameter root) message result) := by
  unfold maskedJointSign at hresult
  refine revealedOnlyFrom_bindNativeSteps table state finalState ftsFuel _ _ context fuel history cache ftsCache finalCache result
    (PublishedNativeDigestRunCoordinate f (mergedCache parameter table finalCache) (jointDigestKey parameter root) message result)
    hclean (liftNativeBlock_probeFree _ context fuel history cache) ?_ ?_ hresult
  · intro stepState entry stepCache hleft
    exact state_eq_liftNativeBlock table state stepState ftsFuel _ context fuel history cache ftsCache stepCache entry hleft
  · intro stepState entry stepCache hleft hnext
    obtain ⟨hstate, hsynced', _⟩ := invariants_liftNativeBlock parameter table state stepState ftsFuel _
      (fun cache => cacheMapCommutes_native_signDigestLoop (jointDigestKey parameter root) table cache message digestAttemptLimit)
      context fuel history cache ftsCache stepCache (some entry) hsynced hleft
    cases hselected : entry.value.1 with
    | none =>
        simp only [hselected] at hnext
        have hstate' := state_eq_liftNativeBlock table stepState finalState ftsFuel _
          entry.context entry.remaining entry.history entry.value.2 stepCache finalCache result hnext
        rw [hstate']
        exact fun _ _ h => Or.inl h
    | some selected =>
        rcases selected with ⟨randomness, index, leaves⟩
        simp only [hselected] at hnext
        have horigin := revealedOnlyFrom_maskedJointSignAfterDigest_withRandomness parameter table randomness index leaves
          stepState finalState ftsFuel entry.context entry.remaining entry.history entry.value.2 stepCache finalCache result
          (by simpa [hstate] using hclean) hsynced' hnext
        have hcoupled : NativeStepCoupledAt parameter table state ftsFuel
            (liftNativeBlock (simulateQ OtsProbeSimulation.ordinaryRomImpl
              (signDigestLoop digestAttemptLimit (jointDigestKey parameter root) message)))
            (simulateQ OtsProbeSimulation.ordinaryRomImpl
              (signDigestLoop digestAttemptLimit (jointDigestKey parameter root) message)) context fuel history cache ftsCache :=
          projectNativeStepCache_liftNativeBlock parameter table state ftsFuel ftsCache _
            (cacheMapCommutes_native_signDigestLoop (jointDigestKey parameter root) table ftsCache message digestAttemptLimit)
            context fuel history cache hclean
        intro coordinate value hrevealed
        rcases horigin coordinate value hrevealed with hold | ⟨published, signature, hpublished, hsignature, hrandomness, hcoordinate⟩
        · exact Or.inl hold
        · subst result
          have hle := mergedCache_le_maskedJointSignAfterDigest parameter table randomness index leaves
            stepState finalState ftsFuel entry.context entry.remaining entry.history entry.value.2 stepCache finalCache published
            (by simpa [hstate] using hclean) hsynced' hnext
          have hdigest := successfulDigestRun_of_nativeHistory (jointDigestKey parameter root) message digestAttemptLimit
            randomness index leaves context fuel history
            (OtsProbeSimulation.replaceOrdinaryCache cache (mergedCache parameter table ftsCache))
            (OtsProbeSimulation.replaceHistoryOrdinaryCache (mergedCache parameter table stepCache) entry)
            (mergedCache parameter table finalCache) f
            (hcoupled.mem_support_native hleft) hselected hle hf
          exact Or.inr ⟨published, signature, index, leaves, rfl, hsignature,
            by simpa only [hrandomness] using hdigest, hcoordinate⟩

end SphincsSecurity.Concrete.FtsProbeSimulation

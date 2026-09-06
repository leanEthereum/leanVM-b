import SphincsSecurity.Proof.FtsProbeJointSignerRandomness

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] signDigestLoop

def NativeDigestSelection
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → Digest) (message : Message)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) : Prop :=
  ∃ entry, some entry ∈ support (OtsProbeSimulation.runResolvedHistoryPrefix
      (OtsProbeSimulation.eraseProbeQueries
        ((simulateQ OtsProbeSimulation.ordinaryRomImpl
          (signDigestLoop digestAttemptLimit (jointDigestKey parameter root) message)).run
            (OtsProbeSimulation.replaceOrdinaryCache cache (mergedCache parameter table ftsCache)))) context fuel history) ∧
    entry.value.1 = some (randomness, index, leaves)

def PublishedNativeDigestCoordinate
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → Digest) (message : Message)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache)
    (result : NativePublicationResult) (coordinate : Coordinate) : Prop :=
  ∃ randomness index leaves,
    NativeDigestSelection parameter root table message context fuel history cache ftsCache randomness index leaves ∧
    PublishedNativeCoordinateAtRandomness randomness index leaves result coordinate

theorem revealedOnlyFrom_maskedJointSign
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → Digest) (message : Message)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache finalCache : SplitHashCache) (result : NativePublicationResult)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state ftsCache)
    (hresult : .done false finalState (result, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel
        ((maskedJointSign parameter root message context fuel history cache).run ftsCache))) :
    RevealedOnlyFrom state finalState
      (PublishedNativeDigestCoordinate parameter root table message context fuel history cache ftsCache result) := by
  unfold maskedJointSign at hresult
  refine revealedOnlyFrom_bindNativeSteps table state finalState ftsFuel _ _ context fuel history cache ftsCache finalCache result
    (PublishedNativeDigestCoordinate parameter root table message context fuel history cache ftsCache result)
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
        have hselection : NativeDigestSelection parameter root table message context fuel history cache ftsCache randomness index leaves :=
          ⟨OtsProbeSimulation.replaceHistoryOrdinaryCache (mergedCache parameter table stepCache) entry,
            hcoupled.mem_support_native hleft, hselected⟩
        intro coordinate value hrevealed
        rcases horigin coordinate value hrevealed with hold | hnew
        · exact Or.inl hold
        · exact Or.inr ⟨randomness, index, leaves, hselection, hnew⟩

theorem maskedJointSign_no_new_reveals_of_no_signature
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → Digest) (message : Message)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache finalCache : SplitHashCache) (result : NativePublicationResult)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state ftsCache)
    (hfailed : result.bind (fun entry => entry.value.1) = none)
    (hresult : .done false finalState (result, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel
        ((maskedJointSign parameter root message context fuel history cache).run ftsCache))) :
    ∀ coordinate value, finalState.revealed coordinate = some value → state.revealed coordinate = some value := by
  have horigin := revealedOnlyFrom_maskedJointSign parameter root table message state finalState ftsFuel
    context fuel history cache ftsCache finalCache result hclean hsynced hresult
  intro coordinate value hrevealed
  rcases horigin coordinate value hrevealed with hold | ⟨randomness, index, leaves, _, entry, signature, rfl, hsignature, _, _⟩
  · exact hold
  · simp only [Option.bind_some, hsignature, reduceCtorEq] at hfailed

end SphincsSecurity.Concrete.FtsProbeSimulation

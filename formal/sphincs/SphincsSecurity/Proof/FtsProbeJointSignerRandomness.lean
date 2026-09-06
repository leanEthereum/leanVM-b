import SphincsSecurity.Proof.FtsProbeJointSignerOrigin
import SphincsSecurity.Proof.OtsProbeSignatureRandomness

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] OtsProbeSimulation.maskedPublishedChronologicalSignAfterDigest

theorem NativeStepCoupledAt.mem_support_native
    {parameter : PublicParameter} {table : Coordinate → Digest}
    {state finalState : AdaptiveRevealProbe.State Coordinate} {ftsFuel : Nat}
    {masked : NativeFtsStep α}
    {native : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α}
    {context : OtsProbeSimulation.DeferredContext} {fuel : Nat} {history : List OtsProbeSimulation.Probe}
    {cache : OtsProbeSimulation.SplitHashCache} {ftsCache finalCache : SplitHashCache}
    {entry : OtsProbeSimulation.HistoryResolvedPrefix (α × OtsProbeSimulation.SplitHashCache)}
    (h : NativeStepCoupledAt parameter table state ftsFuel masked native context fuel history cache ftsCache)
    (hresult : .done false finalState (some entry, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel ((masked context fuel history cache).run ftsCache))) :
    some (OtsProbeSimulation.replaceHistoryOrdinaryCache (mergedCache parameter table finalCache) entry) ∈ support
      (OtsProbeSimulation.runResolvedHistoryPrefix
        (OtsProbeSimulation.eraseProbeQueries
          (native.run (OtsProbeSimulation.replaceOrdinaryCache cache (mergedCache parameter table ftsCache)))) context fuel history) := by
  rw [← h, support_map]
  exact ⟨.done false finalState (some entry, finalCache), hresult, rfl⟩

theorem maskedJointSignAfterDigest_randomness_of_mem
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache finalCache : SplitHashCache)
    (entry : OtsProbeSimulation.HistoryResolvedPrefix (Option Signature × OtsProbeSimulation.SplitHashCache)) (signature : Signature)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state ftsCache) (hvalue : entry.value.1 = some signature)
    (hresult : .done false finalState (some entry, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel
        ((maskedJointSignAfterDigest parameter randomness index leaves context fuel history cache).run ftsCache))) :
    signature.randomness = randomness := by
  have hnative := (coupled_maskedJointSignAfterDigest parameter table randomness index leaves state ftsFuel
    context fuel history cache ftsCache hclean hsynced).mem_support_native hresult
  rw [OtsProbeSimulation.eraseProbeQueries_eq_of_probeFree _
    (OtsProbeSimulation.maskedPublishedChronologicalSignAfterDigest_probeFree parameter
      (fun index tree leaf => table (index, tree, leaf)) randomness index leaves _)] at hnative
  have hraw := OtsProbeSimulation.mem_support_of_historyPrefix _ context fuel history _ hnative
  have hraw' : (some signature, OtsProbeSimulation.replaceOrdinaryCache entry.value.2 (mergedCache parameter table finalCache)) ∈ support
      ((OtsProbeSimulation.maskedPublishedChronologicalSignAfterDigest parameter
        (fun index tree leaf => table (index, tree, leaf)) randomness index leaves).run
          (OtsProbeSimulation.replaceOrdinaryCache cache (mergedCache parameter table ftsCache))) := by
    simpa only [OtsProbeSimulation.replaceHistoryOrdinaryCache, hvalue] using hraw
  exact OtsProbeSimulation.maskedPublishedChronologicalSignAfterDigest_randomness_of_mem parameter
    (fun index tree leaf => table (index, tree, leaf)) randomness index leaves _ _ signature hraw'

def PublishedNativeCoordinateAtRandomness (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (result : NativePublicationResult) (coordinate : Coordinate) : Prop :=
  ∃ entry signature, result = some entry ∧ entry.value.1 = some signature ∧ signature.randomness = randomness ∧
    SelectedCoordinate index leaves coordinate

theorem revealedOnlyFrom_maskedJointSignAfterDigest_withRandomness
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache finalCache : SplitHashCache) (result : NativePublicationResult)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state ftsCache)
    (hresult : .done false finalState (result, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel
        ((maskedJointSignAfterDigest parameter randomness index leaves context fuel history cache).run ftsCache))) :
    RevealedOnlyFrom state finalState (PublishedNativeCoordinateAtRandomness randomness index leaves result) := by
  have horigin := revealedOnlyFrom_maskedJointSignAfterDigest parameter table randomness index leaves state finalState ftsFuel
    context fuel history cache ftsCache finalCache result hclean hsynced hresult
  intro coordinate value hrevealed
  rcases horigin coordinate value hrevealed with hold | ⟨entry, signature, rfl, hsignature, hselected⟩
  · exact Or.inl hold
  · exact Or.inr ⟨entry, signature, rfl, hsignature, maskedJointSignAfterDigest_randomness_of_mem parameter table randomness index leaves
      state finalState ftsFuel context fuel history cache ftsCache finalCache entry signature hclean hsynced hsignature hresult, hselected⟩

end SphincsSecurity.Concrete.FtsProbeSimulation

import SphincsSecurity.Proof.FtsProbeJointDigestReplay

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem PublishedNativeDigestRunCoordinate.coveredByLog
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec} {secretKey : SecretKey} {message : Message}
    {result : NativePublicationResult} {coordinate : Coordinate} {log : QueryLog SigningSpec}
    (horigin : PublishedNativeDigestRunCoordinate f cache secretKey message result coordinate)
    (hlog : ∀ entry signature, result = some entry → entry.value.1 = some signature →
      (⟨message, some signature⟩ : SigningEntry) ∈ log) :
    CoveredByLog f cache secretKey log coordinate := by
  obtain ⟨entry, signature, index, leaves, hentry, hsignature, hdigest, hcoordinate⟩ := horigin
  exact ⟨message, signature, index, leaves, hlog entry signature hentry hsignature, hdigest, hcoordinate⟩

theorem revealedOnlyFrom_maskedJointSign_signingLog
    (secretKey : SecretKey) (table : Coordinate → Digest) (message : Message)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache finalCache : SplitHashCache)
    (entry : OtsProbeSimulation.HistoryResolvedPrefix (Option Signature × OtsProbeSimulation.SplitHashCache))
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced secretKey.parameter table state ftsCache)
    (f : QueryImpl HashSpec Id)
    (hf : (mergedCache secretKey.parameter table finalCache).AgreesWithFn f)
    (hresult : .done false finalState (some entry, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel
        ((maskedJointSign secretKey.parameter secretKey.root message context fuel history cache).run ftsCache))) :
    RevealedOnlyFrom state finalState
      (CoveredByLog f (mergedCache secretKey.parameter table finalCache) secretKey
        [⟨message, entry.value.1⟩]) := by
  have horigin := revealedOnlyFrom_maskedJointSign_finalCache secretKey.parameter secretKey.root table message
    state finalState ftsFuel context fuel history cache ftsCache finalCache (some entry) hclean hsynced f hf hresult
  intro coordinate value hrevealed
  rcases horigin coordinate value hrevealed with hold | hnew
  · exact Or.inl hold
  · obtain ⟨published, signature, index, leaves, heq, hsignature, hdigest, hcoordinate⟩ := hnew
    cases Option.some.inj heq
    refine Or.inr ⟨message, signature, index, leaves, ?_, ?_, hcoordinate⟩
    · simp only [hsignature, List.mem_singleton]
    · exact OtsProbeSimulation.successfulDigestRun_changeSecretKey hdigest rfl rfl

end SphincsSecurity.Concrete.FtsProbeSimulation

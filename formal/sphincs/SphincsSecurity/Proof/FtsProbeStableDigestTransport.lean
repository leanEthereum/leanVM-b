import SphincsSecurity.Proof.FtsProbeStableExecutionCache

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def stableOrdinarySubcache (parameter : PublicParameter) (cache : QueryCache HashSpec) : QueryCache HashSpec :=
  fun input => if OtsProbeSimulation.StableOrdinaryInput parameter input then cache input else none

theorem successfulDigestRun_transport_stable
    {secretKey : SecretKey} {message : Message} {randomness : Randomness} {index : Index} {leaves : DigestTree → FtsLeaf}
    {initial final : QueryCache HashSpec} {before after : QueryImpl HashSpec Id}
    (hstable : OtsProbeSimulation.StableOrdinaryCacheLE secretKey.parameter
      (OtsProbeSimulation.replaceOrdinaryCache OtsProbeSimulation.emptySplitHashCache initial)
      (OtsProbeSimulation.replaceOrdinaryCache OtsProbeSimulation.emptySplitHashCache final))
    (hbefore : initial.AgreesWithFn before) (hafter : final.AgreesWithFn after)
    (hrun : SuccessfulDigestRun before initial secretKey message randomness index leaves) :
    SuccessfulDigestRun after final secretKey message randomness index leaves := by
  let shared := stableOrdinarySubcache secretKey.parameter initial
  have hle : shared ≤ final := by
    intro input output houtput
    dsimp [shared, stableOrdinarySubcache] at houtput
    split_ifs at houtput with hinput
    exact hstable input output hinput houtput
  have hbefore' : shared.AgreesWithFn before := by
    intro input output houtput
    dsimp [shared, stableOrdinarySubcache] at houtput
    split_ifs at houtput with hinput
    exact hbefore houtput
  have hafter' : shared.AgreesWithFn after := fun _ _ houtput => hafter (hle houtput)
  have hcached : CachedRun shared before (signAttempt secretKey message randomness) := by
    intro input hinput
    have hstableInput := OtsProbeSimulation.queriesStable_signAttempt before secretKey message randomness input hinput
    simpa only [shared, stableOrdinarySubcache, if_pos hstableInput] using hrun.2.2 input hinput
  refine ⟨hrun.1, ?_, CachedRun.mono hle (hcached.changeAnswerFn hbefore' hafter')⟩
  exact (hcached.eval_eq hbefore' hafter').symm.trans hrun.2.1

theorem CoveredByLog.transport_stable
    {secretKey : SecretKey} {log : QueryLog SigningSpec} {coordinate : Coordinate}
    {initial final : QueryCache HashSpec} {before after : QueryImpl HashSpec Id}
    (hcovered : CoveredByLog before initial secretKey log coordinate)
    (hstable : OtsProbeSimulation.StableOrdinaryCacheLE secretKey.parameter
      (OtsProbeSimulation.replaceOrdinaryCache OtsProbeSimulation.emptySplitHashCache initial)
      (OtsProbeSimulation.replaceOrdinaryCache OtsProbeSimulation.emptySplitHashCache final))
    (hbefore : initial.AgreesWithFn before) (hafter : final.AgreesWithFn after) :
    CoveredByLog after final secretKey log coordinate := by
  obtain ⟨message, signature, index, leaves, hlog, hrun, hcoordinate⟩ := hcovered
  exact ⟨message, signature, index, leaves, hlog,
    successfulDigestRun_transport_stable hstable hbefore hafter hrun, hcoordinate⟩

noncomputable def cacheAnswerFn (cache : QueryCache HashSpec) : QueryImpl HashSpec Id :=
  fun input => (cache input).getD 0

theorem cacheAnswerFn_agrees (cache : QueryCache HashSpec) : cache.AgreesWithFn (cacheAnswerFn cache) := by
  intro input output houtput
  simp [cacheAnswerFn, houtput]

theorem revealedOnlyFrom_maskedJointSign_laterCache
    (secretKey : SecretKey) (table : Coordinate → Digest) (message : Message)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache finalCache targetCache : SplitHashCache)
    (entry : OtsProbeSimulation.HistoryResolvedPrefix (Option Signature × OtsProbeSimulation.SplitHashCache))
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced secretKey.parameter table state ftsCache)
    (hstable : StableMergedCacheLE secretKey.parameter table finalCache targetCache)
    (f : QueryImpl HashSpec Id) (hf : (mergedCache secretKey.parameter table targetCache).AgreesWithFn f)
    (hresult : .done false finalState (some entry, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel
        ((maskedJointSign secretKey.parameter secretKey.root message context fuel history cache).run ftsCache))) :
    RevealedOnlyFrom state finalState
      (CoveredByLog f (mergedCache secretKey.parameter table targetCache) secretKey [⟨message, entry.value.1⟩]) := by
  have horigin := revealedOnlyFrom_maskedJointSign_signingLog secretKey table message state finalState ftsFuel
    context fuel history cache ftsCache finalCache entry hclean hsynced
    (cacheAnswerFn (mergedCache secretKey.parameter table finalCache))
    (cacheAnswerFn_agrees _) hresult
  intro coordinate value hrevealed
  rcases horigin coordinate value hrevealed with hold | hnew
  · exact Or.inl hold
  · exact Or.inr (hnew.transport_stable hstable (cacheAnswerFn_agrees _) hf)

end SphincsSecurity.Concrete.FtsProbeSimulation

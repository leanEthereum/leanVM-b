import SphincsSecurity.Proof.FtsProbeJointLogCoverage
import SphincsSecurity.Proof.OuterHashQueryCapTrace

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem revealedOnlyFrom_maskedJointCappedSigningTrace
    (secretKey : SecretKey) (table : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (value : α) (log : QueryLog SigningSpec)
    (state finalState : AdaptiveRevealProbe.State Coordinate)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache finalCache : SplitHashCache)
    (entry : OtsProbeSimulation.HistoryResolvedPrefix (Option (α × QueryLog SigningSpec) × OtsProbeSimulation.SplitHashCache))
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced secretKey.parameter table state ftsCache)
    (f : QueryImpl HashSpec Id) (hf : (mergedCache secretKey.parameter table finalCache).AgreesWithFn f)
    (hvalue : entry.value.1 = some (value, log))
    (hresult : .done false finalState (some entry, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state q
        ((maskedJointComputation secretKey.parameter secretKey.root
          (OtsProbeSimulation.capOuterHashQueries (signingTraceComputation computation) q)
          context fuel history cache).run ftsCache))) :
    RevealedOnlyFrom state finalState (CoveredByLog f (mergedCache secretKey.parameter table finalCache) secretKey log) := by
  rw [OtsProbeSimulation.capOuterHashQueries_signingTrace] at hresult
  apply revealedOnlyFrom_maskedJointSigningTrace_map secretKey table (OtsProbeSimulation.capOuterHashQueries computation q)
    OtsProbeSimulation.completedSigningTrace log state finalState q context fuel history cache ftsCache finalCache entry
    _ hclean hsynced f hf _ hresult
  · rw [isQueryBoundP_map_iff]
    exact OtsProbeSimulation.isQueryBoundP_signingTraceComputation _ q
      (OtsProbeSimulation.capOuterHashQueries_hashBound computation q)
  · intro selected tail hproject signed hsigned
    rw [hvalue] at hproject
    cases selected with
    | none => cases hproject
    | some selected =>
        have htail : tail = log := congrArg (fun result => result.map Prod.snd) hproject |> Option.some.inj
        exact htail ▸ hsigned

end SphincsSecurity.Concrete.FtsProbeSimulation

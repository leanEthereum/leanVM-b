import SphincsSecurity.Proof.FtsProbeNativeHistory

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem stableOrdinaryInput_of_decodeProbe
    (parameter : PublicParameter) (input : HashInput) (probe : FtsSecretProbe)
    (hdecode : decodeProbe? parameter input = some probe) :
    OtsProbeSimulation.StableOrdinaryInput parameter input := by
  rw [← (decodeProbe?_eq_some_iff parameter input probe).1 hdecode]
  exact OtsProbeSimulation.stableOrdinaryInput_tweakableHashInput parameter
    (.ftsLeaf probe.index probe.tree probe.leafIdx) (digestBytes probe.candidate)
    (by trivial) (by simp) (by simp) (by simp)

theorem nativeProbingHashQuery_eq_ordinary_of_decodeProbe
    (parameter : PublicParameter) (input : HashInput) (probe : FtsSecretProbe)
    (hdecode : decodeProbe? parameter input = some probe) :
    OtsProbeSimulation.probingHashQuery parameter input =
      OtsProbeSimulation.ordinaryHashImpl input :=
  OtsProbeSimulation.probingHashQuery_eq_splitHashQuery_of_stable parameter input
    (stableOrdinaryInput_of_decodeProbe parameter input probe hdecode)

def NativeCleanStepRel (parameter : PublicParameter) (table : Coordinate → Digest)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat)
    (history : List OtsProbeSimulation.Probe) (cache : OtsProbeSimulation.SplitHashCache)
    (masked : AdaptiveRevealProbe.DetailedResult Coordinate (α × SplitHashCache))
    (native : Option (OtsProbeSimulation.HistoryResolvedPrefix (α × OtsProbeSimulation.SplitHashCache))) : Prop :=
  masked.hit = true ∨ ∃ ordinary,
    native = OtsProbeSimulation.ordinaryHistoryResult context fuel history cache ordinary ∧
      CleanResultRel parameter table masked ordinary

theorem relTriple_nativeHistory_probingHashQuery
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (remaining : Nat)
    (ftsCache : SplitHashCache) (input : HashInput)
    (context : OtsProbeSimulation.DeferredContext) (otsFuel : Nat)
    (history : List OtsProbeSimulation.Probe) (otsCache : OtsProbeSimulation.SplitHashCache)
    (hstable : OtsProbeSimulation.StableOrdinaryInput parameter input)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state ftsCache)
    (hcache : OtsProbeSimulation.ordinaryQueryCache otsCache = mergedCache parameter table ftsCache) :
    RelTriple
      (AdaptiveRevealProbe.runDetailed table state (remaining + 1)
        ((probingHashQuery parameter input).run ftsCache))
      (OtsProbeSimulation.runResolvedHistoryPrefix
        (OtsProbeSimulation.eraseProbeQueries
          ((OtsProbeSimulation.probingHashQuery parameter input).run otsCache))
        context otsFuel history)
      (NativeCleanStepRel parameter table context otsFuel history otsCache) := by
  rw [OtsProbeSimulation.probingHashQuery_eq_splitHashQuery_of_stable parameter input hstable]
  have hordinary := OtsProbeSimulation.runErasedHistoryPrefix_simulateQ_ordinaryHashImpl
    (liftM (OracleSpec.query (spec := HashSpec) input) : OracleComp HashSpec HashOutput)
    context otsFuel history otsCache
  simp only [simulateQ_spec_query, OtsProbeSimulation.ordinaryHashImpl] at hordinary
  rw [hordinary, hcache]
  have h := relTriple_probingHashQuery_step parameter table state remaining ftsCache input hclean hsynced
  have hm := relTriple_post_mono h (R' := fun masked ordinary =>
    NativeCleanStepRel parameter table context otsFuel history otsCache masked
      (OtsProbeSimulation.ordinaryHistoryResult context otsFuel history otsCache ordinary))
    (fun masked ordinary hstep => by
      rcases hstep with hhit | hstep
      · exact Or.inl hhit
      · exact Or.inr ⟨ordinary, rfl, hstep⟩)
  simpa only [id_map] using
    (relTriple_map (f := id)
      (g := OtsProbeSimulation.ordinaryHistoryResult context otsFuel history otsCache) hm)

theorem relTriple_nativeHistory_ftsProbe
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (remaining : Nat)
    (ftsCache : SplitHashCache) (input : HashInput) (probe : FtsSecretProbe)
    (context : OtsProbeSimulation.DeferredContext) (otsFuel : Nat)
    (history : List OtsProbeSimulation.Probe) (otsCache : OtsProbeSimulation.SplitHashCache)
    (hdecode : decodeProbe? parameter input = some probe)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state ftsCache)
    (hcache : OtsProbeSimulation.ordinaryQueryCache otsCache = mergedCache parameter table ftsCache) :
    RelTriple
      (AdaptiveRevealProbe.runDetailed table state (remaining + 1)
        ((probingHashQuery parameter input).run ftsCache))
      (OtsProbeSimulation.runResolvedHistoryPrefix
        (OtsProbeSimulation.eraseProbeQueries
          ((OtsProbeSimulation.probingHashQuery parameter input).run otsCache))
        context otsFuel history)
      (NativeCleanStepRel parameter table context otsFuel history otsCache) :=
  relTriple_nativeHistory_probingHashQuery parameter table state remaining ftsCache input
    context otsFuel history otsCache (stableOrdinaryInput_of_decodeProbe parameter input probe hdecode)
    hclean hsynced hcache

theorem NativeCleanStepRel.done_false
    {parameter : PublicParameter} {table : Coordinate → Digest}
    {context : OtsProbeSimulation.DeferredContext} {fuel : Nat}
    {history : List OtsProbeSimulation.Probe} {cache : OtsProbeSimulation.SplitHashCache}
    {state : AdaptiveRevealProbe.State Coordinate} {output : α} {ftsCache : SplitHashCache}
    {native : Option (OtsProbeSimulation.HistoryResolvedPrefix (α × OtsProbeSimulation.SplitHashCache))}
    (h : NativeCleanStepRel parameter table context fuel history cache
      (.done false state (output, ftsCache)) native) :
    native = OtsProbeSimulation.ordinaryHistoryResult context fuel history cache
        (output, mergedCache parameter table ftsCache) ∧
      AdaptiveRevealProbe.tableHits state table = false ∧
        RevealedSynced parameter table state ftsCache := by
  rcases h with hhit | ⟨ordinary, hnative, hclean⟩
  · simp [AdaptiveRevealProbe.DetailedResult.hit] at hhit
  · rcases hclean with ⟨_, rfl, htable, hsynced⟩
    exact ⟨hnative, htable, hsynced⟩

theorem runErasedHistoryPrefix_capped_ftsProbe
    (parameter : PublicParameter) (input : HashInput) (probe : FtsSecretProbe)
    (next : HashOutput × OtsProbeSimulation.SplitHashCache →
      OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate) α)
    (q : Nat) (context : OtsProbeSimulation.DeferredContext) (fuel : Nat)
    (history : List OtsProbeSimulation.Probe) (cache : OtsProbeSimulation.SplitHashCache)
    (hdecode : decodeProbe? parameter input = some probe) :
    OtsProbeSimulation.runResolvedHistoryPrefix
      (OtsProbeSimulation.eraseProbeQueries (OtsProbeSimulation.capProbeQueries
        (((OtsProbeSimulation.probingHashQuery parameter input).run cache) >>= next) q))
      context fuel history =
      ((randomOracle (spec := HashSpec) input).run (OtsProbeSimulation.ordinaryQueryCache cache) >>= fun result =>
        OtsProbeSimulation.runResolvedHistoryPrefix
          (OtsProbeSimulation.eraseProbeQueries (OtsProbeSimulation.capProbeQueries
            (next (result.1, OtsProbeSimulation.replaceOrdinaryCache cache result.2)) q))
          context fuel history) := by
  rw [nativeProbingHashQuery_eq_ordinary_of_decodeProbe parameter input probe hdecode]
  simpa only [simulateQ_spec_query] using OtsProbeSimulation.runErasedHistoryPrefix_capped_ordinary_block
    (liftM (OracleSpec.query (spec := HashSpec) input) : OracleComp HashSpec HashOutput) next q context fuel history cache

end SphincsSecurity.Concrete.FtsProbeSimulation

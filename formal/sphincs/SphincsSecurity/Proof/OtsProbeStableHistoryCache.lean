import SphincsSecurity.Proof.OtsProbeQueryCacheMap
import SphincsSecurity.Proof.OtsProbeHistorySupport
import SphincsSecurity.Proof.OtsProbeHistoryOrdinaryHash

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def pinOrdinaryEntry (input : HashInput) (output : HashOutput) (cache : SplitHashCache) : SplitHashCache :=
  Function.update cache (.ordinary input) (some output)

theorem pinOrdinaryEntry_update_other
    (input : HashInput) (output : HashOutput) (key : SplitHashKey) (value : Option HashOutput)
    (hne : key ≠ .ordinary input) (cache : SplitHashCache) :
    pinOrdinaryEntry input output (Function.update cache key value) =
      Function.update (pinOrdinaryEntry input output cache) key value := by
  funext other
  by_cases hkey : other = key <;> by_cases hinput : other = .ordinary input <;>
    simp_all [pinOrdinaryEntry, Function.update]

theorem cacheMapCommutes_pin_ordinaryHash
    (input query : HashInput) (output : HashOutput) (hne : query ≠ input) :
    CacheMapCommutes (pinOrdinaryEntry input output) (ordinaryHashImpl query) := by
  intro cache
  change (splitHashQuery (.ordinary query)).run _ =
    (fun result => (result.1, pinOrdinaryEntry input output result.2)) <$> (splitHashQuery (.ordinary query)).run cache
  rw [splitHashQuery_run_eq, splitHashQuery_run_eq]
  have hlookup : pinOrdinaryEntry input output cache (.ordinary query) = cache (.ordinary query) := by
    simp [pinOrdinaryEntry, hne]
  rw [hlookup]
  cases cache (.ordinary query) with
  | some value => rfl
  | none =>
      rw [map_bind]
      apply bind_congr
      intro value
      simp only [map_pure]
      rw [pinOrdinaryEntry_update_other input output (.ordinary query) (some value) (by simpa using hne)]

theorem cacheMapCommutes_pin_resolveKnownInput
    (parameter : PublicParameter) (input query : HashInput) (output : HashOutput)
    (coordinate : Coordinate) (hne : query ≠ input) :
    CacheMapCommutes (pinOrdinaryEntry input output) (resolveKnownInput parameter coordinate query) := by
  unfold resolveKnownInput
  apply (cacheMapCommutes_peekTableInput _ parameter coordinate).bind
  intro known
  cases known with
  | none => exact cacheMapCommutes_pin_ordinaryHash input query output hne
  | some known =>
      simp only
      split
      · apply (cacheMapCommutes_revealCoordinateOutput _ (fun cache coordinate value =>
          pinOrdinaryEntry_update_other input output (.hidden coordinate) (some value) (by simp) cache) coordinate).bind
        intro value
        apply (CacheMapCommutes.liftM _ (LazyRevealProbe.publishQuery coordinate)).bind
        intro _
        apply (CacheMapCommutes.modify _ _ (pinOrdinaryEntry_update_other input output (.ordinary query)
          (some value) (by simpa using hne))).bind
        intro _
        exact CacheMapCommutes.pure _ value
      · exact cacheMapCommutes_pin_ordinaryHash input query output hne

theorem cacheMapCommutes_pin_probingHashQuery
    (parameter : PublicParameter) (input query : HashInput) (output : HashOutput) (hne : query ≠ input) :
    CacheMapCommutes (pinOrdinaryEntry input output) (probingHashQuery parameter query) :=
  cacheMapCommutes_probingHashQuery _ parameter query
    (fun coordinate => cacheMapCommutes_pin_resolveKnownInput parameter input query output coordinate hne)
    (cacheMapCommutes_pin_ordinaryHash input query output hne)

theorem historyPrefix_preserves_pin
    (input : HashInput) (output : HashOutput)
    (computation : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hcommutes : CacheMapCommutes (pinOrdinaryEntry input output) computation)
    (context : DeferredContext) (fuel : Nat) (history : List Probe) (cache : SplitHashCache)
    (result : HistoryResolvedPrefix (α × SplitHashCache))
    (hcached : cache (.ordinary input) = some output)
    (hresult : some result ∈ support (runResolvedHistoryPrefix (eraseProbeQueries (computation.run cache)) context fuel history)) :
    result.value.2 (.ordinary input) = some output := by
  have hpin : pinOrdinaryEntry input output cache = cache := by
    funext key
    by_cases hkey : key = .ordinary input <;> simp_all [pinOrdinaryEntry, Function.update]
  have heq := hcommutes.historyPrefix context fuel history cache
  rw [hpin] at heq
  rw [heq, support_map] at hresult
  obtain ⟨entry, _, hentry⟩ := hresult
  cases entry with
  | none => cases hentry
  | some entry =>
      simp only [Option.map_some, Option.some.injEq] at hentry
      subst result
      simp [pinOrdinaryEntry]

theorem stableOrdinaryCacheLE_historyPrefix_probingHashQuery
    (parameter : PublicParameter) (query : HashInput)
    (context : DeferredContext) (fuel : Nat) (history : List Probe) (cache : SplitHashCache)
    (result : HistoryResolvedPrefix (HashOutput × SplitHashCache))
    (hresult : some result ∈ support (runResolvedHistoryPrefix
      (eraseProbeQueries ((probingHashQuery parameter query).run cache)) context fuel history)) :
    StableOrdinaryCacheLE parameter cache result.value.2 := by
  intro input output hstable hcached
  by_cases heq : query = input
  · subst query
    have hquery : probingHashQuery parameter input = ordinaryHashImpl input := by
      unfold probingHashQuery
      rw [hstable.1]
      cases hposition : decodePosition? parameter input with
      | none => rfl
      | some position =>
          cases position with
          | chain | leaf | node => exact (hstable.2 _ hposition (by trivial)).elim
          | ftsLeaf | ftsNode | ftsRoots => rfl
    rw [hquery] at hresult
    change some result ∈ support (runResolvedHistoryPrefix
      (eraseProbeQueries ((splitHashQuery (.ordinary input)).run cache)) context fuel history) at hresult
    rw [splitHashQuery_run_eq, hcached] at hresult
    simp only [eraseProbeQueries, construct_pure, runResolvedHistoryPrefix, mem_support_pure_iff, Option.some.injEq] at hresult
    subst result
    exact hcached
  · exact historyPrefix_preserves_pin input output _
      (cacheMapCommutes_pin_probingHashQuery parameter input query output heq) context fuel history cache result hcached hresult

end SphincsSecurity.Concrete.OtsProbeSimulation

import SphincsSecurity.Proof.OtsProbeStableHistoryCache
import SphincsSecurity.Proof.OtsProbeNativeCacheMonotone

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem ordinaryCacheMonotoneSupport_simulateQ_ordinaryRomImpl
    (computation : OracleComp OracleWorld α) :
    OrdinaryCacheMonotoneSupport (simulateQ ordinaryRomImpl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact OrdinaryCacheMonotoneSupport.pure value
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      apply OrdinaryCacheMonotoneSupport.bind _ ih
      cases input with
      | inl n =>
          exact (ordinaryCacheSupport_of_cacheMapCommutes fun _ => CacheMapCommutes.liftM _ (LazyRevealProbe.uniformQuery n)).monotone
      | inr input => exact ordinaryCacheMonotoneSupport_ordinaryHash input

attribute [local irreducible] maskedPublishedChronologicalSignAfterDigest

theorem ordinaryCacheMonotoneSupport_maskedPublishedChronologicalSign
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message) :
    OrdinaryCacheMonotoneSupport (maskedPublishedChronologicalSign parameter root ftsSecret message) := by
  unfold maskedPublishedChronologicalSign
  apply (ordinaryCacheMonotoneSupport_simulateQ_ordinaryRomImpl _).bind
  intro selected
  cases selected with
  | none => exact OrdinaryCacheMonotoneSupport.pure none
  | some selected =>
      exact ordinaryCacheMonotoneSupport_maskedPublishedChronologicalSignAfterDigest parameter ftsSecret
        selected.1 selected.2.1 selected.2.2

def StableHistoryCacheSupport (parameter : PublicParameter)
    (computation : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ context fuel history cache result,
    some result ∈ support (runResolvedHistoryPrefix (eraseProbeQueries (computation.run cache)) context fuel history) →
      StableOrdinaryCacheLE parameter cache result.value.2

theorem StableHistoryCacheSupport.of_monotone
    (parameter : PublicParameter)
    {computation : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α}
    (h : OrdinaryCacheMonotoneSupport computation) (hfree : ProbeFree computation) :
    StableHistoryCacheSupport parameter computation := by
  intro context fuel history cache result hresult
  rw [eraseProbeQueries_eq_of_probeFree _ (hfree cache)] at hresult
  exact StableOrdinaryCacheLE.of_le (h cache result.value
    (mem_support_of_historyPrefix _ context fuel history result hresult))

theorem StableHistoryCacheSupport.pure (parameter : PublicParameter) (value : α) :
    StableHistoryCacheSupport parameter (pure value : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α) :=
  StableHistoryCacheSupport.of_monotone parameter (OrdinaryCacheMonotoneSupport.pure value) (ProbeFree.pure value)

theorem StableHistoryCacheSupport.bind
    {parameter : PublicParameter}
    {left : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {next : α → StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hleft : StableHistoryCacheSupport parameter left)
    (hnext : ∀ value, StableHistoryCacheSupport parameter (next value)) :
    StableHistoryCacheSupport parameter (left >>= next) := by
  intro context fuel history cache result hresult
  rw [StateT.run_bind, eraseProbeQueries_bind, runResolvedHistoryPrefix_bind, mem_support_bind_iff] at hresult
  obtain ⟨middle, hmiddle, hrest⟩ := hresult
  cases middle with
  | none => simp at hrest
  | some middle =>
      exact (hleft context fuel history cache middle hmiddle).trans
        (hnext middle.value.1 middle.context middle.remaining middle.history middle.value.2 result hrest)

theorem stableHistoryCacheSupport_maskedChronologicalExpandedAdversaryImpl
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (input : (OracleWorld + SigningSpec).Domain) :
    StableHistoryCacheSupport parameter (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input) := by
  cases input with
  | inl world =>
      cases world with
      | inl n =>
          apply StableHistoryCacheSupport.of_monotone parameter
          · exact (ordinaryCacheSupport_of_cacheMapCommutes fun _ => CacheMapCommutes.liftM _ (LazyRevealProbe.uniformQuery n)).monotone
          · exact splitUniformImpl_probeFree n
      | inr input => exact stableOrdinaryCacheLE_historyPrefix_probingHashQuery parameter input
  | inr message =>
      exact StableHistoryCacheSupport.of_monotone parameter
        (ordinaryCacheMonotoneSupport_maskedPublishedChronologicalSign parameter root ftsSecret message)
        (maskedPublishedChronologicalSign_probeFree parameter root ftsSecret message)

theorem stableHistoryCacheSupport_nativeComputation
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    StableHistoryCacheSupport parameter
      (simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact StableHistoryCacheSupport.pure parameter value
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact (stableHistoryCacheSupport_maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).bind ih

end SphincsSecurity.Concrete.OtsProbeSimulation

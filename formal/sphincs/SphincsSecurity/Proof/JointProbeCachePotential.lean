import SphincsSecurity.Proof.FtsProbeEncodingPotential
import SphincsSecurity.Proof.JointProbeMaterializedCharge

namespace SphincsSecurity.AdaptiveRevealProbe

open _root_.OracleComp OracleSpec
variable {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]

theorem runRaw_liftProbComp
    (table : Coordinate → Digest) (state : State Coordinate) (fuel : Nat) (computation : ProbComp α) :
    runRaw table state fuel (liftProbComp computation) =
      (fun value => RawResult.done state fuel value) <$> computation := by
  have h := runRaw_liftProbComp_bind table state fuel computation pure
  simpa only [bind_pure, runRaw, construct_pure, map_eq_bind_pure_comp, Function.comp_def] using h

end SphincsSecurity.AdaptiveRevealProbe

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def jointRawCachePotential (potential : QueryCache HashSpec → ENNReal) :
    AdaptiveRevealProbe.RawResult Coordinate (Option (ResolvedRunResult (α × JointSourceCache))) → ENNReal
  | .stopped _ => 0
  | .done _ _ none => 0
  | .done _ _ (some result) => potential (ordinaryQueryCache result.value.2.2)

def JointCachePotentialBound (potential : QueryCache HashSpec → ENNReal) (source : JointSource α) : Prop :=
  ∀ table state ftsFuel context fuel otsTable cache,
    (∑' result, Pr[= result | AdaptiveRevealProbe.runRaw table state ftsFuel
      (runJointResolved (source.run cache) context fuel otsTable)] * jointRawCachePotential potential result) ≤
        potential (ordinaryQueryCache cache.2)

theorem JointCachePotentialBound.pure (potential : QueryCache HashSpec → ENNReal) (value : α) :
    JointCachePotentialBound potential (pure value) := by
  intro table state ftsFuel context fuel otsTable cache
  simp [runJointResolved, AdaptiveRevealProbe.runRaw, jointRawCachePotential]

theorem JointCachePotentialBound.bind
    {potential : QueryCache HashSpec → ENNReal} {left : JointSource α} {next : α → JointSource β}
    (hleft : JointCachePotentialBound potential left)
    (hnext : ∀ value, JointCachePotentialBound potential (next value)) :
    JointCachePotentialBound potential (left >>= next) := by
  intro table state ftsFuel context fuel otsTable cache
  rw [StateT.run_bind, runJointResolved_bind, AdaptiveRevealProbe.runRaw_bind, tsum_probOutput_bind_mul]
  apply le_trans _ (hleft table state ftsFuel context fuel otsTable cache)
  apply ENNReal.tsum_le_tsum
  intro result
  apply mul_le_mul' le_rfl
  cases result with
  | stopped hit => simp [jointRawCachePotential]
  | done finalState remaining entry =>
      cases entry with
      | none => simp [AdaptiveRevealProbe.runRaw, jointRawCachePotential]
      | some entry => exact hnext entry.value.1 table finalState remaining entry.context entry.remaining entry.table entry.value.2

theorem jointCachePotentialBound_nativeBlock
    (potential : QueryCache HashSpec → ENNReal)
    (computation : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α)
    (hbound : OtsProbeSimulation.ResolvedCachePotentialBound
      (fun cache => potential (OtsProbeSimulation.ordinaryQueryCache cache)) computation) :
    JointCachePotentialBound potential (jointSourceNativeBlock computation) := by
  intro table state ftsFuel context fuel otsTable cache
  change (∑' result, Pr[= result | AdaptiveRevealProbe.runRaw table state ftsFuel
    (runJointResolved ((fun result => (result.1, result.2, withNativeOrdinaryCache cache.2 result.2)) <$>
      jointNativeSource (computation.run (prepareNativeCache cache.2 cache.1))) context fuel otsTable)] *
        jointRawCachePotential potential result) ≤ _
  rw [runJointResolved_map, AdaptiveRevealProbe.runRaw_mapValue, tsum_probOutput_map_mul,
    runJointResolved_native, AdaptiveRevealProbe.runRaw_liftProbComp, tsum_probOutput_map_mul]
  have h := hbound context fuel otsTable (prepareNativeCache cache.2 cache.1)
  dsimp only at h
  rw [prepareNativeCache, OtsProbeSimulation.ordinaryQueryCache_replaceOrdinaryCache] at h
  apply le_trans _ h
  apply ENNReal.tsum_le_tsum
  intro result
  cases result <;> exact le_rfl

theorem jointCachePotentialBound_ftsBlock
    (potential : QueryCache HashSpec → ENNReal)
    (computation : StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) α)
    (hbound : RawCachePotentialBound (fun cache => potential (ordinaryQueryCache cache)) computation) :
    JointCachePotentialBound potential (jointSourceFtsBlock computation) := by
  intro table state ftsFuel context fuel otsTable cache
  change (∑' result, Pr[= result | AdaptiveRevealProbe.runRaw table state ftsFuel
    (runJointResolved ((fun result => (result.1, cache.1, result.2)) <$>
      jointFtsSource (computation.run cache.2)) context fuel otsTable)] * jointRawCachePotential potential result) ≤ _
  rw [runJointResolved_map, runJointResolved_fts, Functor.map_map,
    AdaptiveRevealProbe.runRaw_mapValue, tsum_probOutput_map_mul]
  apply le_trans _ (hbound table state ftsFuel cache.2)
  apply ENNReal.tsum_le_tsum
  intro result
  cases result <;> exact le_rfl

noncomputable def jointSourceUnmergedNativeBlock
    (computation : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α) :
    JointSource α := fun cache =>
  (fun result => (result.1, result.2, cache.2)) <$> jointNativeSource (computation.run cache.1)

theorem jointCachePotentialBound_unmergedNativeBlock
    (potential : QueryCache HashSpec → ENNReal)
    (computation : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α) :
    JointCachePotentialBound potential (jointSourceUnmergedNativeBlock computation) := by
  intro table state ftsFuel context fuel otsTable cache
  change (∑' result, Pr[= result | AdaptiveRevealProbe.runRaw table state ftsFuel
    (runJointResolved ((fun result => (result.1, result.2, cache.2)) <$>
      jointNativeSource (computation.run cache.1)) context fuel otsTable)] * jointRawCachePotential potential result) ≤ _
  rw [runJointResolved_map, AdaptiveRevealProbe.runRaw_mapValue, tsum_probOutput_map_mul,
    runJointResolved_native, AdaptiveRevealProbe.runRaw_liftProbComp, tsum_probOutput_map_mul]
  calc
    _ ≤ ∑' result, Pr[= result | OtsProbeSimulation.runResolvedFromTable context fuel otsTable (computation.run cache.1)] *
        potential (ordinaryQueryCache cache.2) := by
      apply ENNReal.tsum_le_tsum
      intro result
      apply mul_le_mul' le_rfl
      cases result <;> simp [jointRawCachePotential, AdaptiveRevealProbe.RawResult.mapValue]
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left bot_le tsum_probOutput_le_one

theorem jointRawCachePotential_sum {ι : Type} (indices : Finset ι)
    (potential : ι → QueryCache HashSpec → ENNReal)
    (result : AdaptiveRevealProbe.RawResult Coordinate (Option (ResolvedRunResult (α × JointSourceCache)))) :
    jointRawCachePotential (fun cache => ∑ i ∈ indices, potential i cache) result =
      ∑ i ∈ indices, jointRawCachePotential (potential i) result := by
  cases result with
  | stopped hit => simp [jointRawCachePotential]
  | done state fuel entry => cases entry <;> simp [jointRawCachePotential]

theorem JointCachePotentialBound.sum {ι : Type} (indices : Finset ι)
    (potential : ι → QueryCache HashSpec → ENNReal) (source : JointSource α)
    (hbound : ∀ i ∈ indices, JointCachePotentialBound (potential i) source) :
    JointCachePotentialBound (fun cache => ∑ i ∈ indices, potential i cache) source := by
  intro table state ftsFuel context fuel otsTable cache
  simp_rw [jointRawCachePotential_sum, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  exact Finset.sum_le_sum fun i hi => hbound i hi table state ftsFuel context fuel otsTable cache

attribute [local irreducible] JointCachePotentialBound

theorem JointCachePotentialBound.map
    {potential : QueryCache HashSpec → ENNReal} {source : JointSource α}
    (hsource : JointCachePotentialBound potential source) (f : α → β) :
    JointCachePotentialBound potential (f <$> source) := by
  rw [map_eq_bind_pure_comp]
  exact hsource.bind fun _ => JointCachePotentialBound.pure _ _

theorem jointCachePotentialBound_simulateQ {ι : Type} {spec : OracleSpec ι}
    (potential : QueryCache HashSpec → ENNReal) (impl : QueryImpl spec JointSource)
    (himpl : ∀ input, JointCachePotentialBound potential (impl input))
    (computation : OracleComp spec α) : JointCachePotentialBound potential (simulateQ impl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simpa using JointCachePotentialBound.pure potential value
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact (himpl input).bind ih

end SphincsSecurity.Concrete.FtsProbeSimulation

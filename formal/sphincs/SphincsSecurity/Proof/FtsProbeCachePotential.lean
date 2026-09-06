import SphincsSecurity.Proof.OtsProbeEncodingPotentialHash
import SphincsSecurity.Proof.FtsProbeNativeCachePreservation

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def rawCachePotential (potential : SplitHashCache → ENNReal) :
    AdaptiveRevealProbe.RawResult Coordinate (α × SplitHashCache) → ENNReal
  | .stopped _ => 0
  | .done _ _ result => potential result.2

def RawCachePotentialBound (potential : SplitHashCache → ENNReal)
    (computation : StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) α) : Prop :=
  ∀ table state fuel cache,
    (∑' result, Pr[= result | AdaptiveRevealProbe.runRaw table state fuel (computation.run cache)] *
      rawCachePotential potential result) ≤ potential cache

theorem RawCachePotentialBound.pure (potential : SplitHashCache → ENNReal) (value : α) :
    RawCachePotentialBound potential (pure value) := by
  intro table state fuel cache
  simp [AdaptiveRevealProbe.runRaw, rawCachePotential]

theorem RawCachePotentialBound.bind
    {potential : SplitHashCache → ENNReal}
    {left : StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) α}
    {next : α → StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) β}
    (hleft : RawCachePotentialBound potential left)
    (hnext : ∀ value, RawCachePotentialBound potential (next value)) :
    RawCachePotentialBound potential (left >>= next) := by
  intro table state fuel cache
  rw [StateT.run_bind, AdaptiveRevealProbe.runRaw_bind, tsum_probOutput_bind_mul]
  apply le_trans _ (hleft table state fuel cache)
  apply ENNReal.tsum_le_tsum
  intro result
  apply mul_le_mul' le_rfl
  cases result with
  | stopped hit => simp [rawCachePotential]
  | done finalState remaining result => exact hnext result.1 table finalState remaining result.2

theorem rawCachePotentialBound_lift
    (potential : SplitHashCache → ENNReal) (computation : OracleComp (AdaptiveRevealProbe.World Coordinate) α) :
    RawCachePotentialBound potential (liftM computation) := by
  intro table state fuel cache
  change (∑' result, Pr[= result | AdaptiveRevealProbe.runRaw table state fuel
    (computation >>= fun value => pure (value, cache))] * rawCachePotential potential result) ≤ _
  rw [AdaptiveRevealProbe.runRaw_bind, tsum_probOutput_bind_mul]
  calc
    _ ≤ ∑' result, Pr[= result | AdaptiveRevealProbe.runRaw table state fuel computation] * potential cache := by
      apply ENNReal.tsum_le_tsum
      intro result
      apply mul_le_mul' le_rfl
      cases result with
      | stopped hit => simp [rawCachePotential]
      | done finalState remaining result => simp [rawCachePotential, AdaptiveRevealProbe.runRaw]
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left bot_le tsum_probOutput_le_one

theorem rawCachePotentialBound_modify
    (potential : SplitHashCache → ENNReal) (update : SplitHashCache → SplitHashCache)
    (hupdate : ∀ cache, potential (update cache) ≤ potential cache) :
    RawCachePotentialBound potential (modify update) := by
  intro table state fuel cache
  simpa [AdaptiveRevealProbe.runRaw, rawCachePotential] using hupdate cache

theorem rawCachePotentialBound_simulateQ {ι : Type} {spec : OracleSpec ι}
    (potential : SplitHashCache → ENNReal)
    (impl : QueryImpl spec (StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate))))
    (himpl : ∀ input, RawCachePotentialBound potential (impl input))
    (computation : OracleComp spec α) : RawCachePotentialBound potential (simulateQ impl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simpa using RawCachePotentialBound.pure potential value
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact (himpl input).bind ih

attribute [local irreducible] RawCachePotentialBound

theorem rawCachePotentialBound_sequenceFin {n : Nat}
    (potential : SplitHashCache → ENNReal)
    (computation : Fin n → StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) α)
    (hcomponent : ∀ index, RawCachePotentialBound potential (computation index)) :
    RawCachePotentialBound potential (sequenceFin computation) := by
  induction n with
  | zero => simpa [sequenceFin] using RawCachePotentialBound.pure potential Fin.elim0
  | succ n ih =>
      rw [sequenceFin]
      exact (hcomponent 0).bind fun head =>
        (ih (fun index : Fin n => computation index.succ) (fun index => hcomponent index.succ)).bind fun tail =>
          RawCachePotentialBound.pure potential (Fin.cases head tail : Fin (n + 1) → α)

end SphincsSecurity.Concrete.FtsProbeSimulation

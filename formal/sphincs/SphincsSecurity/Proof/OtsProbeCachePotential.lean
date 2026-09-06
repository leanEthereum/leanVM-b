import SphincsSecurity.Proof.OtsProbeSourceChargeComposition
import SphincsSecurity.Proof.EncodingExhaustionProbability

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def resolvedCachePotential (potential : SplitHashCache → ENNReal) :
    Option (ResolvedRunResult (α × SplitHashCache)) → ENNReal
  | none => 0
  | some result => potential result.value.2

def ResolvedCachePotentialBound (potential : SplitHashCache → ENNReal)
    (computation : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ context fuel table cache,
    (∑' result, Pr[= result | runResolvedFromTable context fuel table (computation.run cache)] *
      resolvedCachePotential potential result) ≤ potential cache

theorem ResolvedCachePotentialBound.pure (potential : SplitHashCache → ENNReal) (value : α) :
    ResolvedCachePotentialBound potential (pure value) := by
  intro context fuel table cache
  simp [runResolvedFromTable, resolvedCachePotential]

theorem ResolvedCachePotentialBound.bind
    {potential : SplitHashCache → ENNReal}
    {left : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {next : α → StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hleft : ResolvedCachePotentialBound potential left)
    (hnext : ∀ value, ResolvedCachePotentialBound potential (next value)) :
    ResolvedCachePotentialBound potential (left >>= next) := by
  intro context fuel table cache
  rw [StateT.run_bind, runResolvedFromTable_bind, tsum_probOutput_bind_mul]
  apply le_trans _ (hleft context fuel table cache)
  apply ENNReal.tsum_le_tsum
  intro result
  apply mul_le_mul' le_rfl
  cases result with
  | none => simp [resolvedCachePotential]
  | some result => exact hnext result.value.1 result.context result.remaining result.table result.value.2

theorem resolvedCachePotentialBound_lift
    (potential : SplitHashCache → ENNReal) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    ResolvedCachePotentialBound potential (liftM computation) := by
  intro context fuel table cache
  change (∑' result, Pr[= result | runResolvedFromTable context fuel table
    (computation >>= fun value => pure (value, cache))] * resolvedCachePotential potential result) ≤ _
  rw [runResolvedFromTable_bind, tsum_probOutput_bind_mul]
  calc
    _ ≤ ∑' result, Pr[= result | runResolvedFromTable context fuel table computation] * potential cache := by
      apply ENNReal.tsum_le_tsum
      intro result
      apply mul_le_mul' le_rfl
      cases result with
      | none => simp [resolvedCachePotential]
      | some result => simp [resolvedCachePotential, runResolvedFromTable]
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left bot_le tsum_probOutput_le_one

theorem resolvedCachePotentialBound_modify
    (potential : SplitHashCache → ENNReal) (update : SplitHashCache → SplitHashCache)
    (hupdate : ∀ cache, potential (update cache) ≤ potential cache) :
    ResolvedCachePotentialBound potential (modify update) := by
  intro context fuel table cache
  simpa [runResolvedFromTable, resolvedCachePotential] using hupdate cache

theorem resolvedCachePotentialBound_get
    (potential : SplitHashCache → ENNReal) :
    ResolvedCachePotentialBound potential (get : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) SplitHashCache) := by
  intro context fuel table cache
  simp [runResolvedFromTable, resolvedCachePotential]

theorem resolvedCachePotentialBound_simulateQ {ι : Type} {spec : OracleSpec ι}
    (potential : SplitHashCache → ENNReal)
    (impl : QueryImpl spec (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (himpl : ∀ input, ResolvedCachePotentialBound potential (impl input))
    (computation : OracleComp spec α) : ResolvedCachePotentialBound potential (simulateQ impl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simpa using ResolvedCachePotentialBound.pure potential value
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact (himpl input).bind ih

attribute [local irreducible] ResolvedCachePotentialBound

theorem resolvedCachePotentialBound_sequenceFin {n : Nat}
    (potential : SplitHashCache → ENNReal)
    (computation : Fin n → StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hcomponent : ∀ index, ResolvedCachePotentialBound potential (computation index)) :
    ResolvedCachePotentialBound potential (sequenceFin computation) := by
  induction n with
  | zero => simpa [sequenceFin] using ResolvedCachePotentialBound.pure potential Fin.elim0
  | succ n ih =>
      rw [sequenceFin]
      exact (hcomponent 0).bind fun head =>
        (ih (fun index : Fin n => computation index.succ) (fun index => hcomponent index.succ)).bind fun tail =>
          ResolvedCachePotentialBound.pure potential (Fin.cases head tail : Fin (n + 1) → α)

end SphincsSecurity.Concrete.OtsProbeSimulation

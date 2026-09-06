import SphincsSecurity.Proof.EncodingCacheExtension
import SphincsSecurity.Proof.FtsProbeEncodingPotential

namespace SphincsSecurity.AdaptiveRevealProbe

open _root_.OracleComp OracleSpec
variable {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]

theorem mem_support_of_runRaw_done
    (table : Coordinate → Digest) (state finalState : State Coordinate) (fuel remaining : Nat)
    (computation : OracleComp (World Coordinate) α) (value : α)
    (hresult : RawResult.done finalState remaining value ∈ support (runRaw table state fuel computation)) :
    value ∈ support computation := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure output =>
      simp only [runRaw, construct_pure, mem_support_pure_iff, RawResult.done.injEq] at hresult
      simp [hresult.2.2]
  | query_bind input next ih =>
      rw [runRaw_bind, mem_support_bind_iff] at hresult
      obtain ⟨middle, hmiddle, hrest⟩ := hresult
      cases middle with
      | stopped hit => simp at hrest
      | done middleState middleFuel output =>
          rw [mem_support_bind_iff]
          exact ⟨output, mem_support_query input output, ih output middleState middleFuel hrest⟩

end SphincsSecurity.AdaptiveRevealProbe

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def EncodingCacheMonotoneSupport
    (computation : StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) α) : Prop :=
  ∀ cache result, result ∈ support (computation.run cache) →
    EncodingCacheExtends (ordinaryQueryCache cache) (ordinaryQueryCache result.2)

theorem EncodingCacheMonotoneSupport.pure (value : α) :
    EncodingCacheMonotoneSupport (pure value) := by
  intro cache result hresult
  simp only [StateT.run_pure, mem_support_pure_iff] at hresult
  subst result
  exact .refl _

theorem EncodingCacheMonotoneSupport.bind
    {left : StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) α}
    {next : α → StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) β}
    (hleft : EncodingCacheMonotoneSupport left) (hnext : ∀ value, EncodingCacheMonotoneSupport (next value)) :
    EncodingCacheMonotoneSupport (left >>= next) := by
  intro cache result hresult
  rw [StateT.run_bind, mem_support_bind_iff] at hresult
  obtain ⟨middle, hmiddle, hrest⟩ := hresult
  exact (hleft cache middle hmiddle).trans (hnext middle.1 middle.2 result hrest)

theorem encodingCacheMonotoneSupport_lift (computation : OracleComp (AdaptiveRevealProbe.World Coordinate) α) :
    EncodingCacheMonotoneSupport (liftM computation) := by
  intro cache result hresult
  change result ∈ support (computation >>= fun value => pure (value, cache)) at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨value, _, hresult⟩ := hresult
  simp only [mem_support_pure_iff] at hresult
  subst result
  exact .refl _

theorem encodingCacheMonotoneSupport_modify (update : SplitHashCache → SplitHashCache)
    (hupdate : ∀ cache, EncodingCacheExtends (ordinaryQueryCache cache) (ordinaryQueryCache (update cache))) :
    EncodingCacheMonotoneSupport (modify update) := by
  intro cache result hresult
  change result ∈ support (pure ((), update cache) : OracleComp (AdaptiveRevealProbe.World Coordinate) _) at hresult
  simp only [mem_support_pure_iff] at hresult
  subst result
  exact hupdate cache

theorem encodingCacheMonotoneSupport_splitHashQuery (key : SplitHashKey) :
    EncodingCacheMonotoneSupport (splitHashQuery key) := by
  intro cache result hresult
  rw [splitHashQuery_run_eq] at hresult
  cases hlookup : cache key with
  | some output =>
      simp only [hlookup, mem_support_pure_iff] at hresult
      subst result
      exact .refl _
  | none =>
      simp only [hlookup, mem_support_bind_iff, mem_support_pure_iff] at hresult
      obtain ⟨output, _, rfl⟩ := hresult
      intro parameter position message input hinput value hcached
      change cache (.ordinary input) = some value at hcached
      change Function.update cache key (some output) (.ordinary input) = some value
      by_cases heq : SplitHashKey.ordinary input = key
      · rw [heq, hlookup] at hcached
        cases hcached
      · simpa only [Function.update_of_ne heq] using hcached

theorem EncodingCacheMonotoneSupport.raw
    {computation : StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) α}
    (h : EncodingCacheMonotoneSupport computation)
    (table : Coordinate → Digest) (state finalState : AdaptiveRevealProbe.State Coordinate) (fuel remaining : Nat)
    (cache : SplitHashCache) (result : α × SplitHashCache)
    (hresult : AdaptiveRevealProbe.RawResult.done finalState remaining result ∈
      support (AdaptiveRevealProbe.runRaw table state fuel (computation.run cache))) :
    EncodingCacheExtends (ordinaryQueryCache cache) (ordinaryQueryCache result.2) :=
  h cache result (AdaptiveRevealProbe.mem_support_of_runRaw_done table state finalState fuel remaining _ result hresult)

attribute [local irreducible] EncodingCacheMonotoneSupport

theorem encodingCacheMonotoneSupport_simulateQ {ι : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate))))
    (himpl : ∀ input, EncodingCacheMonotoneSupport (impl input))
    (computation : OracleComp spec α) : EncodingCacheMonotoneSupport (simulateQ impl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simpa using EncodingCacheMonotoneSupport.pure value
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact (himpl input).bind ih

theorem encodingCacheMonotoneSupport_sequenceFin {n : Nat}
    (computation : Fin n → StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) α)
    (h : ∀ index, EncodingCacheMonotoneSupport (computation index)) :
    EncodingCacheMonotoneSupport (sequenceFin computation) := by
  induction n with
  | zero => simpa [sequenceFin] using EncodingCacheMonotoneSupport.pure Fin.elim0
  | succ n ih =>
      rw [sequenceFin]
      exact (h 0).bind fun head => (ih (fun i => computation i.succ) (fun i => h i.succ)).bind
        fun tail => EncodingCacheMonotoneSupport.pure (Fin.cases head tail : Fin (n + 1) → α)

end SphincsSecurity.Concrete.FtsProbeSimulation

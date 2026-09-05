import SphincsSecurity.Proof.OtsProbeNativeOrdinaryCacheHash
import SphincsSecurity.Proof.OuterQueryCut

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def runNativeOuterCut
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (safe : (OracleWorld + SigningSpec).Domain → DeferredContext → Prop)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    DeferredContext → Nat → (OtsSecretIndex → HashOutput) → SplitHashCache →
      ProbComp (Option (ResolvedRunResult (OuterQueryCut α × SplitHashCache))) :=
  OracleComp.construct
    (fun value context fuel table cache => pure (some ⟨context, fuel, (.done value, cache), table⟩))
    (fun input next recursivelyRun context fuel table cache =>
      if safe input context then do
        let result ← runResolvedFromTable context fuel table ((impl input).run cache)
        match result with
        | none => pure none
        | some result => recursivelyRun result.value.1 result.context result.remaining result.table result.value.2
      else pure (some ⟨context, fuel, (.query input next, cache), table⟩)) computation

theorem runNativeOuterCut_query_bind
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (safe : (OracleWorld + SigningSpec).Domain → DeferredContext → Prop)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    runNativeOuterCut impl safe (OracleSpec.query input >>= next) context fuel table cache =
      if safe input context then do
        let result ← runResolvedFromTable context fuel table ((impl input).run cache)
        match result with
        | none => pure none
        | some result => runNativeOuterCut impl safe (next result.value.1) result.context result.remaining result.table result.value.2
      else pure (some ⟨context, fuel, (.query input next, cache), table⟩) := rfl

noncomputable def resumeNativeOuterCut
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)))) :
    Option (ResolvedRunResult (OuterQueryCut α × SplitHashCache)) → ProbComp (Option (ResolvedRunResult (α × SplitHashCache)))
  | none => pure none
  | some result => runResolvedFromTable result.context result.remaining result.table
      ((simulateQ impl result.value.1.resume).run result.value.2)

theorem runNativeOuterCut_resume
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (safe : (OracleWorld + SigningSpec).Domain → DeferredContext → Prop)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    runNativeOuterCut impl safe computation context fuel table cache >>= resumeNativeOuterCut impl =
      runResolvedFromTable context fuel table ((simulateQ impl computation).run cache) := by
  induction computation using OracleComp.inductionOn generalizing context fuel table cache with
  | pure value => rfl
  | query_bind input next ih =>
      rw [runNativeOuterCut_query_bind]
      by_cases hsafe : safe input context
      · rw [if_pos hsafe, bind_assoc]
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, runResolvedFromTable_bind]
        apply bind_congr
        intro result
        cases result with
        | none => rfl
        | some result => exact ih result.value.1 result.context result.remaining result.table result.value.2
      · rw [if_neg hsafe, pure_bind]
        rfl

theorem relTriple_runNativeOuterCut_ordinaryCache
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (himpl : ∀ input, OrdinaryCacheNativeCouples (impl input))
    (safe : (OracleWorld + SigningSpec).Domain → DeferredContext → Prop)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (leftCache rightCache : SplitHashCache) (hcache : OrdinarySplitCacheEq leftCache rightCache) :
    RelTriple (runNativeOuterCut impl safe computation context fuel table leftCache)
      (runNativeOuterCut impl safe computation context fuel table rightCache) OrdinaryCacheNativeSameRel := by
  induction computation using OracleComp.inductionOn generalizing context fuel table leftCache rightCache with
  | pure value => exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hcache⟩
  | query_bind input next ih =>
      rw [runNativeOuterCut_query_bind, runNativeOuterCut_query_bind]
      by_cases hsafe : safe input context
      · rw [if_pos hsafe, if_pos hsafe]
        apply relTriple_bind (himpl input leftCache rightCache hcache context fuel table)
        intro left right hrel
        cases left with
        | none =>
            cases right with
            | none => exact relTriple_pure_pure trivial
            | some right => contradiction
        | some left =>
            cases right with
            | none => contradiction
            | some right =>
                rcases hrel with ⟨hcontext, hfuel, htable, hvalue, hcaches⟩
                simp only
                rw [← hcontext, ← hfuel, ← htable, ← hvalue]
                exact ih left.value.1 left.context left.remaining left.table left.value.2 right.value.2 hcaches
      · rw [if_neg hsafe, if_neg hsafe]
        exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hcache⟩

end SphincsSecurity.Concrete.OtsProbeSimulation

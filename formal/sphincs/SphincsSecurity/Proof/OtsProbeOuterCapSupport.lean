import SphincsSecurity.Proof.OuterHashQueryCapTrace
import SphincsSecurity.Proof.OtsProbeCanonicalTraceSupport

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem mem_support_runResolved_of_outerCap_some
    (impl : QueryImpl (OracleWorld + SigningSpec)
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (α × SplitHashCache))
    (hresult : some (⟨result.context, result.remaining, (some result.value.1, result.value.2), result.table⟩ :
        ResolvedRunResult (Option α × SplitHashCache)) ∈ support (runResolvedFromTable context fuel table
          ((simulateQ impl (capOuterHashQueries computation q)).run cache))) :
    some result ∈ support (runResolvedFromTable context fuel table ((simulateQ impl computation).run cache)) := by
  induction computation using OracleComp.inductionOn generalizing q context fuel table cache with
  | pure value =>
      simp only [capOuterHashQueries_pure, simulateQ_pure, StateT.run_pure,
        runResolvedFromTable, construct_pure, mem_support_pure_iff, Option.some.injEq,
        ResolvedRunResult.mk.injEq, Prod.mk.injEq, Option.some.injEq] at hresult
      rcases result with ⟨finalContext, remaining, ⟨returned, finalCache⟩, finalTable⟩
      rcases hresult with ⟨rfl, rfl, ⟨rfl, rfl⟩, rfl⟩
      simp [simulateQ_pure, runResolvedFromTable]
  | query_bind input next ih =>
      rw [capOuterHashQueries_query_bind] at hresult
      by_cases hh : IsOuterHash input
      · rw [if_pos hh] at hresult
        cases q with
        | zero => simp [simulateQ_pure, runResolvedFromTable] at hresult
        | succ q =>
            rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, runResolvedFromTable_bind,
              mem_support_bind_iff] at hresult ⊢
            obtain ⟨middle, hm, ht⟩ := hresult
            cases middle with
            | none => simp at ht
            | some middle =>
                exact ⟨some middle, hm, ih middle.value.1 q middle.context middle.remaining middle.table middle.value.2 ht⟩
      · rw [if_neg hh] at hresult
        rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, runResolvedFromTable_bind,
          mem_support_bind_iff] at hresult ⊢
        obtain ⟨middle, hm, ht⟩ := hresult
        cases middle with
        | none => simp at ht
        | some middle =>
            exact ⟨some middle, hm, ih middle.value.1 q middle.context middle.remaining middle.table middle.value.2 ht⟩

end SphincsSecurity.Concrete.OtsProbeSimulation

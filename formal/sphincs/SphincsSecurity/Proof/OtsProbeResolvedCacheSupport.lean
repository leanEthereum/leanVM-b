import SphincsSecurity.Proof.OtsProbeNativeCacheMonotone

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

theorem mem_support_of_runResolvedFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (result : ResolvedRunResult α)
    (hresult : some result ∈ support (runResolvedFromTable context fuel table computation)) :
    result.value ∈ support computation := by
  induction computation using OracleComp.inductionOn generalizing context fuel table with
  | pure value =>
      simp only [runResolvedFromTable, construct_pure, mem_support_pure_iff, Option.some.injEq] at hresult
      subst result
      simp
  | query_bind input next ih =>
      rw [runResolvedFromTable_bind, mem_support_bind_iff] at hresult
      obtain ⟨middleOption, hmiddle, hrest⟩ := hresult
      cases middleOption with
      | none => simp at hrest
      | some middle =>
          rw [mem_support_bind_iff]
          exact ⟨middle.value, mem_support_query input middle.value,
            ih middle.value middle.context middle.remaining middle.table hrest⟩

theorem OrdinaryCacheMonotoneSupport.resolved
    {computation : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α}
    (h : OrdinaryCacheMonotoneSupport computation)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (α × SplitHashCache))
    (hresult : some result ∈ support (runResolvedFromTable context fuel table (computation.run cache))) :
    ordinaryQueryCache cache ≤ ordinaryQueryCache result.value.2 :=
  h cache result.value (mem_support_of_runResolvedFromTable _ context fuel table result hresult)

theorem OrdinaryCacheSupport.resolved
    {computation : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α}
    (h : OrdinaryCacheSupport computation)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (α × SplitHashCache))
    (hresult : some result ∈ support (runResolvedFromTable context fuel table (computation.run cache))) :
    ordinaryQueryCache result.value.2 = ordinaryQueryCache cache :=
  h cache result.value (mem_support_of_runResolvedFromTable _ context fuel table result hresult)

end SphincsSecurity.Concrete.OtsProbeSimulation

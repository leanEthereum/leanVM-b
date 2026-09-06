import SphincsSecurity.Proof.JointProbeQueryPublicationInvariant

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] runJointResolved AdaptiveRevealProbe.runRaw OtsProbeSimulation.runResolvedFromTable
attribute [local irreducible] OtsProbeSimulation.maskedPublishedTreeRoot jointSourceOuterQuery
set_option backward.isDefEq.respectTransparency false

theorem jointPublicationInvariant_of_mem_computation
    (parameter : PublicParameter) (root : Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (table : Coordinate → Digest) (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel remaining : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (entry : ResolvedRunResult (α × JointSourceCache)) (hinvariant : JointPublicationInvariant context cache)
    (hresult : .done finalState remaining (some entry) ∈ support (AdaptiveRevealProbe.runRaw table state ftsFuel
      (runJointResolved ((jointSourceComputation parameter root computation).run cache) context fuel otsTable))) :
    JointPublicationInvariant entry.context entry.value.2 := by
  induction computation using OracleComp.inductionOn generalizing state ftsFuel context fuel otsTable cache with
  | pure value =>
      change .done finalState remaining (some entry) ∈ support (AdaptiveRevealProbe.runRaw table state ftsFuel
        (runJointResolved ((jointSourceNativeBlock (pure value)).run cache) context fuel otsTable)) at hresult
      obtain ⟨native, hnative, _, _, rfl⟩ := mem_support_jointSourceNativeBlock_raw_done
        table state finalState ftsFuel remaining _ context fuel otsTable cache entry hresult
      simp only [StateT.run_pure, OtsProbeSimulation.runResolvedFromTable, construct_pure,
        mem_support_pure_iff, Option.some.injEq] at hnative
      subst native
      change JointPublicationInvariant context
        (prepareNativeCache cache.2 cache.1, withNativeOrdinaryCache cache.2 (prepareNativeCache cache.2 cache.1))
      rw [withNativeOrdinaryCache_prepare]
      exact hinvariant
  | query_bind input next ih =>
      change .done finalState remaining (some entry) ∈ support (AdaptiveRevealProbe.runRaw table state ftsFuel
        (runJointResolved ((jointSourceOuterQuery parameter root input >>= fun value => jointSourceComputation parameter root (next value)).run cache)
          context fuel otsTable)) at hresult
      obtain ⟨middleState, middleFuel, middle, hmiddle, hrest⟩ := mem_support_jointSource_bind_raw_done
        table state finalState ftsFuel remaining _ _ context fuel otsTable cache entry hresult
      exact ih middle.value.1 middleState middleFuel middle.context middle.remaining middle.table middle.value.2
        (jointPublicationInvariant_of_mem_outerQuery parameter root input table state middleState ftsFuel middleFuel
          context fuel otsTable cache middle hinvariant hmiddle) hrest

theorem jointPublicationInvariant_of_mem_retained
    (adversary : Adversary) (parameter : PublicParameter) (q : Nat) (targets : Finset Position)
    (table : Coordinate → Digest) (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel remaining : Nat)
    (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput)
    (entry : ResolvedRunResult (Option RetainedGameResult × JointSourceCache))
    (hresult : .done finalState remaining (some entry) ∈ support (AdaptiveRevealProbe.runRaw table state ftsFuel
      (runJointResolved ((jointSourceRetained adversary parameter q).run (OtsProbeSimulation.emptySplitHashCache, emptySplitHashCache))
        (OtsProbeSimulation.ensuredInitialContext targets) fuel otsTable))) :
    JointPublicationInvariant entry.context entry.value.2 := by
  rw [jointSourceRetained] at hresult
  obtain ⟨middleState, middleFuel, middle, hmiddle, hrest⟩ := mem_support_jointSource_bind_raw_done
    table state finalState ftsFuel remaining _ _ (OtsProbeSimulation.ensuredInitialContext targets) fuel otsTable _ entry hresult
  obtain ⟨native, hnative, _, _, rfl⟩ := mem_support_jointSourceNativeBlock_raw_done
    table state middleState ftsFuel middleFuel _ (OtsProbeSimulation.ensuredInitialContext targets) fuel otsTable _ middle hmiddle
  have hempty : prepareNativeCache emptySplitHashCache OtsProbeSimulation.emptySplitHashCache = OtsProbeSimulation.emptySplitHashCache := by
    funext key
    cases key <;> rfl
  dsimp only at hnative
  rw [hempty] at hnative
  exact jointPublicationInvariant_of_mem_computation parameter native.value.1 _ table middleState finalState middleFuel remaining
    native.context native.remaining native.table (native.value.2, withNativeOrdinaryCache emptySplitHashCache native.value.2) entry
    (Or.inl (OtsProbeSimulation.materializedChainsPublished_of_mem_initializedRoot targets fuel otsTable native hnative)) hrest

end SphincsSecurity.Concrete.FtsProbeSimulation

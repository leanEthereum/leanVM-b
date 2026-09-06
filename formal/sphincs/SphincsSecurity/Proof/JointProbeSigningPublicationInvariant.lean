import SphincsSecurity.Proof.JointProbeSigningChainPublication
import SphincsSecurity.Proof.JointProbeSigningEncodingFailure
import SphincsSecurity.Proof.JointProbeMaterializedPotential

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex MaterializedChainsPublished)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] runJointResolved AdaptiveRevealProbe.runRaw OtsProbeSimulation.runResolvedFromTable
attribute [local irreducible] jointSourceSignAfterDigest
set_option backward.isDefEq.respectTransparency false

theorem jointPublicationInvariant_of_mem_signAfterDigest
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (table : Coordinate → Digest) (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel remaining : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (entry : ResolvedRunResult (Option Signature × JointSourceCache)) (hinvariant : JointPublicationInvariant context cache)
    (hresult : .done finalState remaining (some entry) ∈ support (AdaptiveRevealProbe.runRaw table state ftsFuel
      (runJointResolved ((jointSourceSignAfterDigest parameter randomness index leaves).run cache) context fuel otsTable))) :
    JointPublicationInvariant entry.context entry.value.2 := by
  rcases hinvariant with hpublic | hexhausted
  · by_cases hfailed : entry.value.1 = none
    · exact Or.inr (anyEncodingInputsExhausted_of_mem_failed_jointSignAfterDigest parameter randomness index leaves
        table state finalState ftsFuel remaining context fuel otsTable cache entry hresult hfailed)
    · exact Or.inl (materializedChainsPublished_of_successful_jointSignAfterDigest parameter randomness index leaves
        table state finalState ftsFuel remaining context fuel otsTable cache entry hpublic hresult hfailed)
  · exact Or.inr ((jointEncodingCacheMonotone_signAfterDigest parameter randomness index leaves
      table state ftsFuel context fuel otsTable cache finalState remaining entry hresult).exhausted hexhausted)

theorem jointPublicationInvariant_of_mem_sign
    (parameter : PublicParameter) (root : Digest) (message : Message)
    (table : Coordinate → Digest) (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel remaining : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (entry : ResolvedRunResult (Option Signature × JointSourceCache)) (hinvariant : JointPublicationInvariant context cache)
    (hresult : .done finalState remaining (some entry) ∈ support (AdaptiveRevealProbe.runRaw table state ftsFuel
      (runJointResolved ((jointSourceSign parameter root message).run cache) context fuel otsTable))) :
    JointPublicationInvariant entry.context entry.value.2 := by
  rcases hinvariant with hpublic | hexhausted
  · rw [jointSourceSign] at hresult
    obtain ⟨middleState, middleFuel, middle, hmiddle, hrest⟩ := mem_support_jointSource_bind_raw_done
      table state finalState ftsFuel remaining _ _ context fuel otsTable cache entry hresult
    obtain ⟨native, hnative, _, _, rfl⟩ := mem_support_jointSourceNativeBlock_raw_done
      table state middleState ftsFuel middleFuel _ context fuel otsTable cache middle hmiddle
    have hpublished : MaterializedChainsPublished native.context := by
      intro coordinate hchain hknown
      have hpreserved := OtsProbeSimulation.resolvedPreservesCoordinate_simulateQ_ordinaryRomImpl coordinate _
        context fuel otsTable (prepareNativeCache cache.2 cache.1) native hnative
      exact hpreserved.2.mpr (hpublic coordinate hchain (by rwa [hpreserved.1] at hknown))
    dsimp only [packResolvedNativeBlock] at hrest
    cases hselected : native.value.1 with
    | none =>
        simp only [hselected] at hrest
        obtain ⟨returned, hreturned, _, _, rfl⟩ := mem_support_jointSourceNativeBlock_raw_done
          table middleState finalState middleFuel remaining _ native.context native.remaining native.table
          (native.value.2, withNativeOrdinaryCache cache.2 native.value.2) entry hrest
        simp only [StateT.run_pure, OtsProbeSimulation.runResolvedFromTable, construct_pure,
          mem_support_pure_iff, Option.some.injEq] at hreturned
        subst returned
        exact Or.inl hpublished
    | some selected =>
        simp only [hselected] at hrest
        exact jointPublicationInvariant_of_mem_signAfterDigest parameter selected.1 selected.2.1 selected.2.2
          table middleState finalState middleFuel remaining native.context native.remaining native.table
          (native.value.2, withNativeOrdinaryCache cache.2 native.value.2) entry (Or.inl hpublished) hrest
  · exact Or.inr ((jointEncodingCacheMonotone_sign parameter root message
      table state ftsFuel context fuel otsTable cache finalState remaining entry hresult).exhausted hexhausted)

end SphincsSecurity.Concrete.FtsProbeSimulation

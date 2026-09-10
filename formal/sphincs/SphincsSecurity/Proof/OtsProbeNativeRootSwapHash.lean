import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeNativeRootEncodingHash
import SphincsSecurity.Proof.OtsProbeNativeRootHashPlan
import SphincsSecurity.Proof.OtsProbeNativeRootSwap

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

theorem relTriple_nativeRootSwap_probingHashQuery
    (parameter : PublicParameter) (target : Position) (before after : HashOutput) (input : HashInput)
    (left right : DeferredContext) (hcontext : NativeRootContextRel target before after left right)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (leftCache rightCache : SplitHashCache)
    (hcache : NativeRootSwapCacheRel parameter target before after leftCache rightCache)
    (havoid : RootInputAvoids parameter target (truncateHash before) (truncateHash after) input)
    (hprobe : ∀ candidate, (purePlanProbingHashQuery parameter input left.state).candidate? = some candidate →
      ¬IsPrivateValueExposure target before after (.probe candidate.coordinate candidate.candidate))
    (haction : NativeRootActionSafe parameter target input left right
      (purePlanProbingHashQuery parameter input left.state).action) :
    RelTriple
      (runResolvedFromTable left fuel table ((probingHashQuery parameter input).run leftCache))
      (runResolvedFromTable right fuel table ((probingHashQuery parameter input).run rightCache))
      (NativeRootSwapSameRel parameter target before after) := by
  obtain ⟨middleCache, hencoding, hhidden⟩ := hcache
  have hfirst := rootEncodingNativeCouples_probingHashQuery_avoids parameter target
    (truncateHash before) (truncateHash after) input havoid leftCache middleCache hencoding left fuel table
  have hsecond := relTriple_nativeRoot_probingHashQuery_of_safe parameter target before after input
    left right hcontext fuel table middleCache rightCache hhidden hprobe haction
  apply relTriple_post_mono (SphincsSecurity.relTriple_trans_exists hfirst hsecond)
  intro leftResult rightResult hrel
  obtain ⟨middleResult, hfirst, hsecond⟩ := hrel
  cases leftResult with
  | none =>
      cases middleResult with
      | some middleResult => contradiction
      | none =>
          cases rightResult with
          | none => trivial
          | some rightResult => contradiction
  | some leftResult =>
      cases middleResult with
      | none => contradiction
      | some middleResult =>
          cases rightResult with
          | none => contradiction
          | some rightResult =>
              rcases hfirst with ⟨hcontextEq, hfuel₁, htable₁, hvalue₁, hcache₁⟩
              rcases hsecond with ⟨hcontext₂, hfuel₂, htable₂, hvalue₂, hcache₂⟩
              refine ⟨?_, hfuel₁.trans hfuel₂, htable₁.trans htable₂, hvalue₁.trans hvalue₂,
                middleResult.value.2, hcache₁, hcache₂⟩
              rw [hcontextEq]
              exact hcontext₂

end SphincsSecurity.Concrete.OtsProbeSimulation

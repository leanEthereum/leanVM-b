import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeNativeRootSwapHash

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

theorem nativeRootSwapSameRel_of_middle
    {parameter : PublicParameter} {target : Position} {before after : HashOutput}
    {left middle right : Option (ResolvedRunResult (α × SplitHashCache))}
    (hfirst : RootEncodingNativeSameRel parameter target (truncateHash before) (truncateHash after) left middle)
    (hsecond : NativeRootSameRel target before after middle right) :
    NativeRootSwapSameRel parameter target before after left right := by
  cases left with
  | none =>
      cases middle with
      | some middle => contradiction
      | none =>
          cases right with
          | none => trivial
          | some right => contradiction
  | some left =>
      cases middle with
      | none => contradiction
      | some middle =>
          cases right with
          | none => contradiction
          | some right =>
              rcases hfirst with ⟨hcontextEq, hfuel₁, htable₁, hvalue₁, hcache₁⟩
              rcases hsecond with ⟨hcontext₂, hfuel₂, htable₂, hvalue₂, hcache₂⟩
              refine ⟨?_, hfuel₁.trans hfuel₂, htable₁.trans htable₂, hvalue₁.trans hvalue₂,
                middle.value.2, hcache₁, hcache₂⟩
              rw [hcontextEq]
              exact hcontext₂

theorem relTriple_nativeRootSwap_uniform
    (parameter : PublicParameter) (target : Position) (before after : HashOutput) (n : Nat)
    (left right : DeferredContext) (hcontext : NativeRootContextRel target before after left right)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (leftCache rightCache : SplitHashCache)
    (hcache : NativeRootSwapCacheRel parameter target before after leftCache rightCache) :
    RelTriple
      (runResolvedFromTable left fuel table ((splitUniformImpl n).run leftCache))
      (runResolvedFromTable right fuel table ((splitUniformImpl n).run rightCache))
      (NativeRootSwapSameRel parameter target before after) := by
  obtain ⟨middleCache, hencoding, hhidden⟩ := hcache
  have hfirst := rootEncodingNativeCouples_splitUniformImpl parameter target
    (truncateHash before) (truncateHash after) n leftCache middleCache hencoding left fuel table
  have hsecond := nativeRootRelates_splitUniformImpl target before after n
    left right hcontext fuel table middleCache rightCache hhidden
  apply relTriple_post_mono (SphincsSecurity.relTriple_trans_exists hfirst hsecond)
  rintro _ _ ⟨_, hfirst, hsecond⟩
  exact nativeRootSwapSameRel_of_middle hfirst hsecond

theorem NativePositionReplaceable.replace_self
    {target : Position} {before after : HashOutput} {context : DeferredContext}
    (h : NativePositionReplaceable target before after context) : replaceNativePosition target before context = context := by
  have hinverse := replaceNativePosition_inverse h
  rwa [replaceNativePosition_idem] at hinverse

def NativeRootHashSafe (parameter : PublicParameter) (target : Position) (before after : HashOutput)
    (input : HashInput) (context : DeferredContext) : Prop :=
  let left := replaceNativePosition target before context
  let right := replaceNativePosition target after context
  RootInputAvoids parameter target (truncateHash before) (truncateHash after) input ∧
    (∀ candidate, (purePlanProbingHashQuery parameter input left.state).candidate? = some candidate →
      ¬IsPrivateValueExposure target before after (.probe candidate.coordinate candidate.candidate)) ∧
    NativeRootActionSafe parameter target input left right (purePlanProbingHashQuery parameter input left.state).action

def NativeRootOuterSafe (parameter : PublicParameter) (target : Position) (before after : HashOutput) :
    (OracleWorld + SigningSpec).Domain → DeferredContext → Prop
  | .inl (.inr input), context => NativeRootHashSafe parameter target before after input context
  | _, _ => True

theorem relTriple_nativeRootSwap_outerQuery_of_safe
    (parameter : PublicParameter) (root : Digest) (target : Position) (hroot : IsLayerRoot target)
    (before after : HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (left right : DeferredContext) (hcontext : NativeRootContextRel target before after left right)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (leftCache rightCache : SplitHashCache)
    (hcache : NativeRootSwapCacheRel parameter target before after leftCache rightCache)
    (hsafe : NativeRootOuterSafe parameter target before after input left) :
    RelTriple
      (runResolvedFromTable left fuel table ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run leftCache))
      (runResolvedFromTable right fuel table ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run rightCache))
      (NativeRootSwapSameRel parameter target before after) := by
  cases input with
  | inl input =>
      cases input with
      | inl n =>
          exact relTriple_nativeRootSwap_uniform parameter target before after n
            left right hcontext fuel table leftCache rightCache hcache
      | inr input =>
          change NativeRootHashSafe parameter target before after input left at hsafe
          simp only [NativeRootHashSafe, hcontext.replaceable.replace_self, ← hcontext.right_eq] at hsafe
          exact relTriple_nativeRootSwap_probingHashQuery parameter target before after input
            left right hcontext fuel table leftCache rightCache hcache hsafe.1 hsafe.2.1 hsafe.2.2
  | inr message =>
      exact relTriple_nativeRootSwap_chronologicalSign parameter root target hroot before after ftsSecret message
        left right hcontext fuel table leftCache rightCache hcache

end SphincsSecurity.Concrete.OtsProbeSimulation

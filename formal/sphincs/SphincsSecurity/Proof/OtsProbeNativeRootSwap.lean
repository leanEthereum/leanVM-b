import SphincsSecurity.Proof.OtsProbeNativeRootStateChronological

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def NativeRootSwapCacheRel (parameter : PublicParameter) (target : Position)
    (before after : HashOutput) (left right : SplitHashCache) : Prop :=
  ∃ middle, RootEncodingCacheRel parameter target (truncateHash before) (truncateHash after) left middle ∧
    RootHiddenCacheRel target before after middle right

def NativeRootSwapSameRel (parameter : PublicParameter) (target : Position) (before after : HashOutput) :
    Option (ResolvedRunResult (α × SplitHashCache)) →
      Option (ResolvedRunResult (α × SplitHashCache)) → Prop
  | some left, some right =>
      NativeRootContextRel target before after left.context right.context ∧
        left.remaining = right.remaining ∧ left.table = right.table ∧ left.value.1 = right.value.1 ∧
        NativeRootSwapCacheRel parameter target before after left.value.2 right.value.2
  | none, none => True
  | _, _ => False

theorem nativeRootSwapCacheRel_fullSwap
    (parameter : PublicParameter) (target : Position) (before after : HashOutput)
    (cache : SplitHashCache) (hcache : cache (.hidden (.position target)) = some before) :
    NativeRootSwapCacheRel parameter target before after cache
      (fullSwapRootCache parameter target (truncateHash before) (truncateHash after) after cache) :=
  ⟨swapCanonicalRootEncodingCache parameter target (truncateHash before) (truncateHash after) cache,
    rootEncodingCacheRel_swapCanonical parameter target (truncateHash before) (truncateHash after) cache,
    rootHiddenCacheRel_fullSwapRootCache parameter target before after cache hcache⟩

theorem relTriple_nativeRootSwap_chronologicalSign
    (parameter : PublicParameter) (root : Digest) (target : Position) (hroot : IsLayerRoot target)
    (before after : HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message)
    (left right : DeferredContext) (hcontext : NativeRootContextRel target before after left right)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (leftCache rightCache : SplitHashCache)
    (hcache : NativeRootSwapCacheRel parameter target before after leftCache rightCache) :
    RelTriple
      (runResolvedFromTable left fuel table ((maskedPublishedChronologicalSign parameter root ftsSecret message).run leftCache))
      (runResolvedFromTable right fuel table ((maskedPublishedChronologicalSign parameter root ftsSecret message).run rightCache))
      (NativeRootSwapSameRel parameter target before after) := by
  obtain ⟨middleCache, hencoding, hhidden⟩ := hcache
  have hfirst := rootEncodingNativeRelatesStored_maskedPublishedChronologicalSign_targetComparison
    parameter root target hroot (truncateHash before) (truncateHash after) ftsSecret message
    leftCache middleCache hencoding left fuel table ⟨before, hcontext.replaceable.known, rfl⟩
  have hsecond := nativeRootRelates_chronologicalSign_comparison_actual parameter root target hroot
    before after ftsSecret message left right hcontext fuel table middleCache rightCache hhidden
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
              rcases hfirst.1 with ⟨hcontextEq, hfuel₁, htable₁, hvalue₁, hcache₁⟩
              rcases hsecond with ⟨hcontext₂, hfuel₂, htable₂, hvalue₂, hcache₂⟩
              refine ⟨?_, hfuel₁.trans hfuel₂, htable₁.trans htable₂, hvalue₁.trans hvalue₂,
                middleResult.value.2, hcache₁, hcache₂⟩
              rw [hcontextEq]
              exact hcontext₂

def normalizeNativeRootResult (target : Position) (result : Option (ResolvedRunResult (α × SplitHashCache))) :
    Option (ResolvedRunResult α) :=
  result.map fun result => ⟨replaceNativePosition target 0 result.context, result.remaining, result.value.1, result.table⟩

noncomputable def normalizeLiveNativeRootResult (target : Position) :
    Option (ResolvedRunResult (α × SplitHashCache)) → Option (ResolvedRunResult α)
  | none => none
  | some result =>
      if DeferredCompletable result.table result.context then normalizeNativeRootResult target (some result) else none

theorem NativeRootContextRel.completable_iff
    {target : Position} {before after : HashOutput} {left right : DeferredContext}
    (h : NativeRootContextRel target before after left right) (table : OtsSecretIndex → HashOutput) :
    DeferredCompletable table right ↔ DeferredCompletable table left := by
  rw [h.right_eq]
  exact deferredCompletable_replaceNativePosition_iff target before after left table h.replaceable

theorem NativeRootSwapSameRel.normalize
    {parameter : PublicParameter} {target : Position} {before after : HashOutput}
    {left right : Option (ResolvedRunResult (α × SplitHashCache))}
    (h : NativeRootSwapSameRel parameter target before after left right) :
    normalizeNativeRootResult target left = normalizeNativeRootResult target right := by
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some right => contradiction
  | some left =>
      cases right with
      | none => contradiction
      | some right =>
          rcases h with ⟨hcontext, hfuel, htable, hvalue, _⟩
          simp only [normalizeNativeRootResult, Option.map_some, hcontext.right_eq,
            replaceNativePosition_idem, hfuel, htable, hvalue]

theorem NativeRootSwapSameRel.normalizeLive
    {parameter : PublicParameter} {target : Position} {before after : HashOutput}
    {left right : Option (ResolvedRunResult (α × SplitHashCache))}
    (h : NativeRootSwapSameRel parameter target before after left right) :
    normalizeLiveNativeRootResult target left = normalizeLiveNativeRootResult target right := by
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some right => contradiction
  | some left =>
      cases right with
      | none => contradiction
      | some right =>
          have hnormalize := h.normalize
          rcases h with ⟨hcontext, _, htable, _, _⟩
          simp only [normalizeLiveNativeRootResult, ← htable, hcontext.completable_iff,
            hnormalize]

theorem evalDist_nativeRootSwap_chronologicalSign_live
    (parameter : PublicParameter) (root : Digest) (target : Position) (hroot : IsLayerRoot target)
    (before after : HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message)
    (context : DeferredContext) (h : NativePositionReplaceable target before after context)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hcache : cache (.hidden (.position target)) = some before) :
    evalDist (normalizeLiveNativeRootResult target <$>
      runResolvedFromTable context fuel table ((maskedPublishedChronologicalSign parameter root ftsSecret message).run cache)) =
    evalDist (normalizeLiveNativeRootResult target <$>
      runResolvedFromTable (replaceNativePosition target after context) fuel table
        ((maskedPublishedChronologicalSign parameter root ftsSecret message).run
          (fullSwapRootCache parameter target (truncateHash before) (truncateHash after) after cache))) := by
  apply evalDist_map_eq_of_relTriple
  apply relTriple_post_mono
    (relTriple_nativeRootSwap_chronologicalSign parameter root target hroot before after ftsSecret message
      context (replaceNativePosition target after context) ⟨h, rfl⟩ fuel table cache
      (fullSwapRootCache parameter target (truncateHash before) (truncateHash after) after cache)
      (nativeRootSwapCacheRel_fullSwap parameter target before after cache hcache))
  intro left right hrel
  exact hrel.normalizeLive

end SphincsSecurity.Concrete.OtsProbeSimulation

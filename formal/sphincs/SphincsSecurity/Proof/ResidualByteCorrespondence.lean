import SphincsSecurity.Proof.ResidualByteExecution
import SphincsSecurity.Proof.CanonicalProbeExecution

namespace SphincsSecurity.Concrete.ResidualByteFrontend

open _root_.OracleComp OracleSpec CanonicalProbeRouting HiddenLabelObservation ResidualByteAction
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

def CacheMatches (oracle : HashInput → HashOutput) (cache : ExternalCache) : Prop :=
  ∀ input answer, cache input = some answer → answer = oracle input

theorem cacheMatches_empty (oracle : HashInput → HashOutput) : CacheMatches oracle (fun _ => none) := by
  intro input answer hcache
  cases hcache

theorem cacheMatches_store (oracle : HashInput → HashOutput) (cache : ExternalCache)
    (hmatches : CacheMatches oracle cache) (input : HashInput) :
    CacheMatches oracle (Function.update cache input (some (oracle input))) := by
  intro other answer hcache
  by_cases heq : other = input
  · subst other
    rw [Function.update_self] at hcache
    exact (Option.some.inj hcache).symm
  · rw [Function.update_of_ne heq] at hcache
    exact hmatches other answer hcache

noncomputable def fixedAnswer (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (actual : Labels)
    (oracle : HashInput → HashOutput) (input : HashInput) : Option HashOutput :=
  if CanonicalProbeRouting.Bad parameter words disclosed actual input (oracle input) then none else some (oracle input)

noncomputable def fixedStep (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known actual : Labels)
    (oracle : HashInput → HashOutput) (input : HashInput) (memory : ExternalMemory) : Option HashOutput × ExternalMemory :=
  let paid := charge parameter words disclosed known input memory
  let answer := fixedAnswer parameter words disclosed actual oracle input
  (answer, answer.elim paid (fun answer => storeReply paid input answer))

theorem fixedStep_preserves (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known actual : Labels)
    (oracle : HashInput → HashOutput) (input : HashInput) (memory : ExternalMemory)
    (hmatches : CacheMatches oracle memory.cache) (hclean : CacheClean parameter words disclosed actual memory.cache) :
    let after := (fixedStep parameter words disclosed known actual oracle input memory).2
    CacheMatches oracle after.cache ∧ CacheClean parameter words disclosed actual after.cache ∧
      after.hashCalls = memory.hashCalls + 1 := by
  unfold fixedStep fixedAnswer
  split
  · exact ⟨hmatches, hclean, rfl⟩
  · rename_i hsafe
    exact ⟨cacheMatches_store oracle memory.cache hmatches input,
      cacheClean_store parameter words disclosed actual memory.cache hclean input (oracle input) hsafe, rfl⟩

theorem fixedStep_hashCalls (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known actual : Labels)
    (oracle : HashInput → HashOutput) (input : HashInput) (memory : ExternalMemory) :
    (fixedStep parameter words disclosed known actual oracle input memory).2.hashCalls = memory.hashCalls + 1 := by
  unfold fixedStep
  cases fixedAnswer parameter words disclosed actual oracle input <;> rfl

theorem fixedExternalRun_hashCalls_le {Result : Type} (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known actual : Labels)
    (oracle : HashInput → HashOutput) (computation : OracleComp OracleWorld Result) (memory : ExternalMemory)
    (budget : Nat) (hbound : computation.IsQueryBoundP IsHashQuery budget)
    (result : Option Result × ExternalMemory)
    (hresult : externalRun (fun input memory => pure (fixedStep parameter words disclosed known actual oracle input memory))
      computation memory result ≠ 0) : result.2.hashCalls ≤ memory.hashCalls + budget := by
  apply externalRun_hashCalls_le _ (fun _ => True) _ computation memory trivial budget hbound result hresult
  intro input memory _ result hresult
  simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
  subst result
  exact ⟨trivial, fixedStep_hashCalls parameter words disclosed known actual oracle input memory⟩

variable (parameter : PublicParameter) (inputs : Finset HashInput) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels) (actions : inputs → Action inputs)

theorem publicCachedReply_eq_fixed (actual : Labels) (seed : inputs → HashOutput)
    (oracle : HashInput → HashOutput) (input : inputs) (memory : ExternalMemory)
    (hmatches : CacheMatches oracle memory.cache) (hclean : CacheClean parameter words disclosed actual memory.cache)
    (hfresh : ResidualByteAction.eval actual seed
      (actions input) =
        fixedAnswer parameter words disclosed actual oracle input.val) :
    publicCachedReply inputs actions actual seed input memory =
      fixedAnswer parameter words disclosed actual oracle input.val := by
  cases hcache : memory.cache input.val with
  | none => simpa only [publicCachedReply, hcache, Option.elim_none] using hfresh
  | some answer =>
      have hsafe := hclean input.val answer hcache
      have heq := hmatches input.val answer hcache
      rw [heq] at hsafe
      simp only [publicCachedReply, hcache, Option.elim_some, fixedAnswer, if_neg hsafe, heq]

theorem hashQueryResult_eq_fixed (actual : Labels) (seed : inputs → HashOutput)
    (oracle : HashInput → HashOutput) (input : inputs) (state : State inputs)
    (hcovered : RowsCovered inputs state) (hlocal : Local input (actions input)) (hmatches : CacheMatches oracle state.memory.cache)
    (hclean : CacheClean parameter words disclosed actual state.memory.cache)
    (hfresh : ResidualByteAction.eval actual seed
      (actions input) =
        fixedAnswer parameter words disclosed actual oracle input.val) :
    let result := hashQueryResult parameter inputs words disclosed known actions actual seed input state
    (result.1, result.2.memory) = fixedStep parameter words disclosed known actual oracle input.val state.memory := by
  dsimp only
  rw [hashQueryResult_project parameter inputs words disclosed known actions actual seed input state hcovered hlocal,
    publicCachedReply_eq_fixed parameter inputs words disclosed actions actual seed
      oracle input state.memory hmatches hclean hfresh]
  rfl

theorem hashQueryResult_eq_original (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels) (publicReplies : CanonicalGraphLabels)
    (rows : CanonicalEncodingRows)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (replies : CanonicalGraphLabels)
    (hagrees : PublicAgreement words disclosed known (CanonicalCoordinate.value otsSecret ftsSecret replies))
    (hreplies : ∀ position, ¬CanonicalCoordinate.Hidden words disclosed (.graph position) → publicReplies position = replies position)
    (seed : inputs → HashOutput) (input : inputs) (state : State inputs)
    (hcovered : RowsCovered inputs state)
    (hmatches : CacheMatches (programmedHash parameter otsSecret ftsSecret replies
      (finiteHashAnswer ∅ inputs (canonicalReferenceResidual parameter inputs hencoding replies rows seed))) state.memory.cache)
    (hclean : CacheClean parameter words disclosed (CanonicalCoordinate.value otsSecret ftsSecret replies) state.memory.cache) :
    let oracle := programmedHash parameter otsSecret ftsSecret replies
      (finiteHashAnswer ∅ inputs (canonicalReferenceResidual parameter inputs hencoding replies rows seed))
    let result := hashQueryResult parameter inputs words disclosed known (fresh parameter inputs hencoding words disclosed known publicReplies rows)
      (CanonicalCoordinate.value otsSecret ftsSecret replies) seed input state
    (result.1, result.2.memory) = fixedStep parameter words disclosed known
      (CanonicalCoordinate.value otsSecret ftsSecret replies) oracle input.val state.memory :=
  hashQueryResult_eq_fixed parameter inputs words disclosed known (fresh parameter inputs hencoding words disclosed known publicReplies rows) _ seed _ input state
    hcovered (fresh_local parameter inputs hencoding words disclosed known publicReplies rows input) hmatches hclean
    (fresh_eq_original parameter inputs hencoding words disclosed known otsSecret ftsSecret replies publicReplies
      hagrees hreplies rows seed input)

end SphincsSecurity.Concrete.ResidualByteFrontend

import SphincsSecurity.Proof.FirstParentSettlementGame
import SphincsSecurity.Proof.OtsProbeSettledNativeValue
import SphincsSecurity.Proof.OtsProbeResolvedComputedCoupling

namespace SphincsSecurity

open OracleComp OracleSpec

attribute [local irreducible] instFintypePosition

theorem Settled.node_span
    {parameter : PublicParameter}
    {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    {cache : QueryCache HashSpec} {lay : Layer} {tree : TreeIndex}
    {level : Fin maxLayerHeight} {nodeIdx : LeafIndex}
    (h : Settled parameter otsSecret ftsSecret cache (.node lay tree level nodeIdx)) :
    2 ^ (level.val + 1) * (nodeIdx.val + 1) ≤ 2 ^ maxLayerHeight := by
  have hidx : 2 * nodeIdx.val + 1 < 2 ^ maxLayerHeight := h.valid
  by_cases hzero : level.val = 0
  · simp only [hzero, zero_add, pow_one]
    omega
  · have hpositive : 0 < level.val := by omega
    let childLevel : Fin maxLayerHeight := ⟨level.val - 1, by have := level.isLt; omega⟩
    let childIndex : LeafIndex := ⟨2 * nodeIdx.val + 1, hidx⟩
    have hchild : Settled parameter otsSecret ftsSecret cache (.node lay tree childLevel childIndex) :=
      h.children _ (by simp [Position.children, hidx, hpositive, childLevel, childIndex])
    have hspan := hchild.node_span
    have hlevel : childLevel.val + 1 = level.val := by simp only [childLevel]; omega
    change 2 ^ (childLevel.val + 1) * (2 * nodeIdx.val + 1 + 1) ≤ _ at hspan
    rw [hlevel] at hspan
    rw [pow_succ]
    nlinarith
termination_by level.val

namespace Concrete.OtsProbeSimulation

theorem IsOtsPosition.parent {child parent : Position}
    (hots : IsOtsPosition child) (hparent : child.parentOf = some parent) : IsOtsPosition parent := by
  cases child with
  | chain =>
      simp only [Position.parentOf] at hparent
      split_ifs at hparent <;> cases Option.some.inj hparent <;> trivial
  | leaf =>
      simp only [Position.parentOf] at hparent
      cases Option.some.inj hparent
      trivial
  | node =>
      simp only [Position.parentOf] at hparent
      split_ifs at hparent
      · cases Option.some.inj hparent
        trivial
  | ftsLeaf | ftsNode | ftsRoots => contradiction

theorem IsOtsPosition.resolvable_of_settled
    {parameter : PublicParameter}
    {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    {cache : QueryCache HashSpec} {position : Position}
    (hots : IsOtsPosition position) (hs : Settled parameter otsSecret ftsSecret cache position) :
    ResolvableOtsPosition position := by
  cases position with
  | chain | leaf => trivial
  | node => exact hs.node_span
  | ftsLeaf | ftsNode | ftsRoots => contradiction

theorem ChronologicalCacheAgrees.settled_of_cached_tableInput
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {cache : QueryCache HashSpec}
    (hagrees : ChronologicalCacheAgrees parameter table context cache)
    (hclosed : DeferredComputationsClosed context)
    (completion : Coordinate → HashOutput) (hcompletion : DeferredCompletion table context completion)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    {position : Position} (hots : IsOtsPosition position) (hresolvable : ResolvableOtsPosition position)
    (hcached : cache (tableInput parameter completion (.position position)) ≠ none) :
    Settled parameter (tableOtsSecret completion) ftsSecret cache position := by
  have hquery := hagrees completion hcompletion position hots
  have hknown : ∃ output, context.positionValue position = some output := by
    cases hvalue : context.positionValue position with
    | none => exact False.elim (hcached (by simpa only [ResolveInputAgrees, hvalue] using hquery))
    | some output => exact ⟨output, rfl⟩
  exact ((hclosed position hresolvable hknown).settled_value hagrees completion hcompletion ftsSecret).1

theorem ChronologicalCacheAgrees.input_eq_of_settled
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {cache : QueryCache HashSpec}
    (hagrees : ChronologicalCacheAgrees parameter table context cache)
    (completion : Coordinate → HashOutput) (hcompletion : DeferredCompletion table context completion)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    {position : Position} (hots : IsOtsPosition position)
    (hs : Settled parameter (tableOtsSecret completion) ftsSecret cache position) :
    cachedInput parameter (tableOtsSecret completion) ftsSecret cache position =
      tableInput parameter completion (.position position) := by
  exact honestInput_eq_tableInput_of_children (fromCache cache) parameter completion ftsSecret
    position hots hs.valid (fun child hmem =>
      (hagrees.computed_value_of_settled completion hcompletion ftsSecret child
        (hots.child hmem) (hs.children child hmem)).2)

theorem no_shared_completion_of_early_parent_input
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {initialContext finalContext : DeferredContext} {initialCache finalCache : QueryCache HashSpec}
    (hinitial : ChronologicalCacheAgrees parameter table initialContext initialCache)
    (hfinal : ChronologicalCacheAgrees parameter table finalContext finalCache)
    (hclosed : DeferredComputationsClosed initialContext)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    {parent child : Position} (hots : IsOtsPosition parent) (hchild : child ∈ parent.children)
    (hbefore : ¬ Settled parameter (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
      ftsSecret initialCache child)
    (hafter : Settled parameter (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
      ftsSecret finalCache parent)
    (hcached : initialCache (cachedInput parameter
      (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret finalCache parent) ≠ none) :
    ¬ ∃ completion, DeferredCompletion table initialContext completion ∧ DeferredCompletion table finalContext completion := by
  rintro ⟨completion, hcompletionInitial, hcompletionFinal⟩
  have hkey := hcompletionFinal.tableOtsSecret_eq
  rw [← hkey] at hbefore hafter hcached
  have hinput := hfinal.input_eq_of_settled completion hcompletionFinal ftsSecret hots hafter
  rw [hinput] at hcached
  have hs := hinitial.settled_of_cached_tableInput hclosed completion hcompletionInitial ftsSecret
    hots (hots.resolvable_of_settled hafter) hcached
  exact hbefore (hs.children child hchild)

theorem sampledFirstParentSettlementGame_ots_record_no_shared_completion
    (adversary : Adversary)
    {result : SampledSecrets × ((Bool × QueryCache HashSpec) × Option ExceptionRecord)}
    (hresult : result ∈ support (sampledFirstParentSettlementGame adversary))
    {record : ExceptionRecord} (hrecord : record ∈ result.2.2)
    (hots : ∃ position, AtPosition result.1.parameter record.input position ∧ IsOtsPosition position)
    (table : OtsSecretIndex → HashOutput) (initialContext finalContext : DeferredContext)
    (hinitial : ChronologicalCacheAgrees result.1.parameter table initialContext record.cache)
    (hfinal : ChronologicalCacheAgrees result.1.parameter table finalContext result.2.1.2)
    (hclosed : DeferredComputationsClosed initialContext)
    (hsecrets : result.1.otsSecret =
      fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) :
    ¬ ∃ completion, DeferredCompletion table initialContext completion ∧ DeferredCompletion table finalContext completion := by
  obtain ⟨child, parent, hat, hparent, hbefore, _, _, hafter, hcached, _⟩ :=
    sampledFirstParentSettlementGame_record_full_parent_input adversary hresult hrecord
  obtain ⟨position, hposition, hots⟩ := hots
  have heq := atPosition_unique result.1.parameter hposition hat
  subst position
  rw [hsecrets] at hbefore hafter hcached
  exact no_shared_completion_of_early_parent_input hinitial hfinal hclosed result.1.ftsSecret
    (hots.parent hparent) (Position.mem_children_iff.mpr hparent) hbefore hafter hcached

theorem sampledFirstParentSettlementGame_ots_record_no_resolved_continuation
    (adversary : Adversary)
    {result : SampledSecrets × ((Bool × QueryCache HashSpec) × Option ExceptionRecord)}
    (hresult : result ∈ support (sampledFirstParentSettlementGame adversary))
    {record : ExceptionRecord} (hrecord : record ∈ result.2.2)
    (hots : ∃ position, AtPosition result.1.parameter record.input position ∧ IsOtsPosition position)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (initialContext : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (nativeResult : ResolvedRunResult α) (initialOrdinaryCache finalOrdinaryCache : QueryCache HashSpec)
    (hinitial : ResolvedContextInvariant result.1.parameter table initialContext initialOrdinaryCache record.cache)
    (hfinal : ResolvedContextInvariant result.1.parameter table nativeResult.context finalOrdinaryCache result.2.1.2)
    (hclosed : DeferredComputationsClosed initialContext)
    (hsecrets : result.1.otsSecret =
      fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) :
    some nativeResult ∉ support (runResolvedFromTable initialContext fuel table computation) := by
  intro hrun
  obtain ⟨completion, hcompletion⟩ := hfinal.2.2.2.1
  have hbefore := hcompletion.of_mem_runResolvedFromTable computation initialContext fuel table nativeResult
    completion hinitial.2.1.valuesConsistent hinitial.2.2.1 hrun
  exact sampledFirstParentSettlementGame_ots_record_no_shared_completion adversary hresult hrecord hots table
    initialContext nativeResult.context hinitial.1 hfinal.1 hclosed hsecrets ⟨completion, hbefore, hcompletion⟩

end Concrete.OtsProbeSimulation
end SphincsSecurity

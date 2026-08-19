import XmssSecurity.Proof.CappedGlobalChainHighCausalSimulator

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

structure GlobalEncodingFilteredResultRelation
    (parameter : PublicParameter)
    (leftBase initialLeft initialRight : QueryCache HashSpec)
    (leftResult rightResult : Digest × QueryCache HashSpec) : Prop where
  output_eq : leftResult.1 = rightResult.1
  caches_agree : HashCachesAgreeOn
    (GlobalSigningComparableHashInput parameter) leftResult.2 rightResult.2
  left_le : initialLeft ≤ leftResult.2
  right_le : initialRight ≤ rightResult.2
  filtered : FilteredCacheExtensionRelation leftBase leftResult.2 rightResult.2

structure GlobalRawFilteredResultRelation
    (parameter : PublicParameter)
    (leftBase initialLeft initialRight : QueryCache HashSpec)
    (leftResult rightResult : HashOutput × QueryCache HashSpec) : Prop where
  output_eq : leftResult.1 = rightResult.1
  caches_agree : HashCachesAgreeOn
    (GlobalSigningComparableHashInput parameter) leftResult.2 rightResult.2
  left_le : initialLeft ≤ leftResult.2
  right_le : initialRight ≤ rightResult.2
  filtered : FilteredCacheExtensionRelation leftBase leftResult.2 rightResult.2

theorem relTriple_globalRawHash_run_filtered
    (parameter : PublicParameter)
    (leftBase left right : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn
      (GlobalSigningComparableHashInput parameter) left right)
    (hfiltered : FilteredCacheExtensionRelation leftBase left right)
    (input : HashInput)
    (hinput : GlobalSigningComparableHashInput parameter input) :
    RelTriple ((randomOracle input).run left) ((randomOracle input).run right)
      (GlobalRawFilteredResultRelation parameter leftBase left right) := by
  cases hleft : left input with
  | none =>
      have hright : right input = none := by
        rw [← hagrees input hinput]
        exact hleft
      rw [randomOracle, QueryImpl.withCaching_run_none _ hleft,
        QueryImpl.withCaching_run_none _ hright,
        map_eq_bind_pure_comp, map_eq_bind_pure_comp]
      apply relTriple_bind (relTriple_refl ($ᵗ HashOutput))
      intro leftOutput rightOutput houtput
      subst rightOutput
      exact relTriple_pure_pure ⟨rfl,
        hagrees.cacheQuery (GlobalSigningComparableHashInput parameter)
          left right input leftOutput,
        QueryCache.le_cacheQuery left hleft,
        QueryCache.le_cacheQuery right hright,
        hfiltered.cacheQuery input leftOutput⟩
  | some output =>
      have hright : right input = some output := by
        rw [← hagrees input hinput]
        exact hleft
      rw [randomOracle, QueryImpl.withCaching_run_some _ hleft,
        QueryImpl.withCaching_run_some _ hright]
      exact relTriple_pure_pure ⟨rfl, hagrees, le_rfl, le_rfl, hfiltered⟩

theorem relTriple_globalEncodingHash_run_filtered
    (parameter : PublicParameter)
    (leftBase left right : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn
      (GlobalSigningComparableHashInput parameter) left right)
    (hfiltered : FilteredCacheExtensionRelation leftBase left right)
    (epoch : Epoch) (message : Message) (randomness : Randomness) :
    RelTriple
      ((simulateQ randomOracle
        (Concrete.encodingHash parameter epoch message randomness)).run left)
      ((simulateQ randomOracle
        (Concrete.encodingHash parameter epoch message randomness)).run right)
      (GlobalEncodingFilteredResultRelation parameter leftBase left right) := by
  let input := Concrete.CacheView.encodingInput parameter epoch
    (message, randomness)
  change RelTriple
    ((fun result : HashOutput × QueryCache HashSpec =>
      (truncateHash result.1, result.2)) <$> (randomOracle input).run left)
    ((fun result : HashOutput × QueryCache HashSpec =>
      (truncateHash result.1, result.2)) <$> (randomOracle input).run right)
    (GlobalEncodingFilteredResultRelation parameter leftBase left right)
  apply relTriple_map
  apply relTriple_post_mono
    (relTriple_globalRawHash_run_filtered parameter leftBase left right hagrees
      hfiltered input ⟨epoch, message, randomness, rfl⟩)
  intro leftResult rightResult hresult
  exact ⟨congrArg truncateHash hresult.output_eq, hresult.caches_agree,
    hresult.left_le, hresult.right_le, hresult.filtered⟩

end XmssSecurity.CappedChain

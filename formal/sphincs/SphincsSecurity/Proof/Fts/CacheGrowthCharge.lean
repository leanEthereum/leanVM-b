import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Statement

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem enncard_cacheQuery_of_fresh (cache : QueryCache HashSpec) (input : HashInput)
    (output : HashOutput) (hfresh : cache input = none) :
    QueryCache.enncard (cache.cacheQuery input output) = QueryCache.enncard cache + 1 := by
  have hset : (cache.cacheQuery input output).toSet = insert ⟨input, output⟩ cache.toSet := by
    apply Set.Subset.antisymm (QueryCache.toSet_cacheQuery_subset_insert cache input output)
    rintro pair (heq | hold)
    · subst pair
      exact QueryCache.cacheQuery_self _ _ _
    · exact QueryCache.toSet_mono (QueryCache.le_cacheQuery cache hfresh) hold
  have hnot : (⟨input, output⟩ : Sigma HashSpec.Range) ∉ cache.toSet := by
    simp only [QueryCache.mem_toSet, hfresh, reduceCtorEq, not_false_eq_true]
  unfold QueryCache.enncard
  rw [hset, Set.encard_insert_of_notMem hnot]
  simp

end SphincsSecurity.Concrete

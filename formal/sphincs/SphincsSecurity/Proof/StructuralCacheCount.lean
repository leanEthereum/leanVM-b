import SphincsSecurity.Proof.ParentReserve

namespace SphincsSecurity

open OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
attribute [local irreducible] instFintypePosition

theorem sum_cachedAt_ncard_le (parameter : PublicParameter) {cache : QueryCache HashSpec} (hfinite : Finite cache) :
    (∑ position : Position, (cachedAt parameter cache position).ncard) ≤ {input | cache input ≠ none}.ncard := by
  have hdisjoint : Pairwise (Function.onFun Disjoint (fun position : Position => cachedAt parameter cache position)) := by
    intro left right hne
    change Disjoint (cachedAt parameter cache left) (cachedAt parameter cache right)
    rw [Set.disjoint_left]
    intro input hleft hright
    exact hne (atPosition_unique parameter hleft.2 hright.2)
  have hsubset : (⋃ position : Position, cachedAt parameter cache position) ⊆ {input | cache input ≠ none} := by
    intro input hinput
    obtain ⟨position, hposition⟩ := Set.mem_iUnion.mp hinput
    exact hposition.1
  calc
    _ = ∑ᶠ position : Position, (cachedAt parameter cache position).ncard := (finsum_eq_sum_of_fintype _).symm
    _ = (⋃ position : Position, cachedAt parameter cache position).ncard :=
      (Set.ncard_iUnion_of_finite (fun position => cachedAt_finite parameter hfinite position) hdisjoint).symm
    _ ≤ _ := Set.ncard_le_ncard hsubset hfinite

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)

theorem answerPotential_le_cachedInputs {cache : QueryCache HashSpec} (hfinite : Finite cache) :
    answerPotential parameter otsSecret ftsSecret cache ≤ {input | cache input ≠ none}.ncard := by
  apply le_trans _ (sum_cachedAt_ncard_le parameter hfinite)
  unfold answerPotential
  apply Finset.sum_le_sum
  intro position _
  unfold answerContribution
  split_ifs
  · exact Nat.zero_le _
  · exact le_rfl

theorem parentReserve_le_answerPotential (eligible : Position → Prop) (cache : QueryCache HashSpec) :
    parentReserve parameter otsSecret ftsSecret eligible cache ≤ answerPotential parameter otsSecret ftsSecret cache := by
  unfold parentReserve answerPotential
  apply Finset.sum_le_sum
  intro position _
  unfold parentReserveContribution
  split_ifs with hp
  · have hs : ¬ Settled parameter otsSecret ftsSecret cache position := fun hs => hp.2 hs.children
    rw [answerContribution, if_neg hs]
  · exact Nat.zero_le _

end SphincsSecurity

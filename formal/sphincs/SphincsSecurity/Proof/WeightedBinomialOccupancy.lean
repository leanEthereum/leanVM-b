import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.FewTimeProbability

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem uniform_view_index_weight_expectation (weight : Index → ENNReal) :
    (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] * weight source.1) =
      (∑ index : Index, weight index) / (Fintype.card Index : ENNReal) := by
  have hmarginal : ∀ index, Pr[= index | (Prod.fst <$> ($ᵗ FewTimeView : ProbComp FewTimeView))] =
      Pr[= index | ($ᵗ Index : ProbComp Index)] := by
    intro index
    exact congrArg (fun distribution => distribution index)
      (evalDist_map_fst_uniformSample_prod (α := Index) (β := FtsTree → FtsLeaf))
  rw [← tsum_probOutput_map_mul (mx := ($ᵗ FewTimeView : ProbComp FewTimeView))
    (f := fun source : FewTimeView => source.1) (g := weight)]
  simp only [hmarginal, probOutput_uniformSample, tsum_fintype, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro index _
  exact mul_comm _ _

end SphincsSecurity.Concrete

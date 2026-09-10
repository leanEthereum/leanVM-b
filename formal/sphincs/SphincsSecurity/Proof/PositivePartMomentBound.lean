import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.UniformProposalMixedMoments

namespace SphincsSecurity.Concrete

open _root_.OracleComp ENNReal

theorem uniformWordAverage_const {α : Type} [SampleableType α] [Fintype α] [Nonempty α] [DecidableEq α]
    (steps : Nat) (value : ENNReal) :
    uniformWordAverage steps (fun _word : List α => value) = value := by
  let index : α := Classical.choice inferInstance
  rw [uniformWordAverage, expected_uniformProposalWord_count index steps (fun _ => value)]
  exact binomialAverage_const (ENNReal.inv_le_one.mpr (by exact_mod_cast Fintype.card_pos)) steps value

end SphincsSecurity.Concrete

import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeResolvedSampling

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local irreducible] maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

theorem deferredCompletable_of_no_pending
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hcovered : PendingCovered [] context) : DeferredCompletable table context := by
  let completion : Coordinate → HashOutput
    | .chainStart lay tree leafIdx chainIdx => table ⟨lay, tree, leafIdx, chainIdx⟩
    | .position position => (context.values position).getD 0
  refine ⟨completion, ?_, ?_, ?_, ?_⟩
  · intro coordinate output hvalue
    cases coordinate with
    | chainStart lay tree leafIdx chainIdx => exact (hstarts ⟨lay, tree, leafIdx, chainIdx⟩ output hvalue).symm
    | position position => simp [completion, hconsistent position output hvalue]
  · intro position output hvalue
    simp [completion, hvalue]
  · intro coordinate candidate hmember
    exact False.elim (List.not_mem_nil (hcovered _ hmember))
  · intro index
    cases index
    rfl

open OracleComp.ProgramLogic.Relational

end SphincsSecurity.Concrete.OtsProbeSimulation

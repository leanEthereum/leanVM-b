import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeChronologicalTerminal
import SphincsSecurity.Proof.OtsProbeResolvedComputedInvariant

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedPublishedTreeRoot

set_option maxRecDepth 100000 in
theorem DeferredComputationsClosed.refinedReserve_of_encoding_candidate
    {secretKey : SecretKey} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {ordinaryCache actualCache : QueryCache HashSpec}
    (hclosed : DeferredComputationsClosed context)
    (hinvariant : ResolvedContextInvariant secretKey.parameter table context ordinaryCache actualCache)
    (hsecrets : secretKey.otsSecret = fun lay tree leafIdx chainIdx =>
      truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
    {input : HashInput} {candidate : Probe} {target : Position} {output : HashOutput}
    (hcandidate : EncodingLayerRootCandidateAt secretKey.parameter input candidate)
    (hposition : candidate.coordinate = .position target)
    (hvalue : context.positionValue target = some output) :
    (4 / 3 : ℝ≥0∞) ≤ otsOpeningRefinedQueryReserve secretKey actualCache input := by
  obtain ⟨completion, hcompletion⟩ := hinvariant.2.2.2.1
  obtain ⟨position, hcoordinate, hroot⟩ := encodingLayerRootCandidateAt_isLayerRoot hcandidate
  have heq : position = target := Coordinate.position.inj (hcoordinate.symm.trans hposition)
  have hresolvable : ResolvableOtsPosition target := by
    rw [← heq]
    obtain ⟨lay, tree, rfl⟩ := hroot
    exact resolvableOtsPosition_layerRootPosition lay tree
  exact (hclosed target hresolvable ⟨output, hvalue⟩).refinedReserve_of_encoding_candidate hinvariant.1
    completion hcompletion (hsecrets.trans hcompletion.tableOtsSecret_eq.symm) hcandidate hposition

end SphincsSecurity.Concrete.OtsProbeSimulation

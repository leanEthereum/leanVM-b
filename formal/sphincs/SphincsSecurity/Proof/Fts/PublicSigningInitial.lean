import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Hypertree.CanonicalPublicPrior
import SphincsSecurity.Proof.Reference.ReferenceAuxiliarySigning

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec CanonicalProbeRouting UniformTableCompletion
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

theorem initialKnown_root (words : OtsReferenceWords) (exposedValues : InitialPublicLabels words)
    (labels : Labels) (hlabels : complete (initialAllowed words exposedValues) labels ≠ 0)
    (high : CanonicalGraphHighHalves) :
    knownRoot (initialKnown words exposedValues) = canonicalGraphRoot (coordinateGraphLabels labels high) := by
  apply knownRoot_eq (coordinateOtsSecrets labels) (coordinateFtsSecrets labels)
    (coordinateGraphLabels labels high) words (fun _ _ _ => False)
  rw [coordinateGraphLabels_value]
  exact initialKnown_agrees words exposedValues labels hlabels

end SphincsSecurity.Concrete

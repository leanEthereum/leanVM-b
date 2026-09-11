import SphincsSecurity.Proof.OtsContactCheckpointLaw
import SphincsSecurity.Proof.OtsPrefixCheckpointCompletion

namespace SphincsSecurity.Concrete.OtsPrefix

open _root_.OracleComp OracleSpec PartialChainEndpoint
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

abbrev ContactCheckpointResult (segment : OtsPrefix) :=
  Digest × (((OtsContactTrace.Trace × OracleComp segment.VisibleWorld (Bool × SigningBoundaryTrace)) × Nat) ×
    (Fin segment.digit.val → Digest → Option Digest)) ×
    ((((Bool × SigningBoundaryTrace) × OtsContactTrace.Trace) × Nat) × (Fin segment.digit.val → Digest → Option Digest))

variable (segment : OtsPrefix) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs) (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
  (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph) (secrets : OtsFrontierValues)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (adversary : Adversary)

theorem contactCheckpointRun_observation (result : segment.ContactCheckpointResult)
    (hresult : result ∈ (segment.contactCheckpointRun inputs hencoding hgraph auxiliary secrets ftsSecret words adversary).support) :
    (OtsContactTrace.Seen segment result.1 result.2.1.1.1.1 ↔ Contact result.2.1.2 result.1) ∧
    (OtsContactTrace.Seen segment result.1 (result.2.1.1.1.1 * result.2.2.1.1.2) ↔ Contact result.2.2.2 result.1) ∧
    queryCount result.2.1.2 ≤ OtsContactTrace.prefixCalls segment result.2.1.1.1.1 ∧
    result.2.2.1.2 ≤ OtsContactTrace.prefixCalls segment result.2.2.1.1.2 := by
  have hs := realCheckpointRun_support
    (fun endpoint => extendAux uniformImpl (segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint))
    (segment.contactCheckpointBefore inputs hencoding hgraph auxiliary secrets ftsSecret words adversary)
    (fun _ middle => QueryPause.traced (segment.visibleObservationTrace auxiliary.high) middle.1.1.2) (fun _ _ => none) result hresult
  exact segment.visible_checkpoint_observation auxiliary.high
    (extendAux uniformImpl (segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words result.1)) result.1
    (OtsContactTrace.Stopped segment.parameter words (segment.seedFrontier inputs hencoding hgraph auxiliary secrets words result.1))
    (CausalFrontierProgram.game segment.parameter (segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words result.1)
      ftsSecret words (segment.seedFrontier inputs hencoding hgraph auxiliary secrets words result.1) adversary)
    result.2.1 hs.1 result.2.2 hs.2

end SphincsSecurity.Concrete.OtsPrefix

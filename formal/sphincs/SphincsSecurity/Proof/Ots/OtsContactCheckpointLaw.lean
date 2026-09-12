import SphincsSecurity.Proof.Ots.OtsTraceCheckpointLaw
namespace SphincsSecurity.Concrete.OtsPrefix

open _root_.OracleComp OracleSpec PartialChainEndpoint
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition

variable (segment : OtsPrefix) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs) (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
  (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph) (secrets : OtsFrontierValues)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (adversary : Adversary)

noncomputable abbrev contactCheckpointRun :=
  segment.traceCheckpointRun OtsContactTrace.Stopped inputs hencoding hgraph auxiliary secrets ftsSecret words adversary

theorem contactCheckpointRun_project :
    (segment.contactCheckpointRun inputs hencoding hgraph auxiliary secrets ftsSecret words adversary).map
      (fun result => (result.1,
        (⟨segment.seedFrontier inputs hencoding hgraph auxiliary secrets words result.1,
          result.2.1.1.1.1, result.2.2.1.1.1, result.2.2.1.1.2⟩ : ContactResult), result.2.2.2)) =
    realRun (fun _ => uniformImpl)
      (fun endpoint => segment.instrumentedSeedGame contactObserver inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary)
      (fun _ _ => none) := by
  simpa only [checkpointObserver_contact] using
    segment.traceCheckpointRun_project OtsContactTrace.Stopped inputs hencoding hgraph auxiliary secrets ftsSecret words adversary

end SphincsSecurity.Concrete.OtsPrefix

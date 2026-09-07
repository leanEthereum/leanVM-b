import SphincsSecurity.Proof.JointProbeResolvedCompletionHistory
import SphincsSecurity.Proof.JointProbeOriginalFailureMonitor
import SphincsSecurity.Proof.OtsProbeParentSettlement

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex IsOtsPosition)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def EarlyOtsParentTransition
    (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (before after : QueryCache HashSpec) : Prop :=
  let otsSecret := fun lay tree leafIdx chainIdx => truncateHash (otsTable ⟨lay, tree, leafIdx, chainIdx⟩)
  let ftsSecret := fun index tree leaf => ftsTable (index, tree, leaf)
  ∃ child parent, IsOtsPosition parent ∧ child ∈ parent.children ∧
    ¬ Settled parameter otsSecret ftsSecret before child ∧
    Settled parameter otsSecret ftsSecret after parent ∧
    before (cachedInput parameter otsSecret ftsSecret after parent) ≠ none

theorem resume_none_of_earlyOtsParentTransition
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Frame) (cache : QueryCache HashSpec)
    (hvalid : frame.Valid parameter otsTable ftsTable cache)
    (hcomputed : OtsProbeSimulation.DeferredComputationsClosed frame.context)
    (actual : (OracleWorld + SigningSpec).Range input × QueryCache HashSpec)
    (result) (hresult : result ∈ support (AdaptiveRevealProbe.runDetailed ftsTable frame.state frame.ftsFuel
      (runJointResolved ((jointSourceOuterQuery parameter root input).run frame.cache) frame.context frame.fuel otsTable)))
    (hrel : JointOriginalRunRel parameter otsTable ftsTable result actual)
    (hearly : EarlyOtsParentTransition parameter otsTable ftsTable cache actual.2) :
    resume parameter otsTable input frame.ftsFuel result = none := by
  cases result with
  | stopped hit => rfl
  | done hit state entry =>
      cases hit with
      | true => rfl
      | false =>
          cases entry with
          | none => rfl
          | some entry =>
              by_cases hc : OtsProbeSimulation.DeferredCompletable otsTable entry.context
              · obtain ⟨completion, hcompletion⟩ := hc
                have hinitial := completion_of_mem_jointDetailed ftsTable _ frame.state state frame.ftsFuel frame.context frame.fuel otsTable entry
                  hvalid.2.2.1.2.1.valuesConsistent hvalid.2.2.1.2.2.1 hresult completion hcompletion
                have hi := jointOriginalQuery_continuation_invariants parameter root otsTable ftsTable input frame.state state frame.ftsFuel
                  frame.context frame.fuel frame.cache entry actual hvalid.1 hvalid.2.1 hresult hrel ⟨completion, hcompletion⟩
                obtain ⟨child, parent, hots, hchild, hbefore, hafter, hcached⟩ := hearly
                exact False.elim (OtsProbeSimulation.no_shared_completion_of_early_parent_input hvalid.2.2.1.1 hi.2.2.1.1 hcomputed
                  (fun index tree leaf => ftsTable (index, tree, leaf)) hots hchild hbefore hafter hcached
                  ⟨completion, hinitial, hcompletion⟩)
              · simp [resume, hc]

theorem stepWithFailure_earlyOtsParent_imp_failed
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Frame) (cache : QueryCache HashSpec)
    (henabled : frame.Enabled parameter otsTable ftsTable input cache false)
    (hcomputed : OtsProbeSimulation.DeferredComputationsClosed frame.context)
    (result) (hresult : result ∈ support
      (stepWithFailure exception parameter root otsTable ftsTable input (some frame) cache false false))
    (hearly : EarlyOtsParentTransition parameter otsTable ftsTable cache result.1.2.1.2) :
    result.2 = true := by
  rw [stepWithFailure, dif_pos henabled, support_map] at hresult
  obtain ⟨raw, hraw, rfl⟩ := hresult
  have hs := queryCoupling_support exception parameter root otsTable ftsTable input frame cache false henabled raw hraw
  have hf := resume_none_of_earlyOtsParentTransition parameter root otsTable ftsTable input frame cache henabled.2.1 hcomputed
    raw.2.1 raw.1 hs.2.1 hs.1 hearly
  simp only [hf, Option.isNone_none, Bool.false_or]

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

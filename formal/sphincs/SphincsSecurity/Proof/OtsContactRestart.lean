import SphincsSecurity.Proof.OtsContactCheckpointBudget
import SphincsSecurity.Proof.AdaptiveChainCheckpointContact
import SphincsSecurity.Proof.OtsContactCheckpointObservation

namespace SphincsSecurity.Concrete.OtsPrefix

open _root_.OracleComp OracleSpec PartialChainEndpoint
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition

variable (segment : OtsPrefix) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs) (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
  (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph) (secrets : OtsFrontierValues)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (adversary : Adversary)

theorem instrumentedSeed_newContact_le (budget : Nat)
    (hreal : ∀ result ∈ (realRun (fun _ => uniformImpl)
      (fun endpoint => segment.seedGame inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary) (fun _ _ => none)).support,
      result.2.1.2.hashCalls ≤ budget)
    (hsmall : budget < Fintype.card Digest) :
    let law := realRun (fun _ => uniformImpl)
      (fun endpoint => segment.instrumentedSeedGame contactObserver inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary)
      (fun _ _ => none)
    (1 - (budget : ENNReal) / Fintype.card Digest) * ((Fintype.card Digest : ENNReal) *
      Pr[fun result => (result.2.1.Marked segment.parameter words ∧ ¬OtsContactTrace.Seen segment result.1 result.2.1.before) ∧
        OtsContactTrace.Seen segment result.1 (result.2.1.before * result.2.1.after) | law]) ≤
    ∑' result, law result *
      (((OtsContactTrace.prefixCalls segment result.2.1.before + 2 * OtsContactTrace.prefixCalls segment result.2.1.after : Nat) : ENNReal) *
        if result.2.1.Marked segment.parameter words ∧ ¬OtsContactTrace.Seen segment result.1 result.2.1.before then 1 else 0) := by
  dsimp only
  let checkpoint := segment.contactCheckpointRun inputs hencoding hgraph auxiliary secrets ftsSecret words adversary
  let marked := fun endpoint (middle : ((OtsContactTrace.Trace × OracleComp segment.VisibleWorld (Bool × SigningBoundaryTrace)) × Nat) ×
      (Fin segment.digit.val → Digest → Option Digest)) =>
    OtsContactTrace.Stopped segment.parameter words (segment.seedFrontier inputs hencoding hgraph auxiliary secrets words endpoint) middle.1.1.1 ∧
      ¬Contact middle.2 endpoint
  have hkernel := realCheckpointRun_contact_charge
    (fun endpoint => extendAux uniformImpl (segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint))
    (segment.contactCheckpointBefore inputs hencoding hgraph auxiliary secrets ftsSecret words adversary)
    (fun _ middle => QueryPause.traced (segment.visibleObservationTrace auxiliary.high) middle.1.1.2) (fun _ _ => none)
    marked budget (fun _ _ h => h.2)
    (fun endpoint middle hmiddle _ result hresult =>
      (segment.contactCheckpoint_budget inputs hencoding hgraph auxiliary secrets ftsSecret words adversary budget hreal hsmall
        endpoint middle hmiddle result hresult).2)
  have hevent : Pr[fun result => (result.2.1.Marked segment.parameter words ∧ ¬OtsContactTrace.Seen segment result.1 result.2.1.before) ∧
      OtsContactTrace.Seen segment result.1 (result.2.1.before * result.2.1.after) |
      realRun (fun _ => uniformImpl)
        (fun endpoint => segment.instrumentedSeedGame contactObserver inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary)
        (fun _ _ => none)] =
      Pr[fun result => marked result.1 result.2.1 ∧ Contact result.2.2.2 result.1 | checkpoint] := by
    rw [← segment.contactCheckpointRun_project inputs hencoding hgraph auxiliary secrets ftsSecret words adversary,
      ← PMF.monad_map_eq_map, probEvent_map]
    simp only [Function.comp_def, ContactResult.Marked, probEvent_eq_tsum_ite, PMF.probOutput_eq_apply]
    apply tsum_congr
    intro result
    by_cases hr : result ∈ checkpoint.support
    · have hs := segment.contactCheckpointRun_observation inputs hencoding hgraph auxiliary secrets ftsSecret words adversary result hr
      simp only [hs.1, hs.2.1, marked, checkpoint]
    · have hz : checkpoint result = 0 := not_not.mp hr
      simp only [checkpoint] at hz
      simp only [checkpoint, hz, ite_self]
  rw [hevent]
  apply hkernel.trans
  rw [← segment.contactCheckpointRun_project inputs hencoding hgraph auxiliary secrets ftsSecret words adversary, expectation_map]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ checkpoint.support
  · have hs := segment.contactCheckpointRun_observation inputs hencoding hgraph auxiliary secrets ftsSecret words adversary result hr
    apply mul_le_mul' le_rfl
    by_cases hm : marked result.1 result.2.1
    · have hm' : OtsContactTrace.Stopped segment.parameter words
          (segment.seedFrontier inputs hencoding hgraph auxiliary secrets words result.1) result.2.1.1.1.1 ∧
          ¬OtsContactTrace.Seen segment result.1 result.2.1.1.1.1 := ⟨hm.1, fun hc => hm.2 (hs.1.mp hc)⟩
      simp only [ContactResult.Marked, if_pos hm, if_pos hm', mul_one]
      exact_mod_cast (Nat.add_le_add hs.2.2.1 (Nat.mul_le_mul_left 2 hs.2.2.2))
    · have hm' : ¬(OtsContactTrace.Stopped segment.parameter words
          (segment.seedFrontier inputs hencoding hgraph auxiliary secrets words result.1) result.2.1.1.1.1 ∧
          ¬OtsContactTrace.Seen segment result.1 result.2.1.1.1.1) := by
        intro h
        exact hm ⟨h.1, fun hc => h.2 (hs.1.mpr hc)⟩
      simp only [ContactResult.Marked, if_neg hm, if_neg hm', mul_zero, le_refl]
  · have hz : checkpoint result = 0 := not_not.mp hr
    simp only [checkpoint, contactCheckpointRun] at hz
    simp only [hz, zero_mul, zero_le]

end SphincsSecurity.Concrete.OtsPrefix

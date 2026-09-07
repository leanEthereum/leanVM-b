import SphincsSecurity.Proof.StoppedOuterCap
import SphincsSecurity.Proof.StoppedTargetCoverageCharge
import SphincsSecurity.Proof.LiveObservedMessageResidual

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem probEvent_retained_liveObservedCover_le_stopped_arrival
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (parameter : PublicParameter) (root : Digest)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q : Nat) (hq : q ≤ 2 ^ 127)
    (hbound : (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable))
      (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP (· matches Sum.inr _) q)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool)
    (hnone : ∀ input, MessageHashInput parameter input → cache input = none)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl (secretKey parameter root otsTable ftsTable))
      (unloggedRetainedRestComputation adversary ⟨root, parameter⟩)).run (cache, [])), QueryCache.enncard result.2.1 ≤ q) :
    Pr[fun result => result.1.2.2 = false ∧ result.2 = false ∧
      ∃ value, result.1.2.1.1 = some value ∧ ObservedRetainedCover value (messageAnswers parameter result.1.2.1.2) |
      runWithFailure exception parameter root otsTable ftsTable (retainedComputation adversary parameter root q) frame cache hit failed] ≤
      expectedStoppedIndexCharge exception parameter root otsTable ftsTable q (targetArrivalHashCost parameter) ∅ Finset.univ
        (unloggedRetainedRestComputation adversary ⟨root, parameter⟩) frame (cache, []) hit failed * ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
  rw [runWithFailure_retainedComputation_trace exception adversary parameter root otsTable ftsTable q hbound, probEvent_map]
  apply le_trans ?_ (probEvent_runWithFailure_liveCover_le_stopped_arrival exception parameter root otsTable ftsTable q hq
    (unloggedRetainedRestComputation adversary ⟨root, parameter⟩) frame cache hit failed hnone hbudget)
  apply probEvent_mono
  intro result _ hcover
  obtain ⟨hhit, hfailed, value, hvalue, hobserved⟩ := hcover
  have hvalue' : (root, arrangeRetainedTrace result.1.2.1.1) = value := Option.some.inj hvalue
  subst value
  have hvalid : SigningTranscript.Valid result.1.2.1.1.2 := by
    have hwin := hobserved.1
    simp only [OtsProbeSimulation.retainedRestVerdict, Bool.and_eq_true, decide_eq_true_eq] at hwin
    exact hwin.1.1
  exact ⟨hhit, hfailed, hvalid, observedFewTimeCover_signingCacheCovered _ _ _ _ _ hobserved.2⟩

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

import SphincsSecurity.Proof.CausalVerifierTrace
import SphincsSecurity.Proof.VerifierWitnessClassification
import SphincsSecurity.Proof.EncodingMarkerBound

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec OtsContactTrace
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs frontierRoot

theorem referenceInstrumentedRest_frontier (key : SecretKey) (f : QueryImpl HashSpec Id) (labels : CanonicalGraphLabels)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary) (result : ContactResult)
    (hr : result ∈ support (referenceInstrumentedRest contactObserver key f labels selections dummy adversary)) :
    result.frontier = canonicalGraphFrontier key.otsSecret labels (referenceFamilyWords selections dummy) := by
  rw [referenceInstrumentedRest, contactObserver, simulateQ_map, support_map] at hr
  obtain ⟨split, _, heq⟩ := hr
  exact (congrArg ContactResult.frontier heq).symm

theorem referenceInstrumentedRest_verify (key : SecretKey) (f : QueryImpl HashSpec Id) (labels : CanonicalGraphLabels)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary) (result : ContactResult)
    (hr : result ∈ support (referenceInstrumentedRest contactObserver key f labels selections dummy adversary))
    (hsuccess : result.output.1 = true) :
    let words := referenceFamilyWords selections dummy
    let frontier := canonicalGraphFrontier key.otsSecret labels words
    let root := frontierRoot key.parameter (maskOtsPrefixes key.parameter words f) words frontier
    ∃ before : AdversaryTrace,
      before ∈ support (fixedTrace f (CausalFrontierProgram.adversaryRun key.parameter root f key.ftsSecret words frontier (adversary.main ⟨root, key.parameter⟩))) ∧
      SigningTranscript.Valid before.1.1.2 ∧ ¬SigningTranscript.Contains before.1.1.2 before.1.1.1 ∧
      evalWithAnswerFn f (verify ⟨root, key.parameter⟩ before.1.1.1.message before.1.1.1.signature) = true ∧
      result.before * result.after = before.2 * answerTrace f (verify ⟨root, key.parameter⟩ before.1.1.1.message before.1.1.1.signature) ∧
      ContainsRun f (result.before * result.after) (verify ⟨root, key.parameter⟩ before.1.1.1.message before.1.1.1.signature) := by
  have ht : (result.output, result.before * result.after) ∈ support
      ((fun output : ContactResult => (output.output, output.before * output.after)) <$>
        referenceInstrumentedRest contactObserver key f labels selections dummy adversary) := by
    rw [support_map]
    exact ⟨result, hr, rfl⟩
  rw [referenceInstrumentedRest, ← simulateQ_map, contactObserver_trace] at ht
  exact fixedTrace_game_verify key.parameter f key.ftsSecret (referenceFamilyWords selections dummy)
    (canonicalGraphFrontier key.otsSecret labels (referenceFamilyWords selections dummy)) adversary
    (result.output, result.before * result.after) ht hsuccess

end SphincsSecurity.Concrete

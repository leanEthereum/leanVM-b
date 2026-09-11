import SphincsSecurity.Proof.ReferenceFtsCoverage
import SphincsSecurity.Proof.ReferencePrimitiveWitness

namespace SphincsSecurity.Concrete.ReferenceVerifierWitness

open _root_.OracleComp OracleSpec OtsContactTrace OtsVerifierWitness
open RetainedResidual (signingInput)
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] frontierRoot canonicalGraphInputs canonicalEncodingInputs instFintypePosition chainWalk sequenceFin

def ForgeryWitnessFor (key : SecretKey) (f : QueryImpl HashSpec Id) (root : Digest) (words : OtsReferenceWords)
    (selections : ReferenceFamily) (adversary : Adversary) (result : ContactResult) (before : AdversaryTrace) : Prop :=
  let actualKey : SecretKey := { key with root := root }
  let labels := canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f
  let frontier := canonicalGraphFrontier key.otsSecret labels words
  let trace := result.before * result.after
  before ∈ support (fixedTrace f (CausalFrontierProgram.adversaryRun key.parameter actualKey.root f key.ftsSecret words frontier
    (adversary.main ⟨actualKey.root, key.parameter⟩))) ∧
  SigningTranscript.Valid before.1.1.2 ∧ ¬SigningTranscript.Contains before.1.1.2 before.1.1.1 ∧
  (∀ message signature, (⟨message, some signature⟩ : SigningEntry) ∈ before.1.1.2 →
    ReferenceSigningWitness.SignatureOrigin actualKey f message signature before.1.2) ∧
  result.frontier = frontier ∧
  trace = before.2 * answerTrace f (verify ⟨actualKey.root, key.parameter⟩ before.1.1.1.message before.1.1.1.signature) ∧
  (ReferenceFtsCoverage.Outcome actualKey f before.1.1.2 before.1.2 trace before.1.1.1 ∨
    ReferencePrimitiveWitness.Outcome actualKey f words (canonicalGraphMessage labels) selections result)

def ForgeryWitnessAtRoot (key : SecretKey) (f : QueryImpl HashSpec Id) (root : Digest) (words : OtsReferenceWords)
    (selections : ReferenceFamily) (adversary : Adversary) (result : ContactResult) : Prop :=
  ∃ before, ForgeryWitnessFor key f root words selections adversary result before

theorem SuccessWitnessFor.classification {key : SecretKey} {f : QueryImpl HashSpec Id} {root : Digest} {words : OtsReferenceWords}
    {selections : ReferenceFamily} {adversary : Adversary} {result : ContactResult} {before : AdversaryTrace}
    (h : SuccessWitnessFor key f root words selections adversary result before) : ForgeryWitnessFor key f root words selections adversary result before := by
  obtain ⟨hb, hv, hf, horigin, hfrontier, ht, digest, hdigest, hrun, hadmissible, hcases⟩ := h
  refine ⟨hb, hv, hf, horigin, hfrontier, ht, ?_⟩
  have heval : evalWithAnswerFn f (messageDigest key.parameter root before.1.1.1.message before.1.1.1.signature.randomness) =
      truncateMessageDigest (f (signingInput { key with root := root } before.1.1.1.message before.1.1.1.signature)) := rfl
  have hd := hdigest.symm.trans heval
  rcases hcases with ⟨_, _, hqueries, hnew⟩ | hlayer | hfts
  · rw [hd] at hadmissible hqueries
    exact Or.inl (ReferenceFtsCoverage.classification { key with root := root } f before.1.1.2 before.1.2
      (result.before * result.after) before.1.1.1 horigin hnew hrun hadmissible hqueries)
  · apply Or.inr
    apply ReferencePrimitiveWitness.layer_exception { key with root := root } f words _ selections result ?_ hlayer
    intro lay tree leaf chain
    rw [hfrontier, canonicalGraphLabels_frontier key.parameter key.otsSecret key.ftsSecret f words root]
    rfl
  · exact Or.inr (Or.inr (Or.inl (ReferencePrimitiveWitness.fts_exception { key with root := root } f words _ _ hfts)))

theorem SuccessWitnessAtRoot.classification {key : SecretKey} {f : QueryImpl HashSpec Id} {root : Digest} {words : OtsReferenceWords}
    {selections : ReferenceFamily} {adversary : Adversary} {result : ContactResult}
    (h : SuccessWitnessAtRoot key f root words selections adversary result) : ForgeryWitnessAtRoot key f root words selections adversary result := by
  obtain ⟨before, hbefore⟩ := h
  exact ⟨before, hbefore.classification⟩

theorem sample_success_classification (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (reference : ReferenceFamily × (inputs → HashOutput)) (hreference : reference ∈ (referenceFamilyOracleSample key inputs hencoding).support)
    (dummy : OtsReferenceWords) (hdummy : ∀ lay tree leaf, TargetSum.Valid (dummy lay tree leaf)) (adversary : Adversary) (result : ContactResult)
    (hr : result ∈ support (referenceInstrumentedRest contactObserver key (finiteHashAnswer ∅ inputs reference.2)
      (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret (finiteHashAnswer ∅ inputs reference.2)) reference.1 dummy adversary))
    (hsuccess : result.output.1 = true) :
    ForgeryWitnessAtRoot key (finiteHashAnswer ∅ inputs reference.2) (rootedKey key (finiteHashAnswer ∅ inputs reference.2)).root
      (referenceFamilyWords reference.1 dummy) reference.1 adversary result :=
  (sample_success_witness key inputs hencoding hgraph reference hreference dummy hdummy adversary result hr hsuccess).classification

end SphincsSecurity.Concrete.ReferenceVerifierWitness

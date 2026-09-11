import SphincsSecurity.Proof.VerifierTraceSource
import SphincsSecurity.Proof.CausalFrontierProgram

namespace SphincsSecurity.Concrete.OtsContactTrace

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] frontierRoot maskOtsPrefixes

theorem ContainsRun.mul_left {Result : Type} {f : QueryImpl HashSpec Id} {trace : Trace} {computation : OracleComp HashSpec Result}
    (h : ContainsRun f trace computation) (before : Trace) : ContainsRun f (before * trace) computation := by
  intro input hi
  exact List.mem_append_right _ (h input hi)

abbrev AdversaryTrace := ((Forgery × QueryLog SigningSpec) × SigningBoundaryTrace) × Trace

private theorem fixedTrace_padding_support (f : QueryImpl HashSpec Id) (padding : SigningBoundaryTrace)
    (computation : OracleComp OracleWorld (Bool × SigningBoundaryTrace)) (result : (Bool × SigningBoundaryTrace) × Trace)
    (hr : result ∈ support (fixedTrace f ((fun output => (output.1, padding * output.2)) <$> computation))) :
    ∃ before ∈ support (fixedTrace f computation), before.1.1 = result.1.1 ∧ before.2 = result.2 := by
  rw [fixedTrace_map, support_map] at hr
  obtain ⟨before, hb, rfl⟩ := hr
  exact ⟨before, hb, rfl, rfl⟩

theorem fixedTrace_gameRest_verify (parameter : PublicParameter) (root : Digest) (f : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (frontier : OtsFrontierValues) (adversary : Adversary)
    (result : (Bool × SigningBoundaryTrace) × Trace)
    (hr : result ∈ support (fixedTrace f (CausalFrontierProgram.gameRest parameter root f ftsSecret words frontier adversary)))
    (hsuccess : result.1.1 = true) :
    ∃ before : AdversaryTrace,
      before ∈ support (fixedTrace f (CausalFrontierProgram.adversaryRun parameter root f ftsSecret words frontier (adversary.main ⟨root, parameter⟩))) ∧
      SigningTranscript.Valid before.1.1.2 ∧ ¬SigningTranscript.Contains before.1.1.2 before.1.1.1 ∧
      evalWithAnswerFn f (verify ⟨root, parameter⟩ before.1.1.1.message before.1.1.1.signature) = true ∧
      result.2 = before.2 * answerTrace f (verify ⟨root, parameter⟩ before.1.1.1.message before.1.1.1.signature) ∧
      ContainsRun f result.2 (verify ⟨root, parameter⟩ before.1.1.1.message before.1.1.1.signature) := by
  rw [CausalFrontierProgram.gameRest, fixedTrace_bind, mem_support_bind_iff] at hr
  obtain ⟨before, hb, hr⟩ := hr
  simp only [fixedTrace_bind, fixedTrace_boundary_hash, fixedTrace_pure, pure_bind, map_pure, mul_one, mem_support_pure_iff] at hr
  subst result
  simp only [boundaryEval_fst, Bool.and_eq_true, decide_eq_true_eq] at hsuccess
  exact ⟨before, hb, hsuccess.1.1, hsuccess.1.2, hsuccess.2, rfl, (containsRun_answerTrace f _).mul_left before.2⟩

theorem fixedTrace_game_verify (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (frontier : OtsFrontierValues) (adversary : Adversary)
    (result : (Bool × SigningBoundaryTrace) × Trace)
    (hr : result ∈ support (fixedTrace f (CausalFrontierProgram.game parameter f ftsSecret words frontier adversary)))
    (hsuccess : result.1.1 = true) :
    let root := frontierRoot parameter (maskOtsPrefixes parameter words f) words frontier
    ∃ before : AdversaryTrace,
      before ∈ support (fixedTrace f (CausalFrontierProgram.adversaryRun parameter root f ftsSecret words frontier (adversary.main ⟨root, parameter⟩))) ∧
      SigningTranscript.Valid before.1.1.2 ∧ ¬SigningTranscript.Contains before.1.1.2 before.1.1.1 ∧
      evalWithAnswerFn f (verify ⟨root, parameter⟩ before.1.1.1.message before.1.1.1.signature) = true ∧
      result.2 = before.2 * answerTrace f (verify ⟨root, parameter⟩ before.1.1.1.message before.1.1.1.signature) ∧
      ContainsRun f result.2 (verify ⟨root, parameter⟩ before.1.1.1.message before.1.1.1.signature) := by
  obtain ⟨rest, hr, hs, ht⟩ := fixedTrace_padding_support f ((FreeMonoid.of none) ^ 1212415) _ result hr
  have h := fixedTrace_gameRest_verify parameter _ f ftsSecret words frontier adversary rest hr (hs.trans hsuccess)
  simpa only [ht] using h

end SphincsSecurity.Concrete.OtsContactTrace

import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalHiddenMatch

/-!
# Hidden fixed-candidate boundary lift

The hidden candidate observer crosses classification and canonicalization. Publication rules out a
matching private witness at an already revealed coordinate; otherwise the hidden observer is the
existing fixed-candidate observer.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable

theorem probEvent_classifyDirectWitnessPlanMatchesCandidate_le_hidden
    (table : OtsSecretIndex → HashOutput) (candidate : Probe)
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp PrivateWitnessPlanOutput)
    (context : DeferredContext) (fuel : Nat) (value : α) (candidates : List Probe)
    (hpublished : PublishedValues context.state)
    (hcontinuation : ¬PrivateStructuralHit context → DeferredCompletable table context →
      Pr[PrivateWitnessPlanMatchesCandidate candidate |
          observe context fuel value candidates] ≤
        Pr[fun hit : Bool => hit = true |
          hiddenPrivateCandidateFire candidate context]) :
    Pr[PrivateWitnessPlanMatchesCandidate candidate |
        classifyDirectWitnessPlanObserve table observe context fuel value candidates] ≤
      Pr[fun hit : Bool => hit = true |
        hiddenPrivateCandidateFire candidate context] := by
  by_cases hrevealed : candidate.coordinate ∈ context.state.revealed
  · rw [hiddenPrivateCandidateFire_of_revealed candidate context hrevealed]
    unfold classifyDirectWitnessPlanObserve
    by_cases hhit : PrivateStructuralHit context
    · simp only [hhit, ↓reduceDIte]
      have hspec := privateHitWitnessOf_spec context hhit
      have hnotMatch :
          ¬(privateHitWitnessOf context hhit).MatchesCandidate candidate := by
        intro hmatch
        have hknown := hpublished candidate.coordinate hrevealed
        rw [hmatch.1] at hknown
        exact hknown hspec.1
      simp [PrivateWitnessPlanMatchesCandidate, hnotMatch]
    · simp only [hhit, ↓reduceDIte]
      by_cases hcompletable : DeferredCompletable table context
      · simp only [hcompletable, ↓reduceIte]
        simpa [hiddenPrivateCandidateFire, hrevealed] using
          hcontinuation hhit hcompletable
      · simp [hcompletable, PrivateWitnessPlanMatchesCandidate]
  · rw [hiddenPrivateCandidateFire_of_not_revealed candidate context hrevealed]
    apply probEvent_classifyDirectWitnessPlanMatchesCandidate_le table candidate observe context
      fuel value candidates
    intro hhit hcompletable
    simpa [hiddenPrivateCandidateFire, hrevealed] using hcontinuation hhit hcompletable

theorem hiddenPrivateCandidateFire_canonicalize
    (table : OtsSecretIndex → HashOutput) (candidate : Probe)
    (context : DeferredContext) (hconsistent : context.ValuesConsistent) :
    evalDist (hiddenPrivateCandidateFire candidate
        (canonicalizeMaterializedValues table context)) =
      evalDist (hiddenPrivateCandidateFire candidate context) := by
  unfold hiddenPrivateCandidateFire
  rw [canonicalizeMaterializedValues_revealed]
  by_cases hrevealed : candidate.coordinate ∈ context.state.revealed
  · simp [hrevealed]
  · simp only [hrevealed, ↓reduceIte]
    exact congrArg evalDist
      (privateCandidateFire_canonicalize table candidate context hconsistent)

theorem probEvent_canonicalizeDirectWitnessPlanMatchesCandidate_le_hidden
    (table : OtsSecretIndex → HashOutput) (candidate : Probe)
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp PrivateWitnessPlanOutput)
    (context : DeferredContext) (fuel : Nat) (value : α) (candidates : List Probe)
    (hconsistent : context.ValuesConsistent)
    (hpublished : PublishedValues context.state)
    (hcontinuation :
      let canonical := canonicalizeMaterializedValues table context
      ¬PrivateStructuralHit canonical → DeferredCompletable table canonical →
      Pr[PrivateWitnessPlanMatchesCandidate candidate |
          observe canonical fuel value candidates] ≤
        Pr[fun hit : Bool => hit = true |
          hiddenPrivateCandidateFire candidate canonical]) :
    Pr[PrivateWitnessPlanMatchesCandidate candidate |
        canonicalizeDirectWitnessPlanObserve table observe context fuel value candidates] ≤
      Pr[fun hit : Bool => hit = true |
        hiddenPrivateCandidateFire candidate context] := by
  let canonical := canonicalizeMaterializedValues table context
  have hcanonicalPublished : PublishedValues canonical.state :=
    hpublished.to_canonicalizedMaterializedValues
  have hclassify := probEvent_classifyDirectWitnessPlanMatchesCandidate_le_hidden table candidate
    observe canonical fuel value candidates hcanonicalPublished hcontinuation
  have hcanonicalize :
      canonicalizeDirectWitnessPlanObserve table observe context fuel value candidates =
        classifyDirectWitnessPlanObserve table observe canonical fuel value candidates := by
    unfold canonicalizeDirectWitnessPlanObserve
    by_cases hhit : PrivateStructuralHit canonical
    · simp [canonical, hhit, classifyDirectWitnessPlanObserve]
    · simp [canonical, hhit, hpublished, classifyDirectWitnessPlanObserve]
  rw [hcanonicalize]
  refine hclassify.trans ?_
  rw [probEvent_eq_eq_probOutput, probEvent_eq_eq_probOutput]
  exact le_of_eq (OracleComp.probOutput_congr rfl
    (hiddenPrivateCandidateFire_canonicalize table candidate context hconsistent))

end SphincsSecurity.Concrete.OtsProbeSimulation

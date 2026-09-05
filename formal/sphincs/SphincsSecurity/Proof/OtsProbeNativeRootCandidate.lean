import SphincsSecurity.Proof.OtsProbeNativeStructuralRootGuess

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem EncodingLayerRootCandidateAt.no_native_candidate
    {parameter : PublicParameter} {input : HashInput} {candidate : Probe}
    (h : EncodingLayerRootCandidateAt parameter input candidate) (state : LazyRevealProbe.State Coordinate) :
    (purePlanProbingHashQuery parameter input state).candidate? = none := by
  obtain ⟨position, index, hat, _⟩ := h
  rw [purePlanProbingHashQuery, decodeProbe?_eq_none_of_atEncodingPosition hat,
    decodePosition?_eq_none_of_atEncodingPosition hat]

theorem EncodingLayerRootCandidateAt.not_structural
    {parameter : PublicParameter} {input : HashInput} {encoding structural : Probe}
    (h : EncodingLayerRootCandidateAt parameter input encoding) :
    ¬StructuralLayerRootCandidateAt parameter input structural := by
  obtain ⟨position, index, hat, _⟩ := h
  rintro ⟨parent, target, hparent, _⟩
  exact hat.not_atPosition parent hparent

def NativeRootCandidateAt (parameter : PublicParameter) (input : HashInput)
    (context : DeferredContext) (candidate : Probe) : Prop :=
  (purePlanProbingHashQuery parameter input context.state).candidate? = some candidate ∨
    EncodingLayerRootCandidateAt parameter input candidate ∨
    (KnownHiddenStructuralRootQuery parameter input context ∧ StructuralLayerRootCandidateAt parameter input candidate)

theorem nativeRootCandidateAt_unique
    {parameter : PublicParameter} {input : HashInput} {context : DeferredContext} {left right : Probe}
    (hleft : NativeRootCandidateAt parameter input context left)
    (hright : NativeRootCandidateAt parameter input context right) : left = right := by
  rcases hleft with hleft | hleft | ⟨hleftKnown, hleft⟩
  · rcases hright with hright | hright | ⟨hrightKnown, hright⟩
    · exact Option.some.inj (hleft.symm.trans hright)
    · rw [hright.no_native_candidate context.state] at hleft
      contradiction
    · rw [hrightKnown.no_candidate] at hleft
      contradiction
  · rcases hright with hright | hright | ⟨hrightKnown, hright⟩
    · rw [hleft.no_native_candidate context.state] at hright
      contradiction
    · exact encodingLayerRootCandidateAt_unique hleft hright
    · exact False.elim (hleft.not_structural hright)
  · rcases hright with hright | hright | ⟨hrightKnown, hright⟩
    · rw [hleftKnown.no_candidate] at hright
      contradiction
    · exact False.elim (hright.not_structural hleft)
    · exact structuralLayerRootCandidateAt_unique hleft hright

noncomputable def nativeRootCandidate? (parameter : PublicParameter) (input : HashInput)
    (context : DeferredContext) : Option Probe :=
  if h : ∃ candidate, NativeRootCandidateAt parameter input context candidate then some h.choose else none

theorem nativeRootCandidate?_eq_some_iff
    (parameter : PublicParameter) (input : HashInput) (context : DeferredContext) (candidate : Probe) :
    nativeRootCandidate? parameter input context = some candidate ↔ NativeRootCandidateAt parameter input context candidate := by
  unfold nativeRootCandidate?
  split
  next hexists =>
    constructor
    · intro heq
      have hchosen : hexists.choose = candidate := Option.some.inj heq
      simpa only [← hchosen] using hexists.choose_spec
    · intro hcandidate
      exact congrArg some (nativeRootCandidateAt_unique hexists.choose_spec hcandidate)
  next hnone =>
    constructor
    · intro heq; contradiction
    · intro hcandidate
      exact False.elim (hnone ⟨candidate, hcandidate⟩)

theorem NativeRootContextRel.candidateAt_iff
    {target : Position} {before after : HashOutput} {left right : DeferredContext}
    (h : NativeRootContextRel target before after left right)
    (parameter : PublicParameter) (input : HashInput) (candidate : Probe) :
    NativeRootCandidateAt parameter input left candidate ↔ NativeRootCandidateAt parameter input right candidate := by
  unfold NativeRootCandidateAt
  rw [purePlanProbingHashQuery_eq_of_nativeRootContextRel h,
    knownHiddenStructuralRootQuery_replace_root_iff h parameter input]

theorem NativeRootContextRel.candidate_eq
    {target : Position} {before after : HashOutput} {left right : DeferredContext}
    (h : NativeRootContextRel target before after left right)
    (parameter : PublicParameter) (input : HashInput) :
    nativeRootCandidate? parameter input left = nativeRootCandidate? parameter input right := by
  cases hleft : nativeRootCandidate? parameter input left with
  | none =>
      cases hright : nativeRootCandidate? parameter input right with
      | none => rfl
      | some candidate =>
          have hcandidate := (h.candidateAt_iff parameter input candidate).mpr
            ((nativeRootCandidate?_eq_some_iff parameter input right candidate).mp hright)
          have heq := (nativeRootCandidate?_eq_some_iff parameter input left candidate).mpr hcandidate
          rw [hleft] at heq
          contradiction
  | some candidate =>
      have hcandidate := (h.candidateAt_iff parameter input candidate).mp
        ((nativeRootCandidate?_eq_some_iff parameter input left candidate).mp hleft)
      exact ((nativeRootCandidate?_eq_some_iff parameter input right candidate).mpr hcandidate).symm

theorem nativeRootHashSafe_failure_of_hidden_result_candidate
    (parameter : PublicParameter) (target : Position) (hroot : IsLayerRoot target) (before after : HashOutput)
    (input : HashInput) (context : DeferredContext) (h : NativePositionReplaceable target before after context)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hunsafe : ¬NativeRootHashSafe parameter target before after input context)
    (result : ResolvedRunResult (HashOutput × SplitHashCache))
    (hresult : some result ∈ support (runResolvedFromTable context fuel table ((probingHashQuery parameter input).run cache)))
    (hhidden : .position target ∉ result.context.state.revealed) :
    ∃ candidate, nativeRootCandidate? parameter input context = some candidate ∧
      candidate.coordinate = .position target ∧
      (candidate.candidate = truncateHash before ∨ candidate.candidate = truncateHash after) := by
  have hfailure := nativeRootHashSafe_failure_of_hidden_result_guesses parameter target hroot before after input context h
    fuel table cache hunsafe result hresult hhidden
  rcases hfailure with (hencoding | hencoding) | ⟨candidate, hplan, hexposure⟩ | ⟨hknown, candidate, hcandidate, hcoordinate, hguess⟩
  · refine ⟨⟨.position target, truncateHash before⟩, ?_, rfl, Or.inl rfl⟩
    apply (nativeRootCandidate?_eq_some_iff parameter input context _).mpr
    exact Or.inr (Or.inl ((decodeEncodingLayerRootCandidate?_eq_some_iff parameter input _).mp hencoding))
  · refine ⟨⟨.position target, truncateHash after⟩, ?_, rfl, Or.inr rfl⟩
    apply (nativeRootCandidate?_eq_some_iff parameter input context _).mpr
    exact Or.inr (Or.inl ((decodeEncodingLayerRootCandidate?_eq_some_iff parameter input _).mp hencoding))
  · exact ⟨candidate, (nativeRootCandidate?_eq_some_iff parameter input context candidate).mpr (Or.inl hplan), hexposure⟩
  · exact ⟨candidate, (nativeRootCandidate?_eq_some_iff parameter input context candidate).mpr
      (Or.inr (Or.inr ⟨hknown, hcandidate⟩)), hcoordinate, hguess⟩

end SphincsSecurity.Concrete.OtsProbeSimulation

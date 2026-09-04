import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateTraceInvariant

/-!
# All-miss candidate preparation

The finite resolver endpoint is strengthened to return the prepared context on an all-miss path. Every candidate coordinate then has one persistent private output which avoids every recorded digest at that coordinate.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable

def CandidateOutputsSafe (context : DeferredContext) (candidates : List Probe) : Prop :=
  ∀ candidate ∈ candidates,
    match candidate.coordinate with
    | .chainStart _ _ _ _ => True
    | .position position =>
        ∃ output, context.values position = some output ∧
          truncateHash output ≠ candidate.candidate

theorem candidateListHits_iff_exists_mem
    (target : Position) (candidates : List Probe) (output : HashOutput) :
    candidateListHits target candidates output ↔
      ∃ candidate ∈ candidates,
        candidate.coordinate = .position target ∧
          truncateHash output = candidate.candidate := by
  induction candidates with
  | nil => simp [candidateListHits]
  | cons candidate remaining ih =>
      simp only [candidateListHits, List.mem_cons, ih]
      constructor
      · rintro (hhead | ⟨found, hfound, hcoordinate, hdigest⟩)
        · exact ⟨candidate, Or.inl rfl, hhead.1, hhead.2⟩
        · exact ⟨found, Or.inr hfound, hcoordinate, hdigest⟩
      · rintro ⟨found, rfl | hfound, hcoordinate, hdigest⟩
        · exact Or.inl ⟨hcoordinate, hdigest⟩
        · exact Or.inr ⟨found, hfound, hcoordinate, hdigest⟩

theorem not_recordedCandidateHit_of_candidateOutputsSafe
    (context : DeferredContext) (candidates : List Probe)
    (hsafe : CandidateOutputsSafe context candidates) :
    ¬RecordedCandidateHit context candidates := by
  rintro ⟨position, output, hvalue, hhit⟩
  obtain ⟨candidate, hcandidate, hcoordinate, hdigest⟩ :=
    (candidateListHits_iff_exists_mem position candidates output).1 hhit
  have hcandidateSafe := hsafe candidate hcandidate
  rw [hcoordinate] at hcandidateSafe
  obtain ⟨safeOutput, hsafeOutput, hne⟩ := hcandidateSafe
  have heq : safeOutput = output := by
    rw [hvalue] at hsafeOutput
    exact Option.some.inj hsafeOutput.symm
  exact hne (heq ▸ hdigest)

theorem CandidateOutputsSafe.of_privateValuesLE
    {left right : DeferredContext} {candidates : List Probe}
    (hsafe : CandidateOutputsSafe left candidates)
    (hvalues : PrivateValuesLE left right) :
    CandidateOutputsSafe right candidates := by
  intro candidate hcandidate
  have hsafeCandidate := hsafe candidate hcandidate
  cases hcoordinate : candidate.coordinate with
  | chainStart lay tree leafIdx chainIdx => trivial
  | position position =>
      simp only [hcoordinate] at hsafeCandidate ⊢
      obtain ⟨output, houtput, hne⟩ := hsafeCandidate
      exact ⟨output, hvalues position output houtput, hne⟩

noncomputable def prepareCandidateGroups : Nat → List Probe → DeferredContext →
    ProbComp (Option DeferredContext)
  | 0, _, context => pure (some context)
  | _ + 1, [], context => pure (some context)
  | fuel + 1, candidate :: remaining, context =>
      match candidate.coordinate with
      | .chainStart _ _ _ _ => prepareCandidateGroups fuel remaining context
      | .position target => do
          let resolved ← resolveDeferredPositionValue target context
          match resolved with
          | none => pure none
          | some resolved =>
              if candidateListHits target (candidate :: remaining) resolved.output then
                pure none
              else
                prepareCandidateGroups fuel
                  (removeTargetCandidates target (candidate :: remaining))
                  resolved.toDeferredContext

noncomputable def prepareCandidateList
    (candidates : List Probe) (context : DeferredContext) :
    ProbComp (Option DeferredContext) :=
  prepareCandidateGroups candidates.length candidates context

set_option maxRecDepth 100000 in
theorem evalDist_isNone_prepareCandidateGroups_eq_fire
    (fuel : Nat) (candidates : List Probe) (context : DeferredContext) :
    evalDist (Option.isNone <$> prepareCandidateGroups fuel candidates context) =
      evalDist (resolvedCandidateGroupsFire fuel candidates context) := by
  induction fuel generalizing candidates context with
  | zero => simp [prepareCandidateGroups, resolvedCandidateGroupsFire]
  | succ fuel ih =>
      cases candidates with
      | nil => simp [prepareCandidateGroups, resolvedCandidateGroupsFire]
      | cons candidate remaining =>
          cases hcoordinate : candidate.coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              simp only [prepareCandidateGroups, resolvedCandidateGroupsFire, hcoordinate]
              exact ih remaining context
          | position target =>
              simp only [prepareCandidateGroups, resolvedCandidateGroupsFire, hcoordinate,
                map_eq_bind_pure_comp, bind_assoc]
              apply evalDist_bind_congr
              intro resolved _hresolved
              cases resolved with
              | none => simp
              | some resolved =>
                  by_cases hhit : candidateListHits target (candidate :: remaining) resolved.output
                  · simp [hhit]
                  · simp only [hhit, ↓reduceIte]
                    exact ih (removeTargetCandidates target (candidate :: remaining))
                      resolved.toDeferredContext

theorem evalDist_isNone_prepareCandidateList_eq_fire
    (candidates : List Probe) (context : DeferredContext) :
    evalDist (Option.isNone <$> prepareCandidateList candidates context) =
      evalDist (resolvedCandidateListFire candidates context) :=
  evalDist_isNone_prepareCandidateGroups_eq_fire candidates.length candidates context

theorem privateValuesLE_install_fresh
    (context : DeferredContext) (target : Position) (output : HashOutput)
    (hfresh : context.values target = none) :
    PrivateValuesLE context
      { state := context.state.clearPending (.position target)
        values := context.values.install target output } := by
  intro position value hvalue
  have hne : position ≠ target := by
    intro heq
    subst position
    rw [hfresh] at hvalue
    contradiction
  simpa [DeferredStructuralValues.install, Function.update_of_ne hne] using hvalue

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem preparedCandidateGroups_safe
    (fuel : Nat) (candidates : List Probe) (context finalContext : DeferredContext)
    (hlength : candidates.length ≤ fuel)
    (hfresh : CandidateCoordinatesFresh context candidates)
    (hresult : some finalContext ∈ support
      (prepareCandidateGroups fuel candidates context)) :
    PrivateValuesLE context finalContext ∧
      CandidateOutputsSafe finalContext candidates := by
  induction fuel generalizing candidates context finalContext with
  | zero =>
      have hcandidates : candidates = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst candidates
      simp [prepareCandidateGroups] at hresult
      subst finalContext
      exact ⟨PrivateValuesLE.refl context, by simp [CandidateOutputsSafe]⟩
  | succ fuel ih =>
      cases candidates with
      | nil =>
          simp [prepareCandidateGroups] at hresult
          subst finalContext
          exact ⟨PrivateValuesLE.refl context, by simp [CandidateOutputsSafe]⟩
      | cons candidate remaining =>
          cases hcoordinate : candidate.coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              simp only [prepareCandidateGroups, hcoordinate] at hresult
              have htailFresh : CandidateCoordinatesFresh context remaining :=
                ⟨hfresh.1, fun next hnext =>
                  hfresh.2 next (List.mem_cons_of_mem candidate hnext)⟩
              obtain ⟨hvalues, hsafe⟩ :=
                ih remaining context finalContext (by simpa using hlength) htailFresh hresult
              refine ⟨hvalues, ?_⟩
              intro next hnext
              simp only [List.mem_cons] at hnext
              rcases hnext with rfl | hnext
              · simp [hcoordinate]
              · exact hsafe next hnext
          | position target =>
              have htargetFresh := hfresh.2 candidate (by simp)
              simp only [hcoordinate] at htargetFresh
              rw [prepareCandidateGroups, hcoordinate, mem_support_bind_iff] at hresult
              obtain ⟨resolvedOption, hresolved, htail⟩ := hresult
              cases resolvedOption with
              | none => simp at htail
              | some resolved =>
                  have hnoHit : ∀ output,
                      ¬context.state.hitAt (.position target) output := fun output =>
                    not_hitAt_of_pending_eq_empty context (.position target) output hfresh.1
                  rw [resolveDeferredPositionValue_fresh target context htargetFresh.1
                    htargetFresh.2, mem_support_bind_iff] at hresolved
                  obtain ⟨sampledOutput, _hsampledOutput, hresolved⟩ := hresolved
                  simp [hnoHit sampledOutput] at hresolved
                  subst resolved
                  by_cases hhit :
                      candidateListHits target (candidate :: remaining) sampledOutput
                  · simp [hhit] at htail
                  · simp only [hhit, ↓reduceIte] at htail
                    let rest := removeTargetCandidates target (candidate :: remaining)
                    have hheadTarget : candidateTargets target candidate = true := by
                      simp [candidateTargets, hcoordinate]
                    have hcountPositive :
                        1 ≤ candidateTargetCount target (candidate :: remaining) := by
                      simp [candidateTargetCount, hheadTarget]
                    have hrestLength : rest.length ≤ fuel := by
                      have hpartition :=
                        candidateTargetCount_add_removeTargetCandidates_length target
                          (candidate :: remaining)
                      dsimp only [rest]
                      omega
                    have hrestFresh := candidateCoordinatesFresh_remove_resolved context
                      candidate remaining target sampledOutput hfresh
                    obtain ⟨hrestValues, hrestSafe⟩ := ih
                      rest
                      { state := context.state.clearPending (.position target)
                        values := context.values.install target sampledOutput }
                      finalContext hrestLength hrestFresh htail
                    have hresolvedValues : PrivateValuesLE context
                        { state := context.state.clearPending (.position target)
                          values := context.values.install target sampledOutput } :=
                      privateValuesLE_install_fresh context target sampledOutput htargetFresh.2
                    refine ⟨hresolvedValues.trans hrestValues, ?_⟩
                    intro next hnext
                    cases hnextCoordinate : next.coordinate with
                    | chainStart nextLay nextTree nextLeaf nextChain => trivial
                    | position other =>
                        by_cases heq : other = target
                        · subst other
                          have htargetValue :
                              (context.values.install target sampledOutput) target =
                                some sampledOutput := by
                            simp [DeferredStructuralValues.install]
                          have hfinalTarget := hrestValues target sampledOutput htargetValue
                          refine ⟨sampledOutput, hfinalTarget, ?_⟩
                          intro heqDigest
                          apply hhit
                          exact candidateListHits_of_mem target sampledOutput next
                            (candidate :: remaining) hnext (by simpa using hnextCoordinate)
                            heqDigest.symm
                        · have hnextRest : next ∈ removeTargetCandidates target
                              (candidate :: remaining) := by
                            unfold removeTargetCandidates
                            apply List.mem_filter.mpr
                            refine ⟨hnext, ?_⟩
                            simp [candidateTargets, hnextCoordinate, heq]
                          simpa [hnextCoordinate] using hrestSafe next hnextRest

theorem preparedCandidateList_safe
    (candidates : List Probe) (context finalContext : DeferredContext)
    (hfresh : CandidateCoordinatesFresh context candidates)
    (hresult : some finalContext ∈ support (prepareCandidateList candidates context)) :
    PrivateValuesLE context finalContext ∧ CandidateOutputsSafe finalContext candidates :=
  preparedCandidateGroups_safe candidates.length candidates context finalContext le_rfl hfresh
    hresult

theorem not_recordedCandidateHit_of_prepared_run
    (candidates : List Probe) (context prepared : DeferredContext)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (result : ResolvedRunResult α)
    (hfresh : CandidateCoordinatesFresh context candidates)
    (hprepared : some prepared ∈ support (prepareCandidateList candidates context))
    (hresult : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable prepared fuel table computation)) :
    ¬RecordedCandidateHit result.context candidates := by
  obtain ⟨_hcontextValues, hsafe⟩ :=
    preparedCandidateList_safe candidates context prepared hfresh hprepared
  have hvalues := privateValuesLE_of_done_runDirectResolvedDetailedFromTable
    computation prepared fuel table result hresult
  exact not_recordedCandidateHit_of_candidateOutputsSafe result.context candidates
    (hsafe.of_privateValuesLE hvalues)

theorem probEvent_prepareCandidateList_empty_none_le (candidates : List Probe) :
    Pr[= none | prepareCandidateList candidates
      { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
        values := emptyDeferredStructuralValues }] ≤
      (candidates.length : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  let initial : DeferredContext :=
    { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
      values := emptyDeferredStructuralValues }
  calc
    _ = Pr[fun result : Option DeferredContext => Option.isNone result = true |
          prepareCandidateList candidates initial] := by
      rw [← probEvent_eq_eq_probOutput]
      apply OracleComp.probEvent_congr' (fun result _ => by cases result <;> simp) rfl
    _ = Pr[= true | Option.isNone <$> prepareCandidateList candidates initial] := by
      rw [← probEvent_eq_eq_probOutput, probEvent_map]
      rfl
    _ = Pr[= true | resolvedCandidateListFire candidates initial] :=
      OracleComp.probOutput_congr rfl
        (evalDist_isNone_prepareCandidateList_eq_fire candidates initial)
    _ ≤ _ := probEvent_resolvedCandidateListFire_empty_le candidates

end SphincsSecurity.Concrete.OtsProbeSimulation

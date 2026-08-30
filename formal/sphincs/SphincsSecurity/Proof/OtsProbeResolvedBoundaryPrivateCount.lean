import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateTrace

/-!
# Planned-probe count

The proof-only plan trace appends at most one candidate at an outer hash query and appends none at uniform or signing queries. Consequently every supported trace contains at most the source computation's outer hash-query budget many new candidates.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

theorem appendPlannedCandidate_length_le (candidates : List Probe)
    (planned : Option Probe) :
    (appendPlannedCandidate candidates planned).length ≤ candidates.length + 1 := by
  cases planned <;> simp [appendPlannedCandidate]

theorem maskedExpandedAdversaryPlanner_none_of_not_outer
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (query : (OracleWorld + SigningSpec).Domain)
    (hquery : ¬IsOuterHash query) :
    maskedExpandedAdversaryPlanner parameter root ftsSecret query = pure none := by
  cases query with
  | inl worldQuery =>
      cases worldQuery with
      | inl n => rfl
      | inr input => simp [IsOuterHash] at hquery
  | inr message => rfl

theorem support_finishDirectDetailedPrivatePlanObserve_length_le
    (observe : DeferredContext → Nat → α → List Probe → ProbComp (Bool × List Probe))
    (candidates : List Probe) (result : DirectDetailedResult α) (bound : Nat)
    (hobserve : ∀ context fuel value candidates output,
      output ∈ support (observe context fuel value candidates) →
      output.2.length ≤ candidates.length + bound)
    (output : Bool × List Probe)
    (houtput : output ∈ support
      (finishDirectDetailedPrivatePlanObserve observe candidates result)) :
    output.2.length ≤ candidates.length + bound := by
  cases result with
  | stopped reason =>
      cases reason <;>
        simp [finishDirectDetailedPrivatePlanObserve] at houtput <;>
        subst output <;> simp
  | done result =>
      exact hobserve result.context result.remaining result.value candidates output houtput

theorem support_classifyDirectDetailedPrivatePlanObserve_length_le
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List Probe → ProbComp (Bool × List Probe))
    (context : DeferredContext) (fuel : Nat) (value : α)
    (candidates : List Probe) (bound : Nat)
    (hobserve : ∀ nextContext remaining nextValue nextCandidates output,
      output ∈ support (observe nextContext remaining nextValue nextCandidates) →
      output.2.length ≤ nextCandidates.length + bound)
    (output : Bool × List Probe)
    (houtput : output ∈ support
      (classifyDirectDetailedPrivatePlanObserve table observe context fuel value candidates)) :
    output.2.length ≤ candidates.length + bound := by
  unfold classifyDirectDetailedPrivatePlanObserve at houtput
  by_cases hprivate : PrivateStructuralHit context
  · simp [hprivate] at houtput
    subst output
    simp
  · simp only [hprivate, ↓reduceIte] at houtput
    by_cases hcompletable : DeferredCompletable table context
    · simp only [hcompletable, ↓reduceIte] at houtput
      exact hobserve context fuel value candidates output houtput
    · simp [hcompletable] at houtput
      subst output
      simp

theorem support_canonicalizeDirectDetailedPrivatePlanObserve_length_le
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List Probe → ProbComp (Bool × List Probe))
    (context : DeferredContext) (fuel : Nat) (value : α)
    (candidates : List Probe) (bound : Nat)
    (hobserve : ∀ nextContext remaining nextValue nextCandidates output,
      output ∈ support (observe nextContext remaining nextValue nextCandidates) →
      output.2.length ≤ nextCandidates.length + bound)
    (output : Bool × List Probe)
    (houtput : output ∈ support
      (canonicalizeDirectDetailedPrivatePlanObserve table observe
        context fuel value candidates)) :
    output.2.length ≤ candidates.length + bound := by
  unfold canonicalizeDirectDetailedPrivatePlanObserve at houtput
  by_cases hprivate : PrivateStructuralHit (canonicalizeMaterializedValues table context)
  · simp [hprivate] at houtput
    subst output
    simp
  · simp only [hprivate, ↓reduceIte] at houtput
    by_cases hpublished : PublishedValues context.state
    · simp only [hpublished, ↓reduceIte] at houtput
      exact support_classifyDirectDetailedPrivatePlanObserve_length_le table observe
        (canonicalizeMaterializedValues table context) fuel value candidates bound hobserve
        output houtput
    · simp [hpublished] at houtput
      subst output
      simp

theorem support_runDirectDetailedPrivatePlanObserve_length_le
    (observe : DeferredContext → Nat → α → List Probe → ProbComp (Bool × List Probe))
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (bound : Nat)
    (hobserve : ∀ nextContext remaining value nextCandidates output,
      output ∈ support (observe nextContext remaining value nextCandidates) →
      output.2.length ≤ nextCandidates.length + bound)
    (output : Bool × List Probe)
    (houtput : output ∈ support
      (runDirectDetailedPrivatePlanObserve observe candidates context fuel table computation)) :
    output.2.length ≤ candidates.length + bound := by
  unfold runDirectDetailedPrivatePlanObserve at houtput
  rw [mem_support_bind_iff] at houtput
  obtain ⟨result, hresult, houtput⟩ := houtput
  exact support_finishDirectDetailedPrivatePlanObserve_length_le observe candidates result bound
    hobserve output houtput

set_option maxRecDepth 100000 in
theorem support_directDetailedBoundaryPrivatePlanObserve_length_le
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) →
      List Probe → ProbComp (Bool × List Probe))
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) (q : Nat)
    (hbound : computation.IsQueryBoundP IsOuterHash q)
    (hobserve : ∀ nextContext remaining value nextCandidates output,
      output ∈ support (observe nextContext remaining value nextCandidates) →
      output.2.length ≤ nextCandidates.length)
    (output : Bool × List Probe)
    (houtput : output ∈ support
      (directDetailedBoundaryPrivatePlanObserve
        (maskedExpandedAdversaryImpl parameter root ftsSecret)
        (maskedExpandedAdversaryPlanner parameter root ftsSecret)
        computation observe candidates context fuel table cache)) :
    output.2.length ≤ candidates.length + q := by
  induction computation using OracleComp.inductionOn generalizing candidates context fuel cache q output with
  | pure value =>
      simp only [directDetailedBoundaryPrivatePlanObserve,
        OracleComp.construct_pure] at houtput
      exact (hobserve context fuel (value, cache) candidates output houtput).trans
        (Nat.le_add_right candidates.length q)
  | query_bind query next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [directDetailedBoundaryPrivatePlanObserve,
        OracleComp.construct_query_bind, mem_support_bind_iff] at houtput
      obtain ⟨plannedResult, hplanned, houtput⟩ := houtput
      cases plannedResult with
      | stopped reason =>
          simp at houtput
          subst output
          simp
      | done plannedResult =>
          let nextCandidates := appendPlannedCandidate candidates plannedResult.value.1
          have htail : output.2.length ≤ nextCandidates.length +
              (if IsOuterHash query then q - 1 else q) := by
            apply support_runDirectDetailedPrivatePlanObserve_length_le
              (canonicalizeDirectDetailedPrivatePlanObserve table
                (fun nextContext remaining value nextCandidates =>
                  directDetailedBoundaryPrivatePlanObserve
                    (maskedExpandedAdversaryImpl parameter root ftsSecret)
                    (maskedExpandedAdversaryPlanner parameter root ftsSecret)
                    (next value.1) observe nextCandidates nextContext remaining table value.2))
              nextCandidates plannedResult.context plannedResult.remaining table
              ((maskedExpandedAdversaryImpl parameter root ftsSecret query).run
                plannedResult.value.2)
              (if IsOuterHash query then q - 1 else q)
            · intro nextContext remaining value laterCandidates laterOutput hlater
              exact support_canonicalizeDirectDetailedPrivatePlanObserve_length_le table _
                nextContext remaining value laterCandidates
                (if IsOuterHash query then q - 1 else q)
                (by
                  intro canonicalContext canonicalRemaining
                    (canonicalValue :
                      (OracleWorld + SigningSpec).Range query × SplitHashCache)
                    canonicalCandidates canonicalOutput hcanonicalOutput
                  exact ih canonicalValue.1
                    (candidates := canonicalCandidates) (context := canonicalContext)
                    (fuel := canonicalRemaining) (cache := canonicalValue.2)
                    (q := if IsOuterHash query then q - 1 else q)
                    (output := canonicalOutput) (hbound.2 canonicalValue.1)
                    hcanonicalOutput)
                laterOutput hlater
            · exact houtput
          by_cases hquery : IsOuterHash query
          · have hpositive : 0 < q := by
              rcases hbound.1 with hnot | hpositive
              · exact (hnot hquery).elim
              · exact hpositive
            have hnextLength : nextCandidates.length ≤ candidates.length + 1 :=
              appendPlannedCandidate_length_le candidates plannedResult.value.1
            simp only [hquery, ↓reduceIte] at htail
            omega
          · have hplanner : maskedExpandedAdversaryPlanner parameter root ftsSecret query =
                pure none :=
              maskedExpandedAdversaryPlanner_none_of_not_outer parameter root ftsSecret query
                hquery
            have hplannedNone : plannedResult.value.1 = none := by
              have hdirect := mem_support_runDirectResolvedFromTable_of_done_detailed
                ((maskedExpandedAdversaryPlanner parameter root ftsSecret query).run cache)
                context fuel table plannedResult hplanned
              rw [hplanner, StateT.run_pure] at hdirect
              have hraw := raw_done_of_mem_runDirectResolvedFromTable
                ((pure none : StateT SplitHashCache
                  (OracleComp (LazyRevealProbe.World Coordinate)) (Option Probe)).run cache)
                context fuel table plannedResult hdirect
              simp [LazyRevealProbe.runRaw] at hraw
              exact congrArg Prod.fst hraw.2.2
            simp only [hquery, ↓reduceIte] at htail
            simp [nextCandidates, hplannedNone, appendPlannedCandidate] at htail ⊢
            exact htail

theorem support_retainedResolvedFinalizationPrivatePlanObserve_length_le
    (table : OtsSecretIndex → HashOutput) (root : Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : RetainedRestResult × SplitHashCache) (candidates : List Probe)
    (output : Bool × List Probe)
    (houtput : output ∈ support
      (retainedResolvedFinalizationPrivatePlanObserve table root context fuel value candidates)) :
    output.2.length ≤ candidates.length := by
  unfold retainedResolvedFinalizationPrivatePlanObserve at houtput
  rw [mem_support_bind_iff] at houtput
  obtain ⟨hit, _hhit, houtput⟩ := houtput
  simp at houtput
  subst output
  simp

set_option maxRecDepth 100000 in
theorem support_granularDetailedRetainedRestPrivatePlanObserve_length_le
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (candidates : List Probe) (q : Nat)
    (hbound : (retainedGameRestComputation adversary ⟨value.1, parameter⟩).IsQueryBoundP
      IsOuterHash q)
    (output : Bool × List Probe)
    (houtput : output ∈ support
      (granularDetailedRetainedRestPrivatePlanObserve adversary parameter table ftsSecret
        context fuel value candidates)) :
    output.2.length ≤ candidates.length + q := by
  unfold granularDetailedRetainedRestPrivatePlanObserve at houtput
  exact support_directDetailedBoundaryPrivatePlanObserve_length_le parameter value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
    (retainedResolvedFinalizationPrivatePlanObserve table value.1)
    candidates context fuel table value.2 q hbound
    (support_retainedResolvedFinalizationPrivatePlanObserve_length_le table value.1)
    output houtput

end SphincsSecurity.Concrete.OtsProbeSimulation

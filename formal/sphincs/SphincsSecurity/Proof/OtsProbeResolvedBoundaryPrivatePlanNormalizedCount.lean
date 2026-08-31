import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivatePlanNormalized

/-!
# Normalized plan count

The normalized trace appends one optional candidate exactly at an outer hash query, so its supported final lists are bounded by the source computation's `IsOuterHash` budget.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem support_directDetailedBoundaryNormalizedPrivatePlanObserve_length_le
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
      (directDetailedBoundaryNormalizedPrivatePlanObserve parameter root ftsSecret computation
        observe candidates context fuel table cache)) :
    output.2.length ≤ candidates.length + q := by
  induction computation using OracleComp.inductionOn generalizing candidates context fuel cache q output with
  | pure value =>
      simp only [directDetailedBoundaryNormalizedPrivatePlanObserve,
        OracleComp.construct_pure] at houtput
      exact (hobserve context fuel (value, cache) candidates output houtput).trans
        (Nat.le_add_right candidates.length q)
  | query_bind query next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [directDetailedBoundaryNormalizedPrivatePlanObserve,
        OracleComp.construct_query_bind] at houtput
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              have htail : output.2.length ≤ candidates.length + q := by
                apply support_runDirectDetailedPrivatePlanObserve_length_le
                  (canonicalizeDirectDetailedPrivatePlanObserve table
                    (fun nextContext remaining value nextCandidates =>
                      directDetailedBoundaryNormalizedPrivatePlanObserve parameter root ftsSecret
                        (next value.1) observe nextCandidates nextContext remaining table value.2))
                  candidates context fuel table ((splitUniformImpl n).run cache) q
                · intro nextContext remaining value nextCandidates nextOutput hnextOutput
                  exact support_canonicalizeDirectDetailedPrivatePlanObserve_length_le table _
                    nextContext remaining value nextCandidates q
                    (by
                      intro finalContext finalRemaining
                        (finalValue : Fin (n + 1) × SplitHashCache)
                        finalCandidates finalOutput hfinalOutput
                      exact ih finalValue.1 finalCandidates finalContext finalRemaining
                        finalValue.2 (q := q)
                        (by simpa [IsOuterHash] using hbound.2 finalValue.1)
                        (output := finalOutput) hfinalOutput)
                    nextOutput hnextOutput
                · exact houtput
              exact htail
          | inr input =>
              let plan := purePlanProbingHashQuery parameter input context.state
              let nextCandidates := appendPlannedCandidate candidates plan.candidate?
              have hpositive : 0 < q := by
                rcases hbound.1 with hnot | hpositive
                · exact (hnot (by simp [IsOuterHash])).elim
                · exact hpositive
              have htail : output.2.length ≤ nextCandidates.length + (q - 1) := by
                apply support_runDirectDetailedPrivatePlanObserve_length_le
                  (canonicalizeDirectDetailedPrivatePlanObserve table
                    (fun nextContext remaining value finalCandidates =>
                      directDetailedBoundaryNormalizedPrivatePlanObserve parameter root ftsSecret
                        (next value.1) observe finalCandidates nextContext remaining table value.2))
                  nextCandidates context fuel table
                    ((probingHashQueryAfterPlan parameter input plan).run cache) (q - 1)
                · intro nextContext remaining value finalCandidates nextOutput hnextOutput
                  exact support_canonicalizeDirectDetailedPrivatePlanObserve_length_le table _
                    nextContext remaining value finalCandidates (q - 1)
                    (by
                      intro finalContext finalRemaining
                        (finalValue : HashOutput × SplitHashCache)
                        laterCandidates finalOutput hfinalOutput
                      exact ih finalValue.1 laterCandidates finalContext finalRemaining
                        finalValue.2 (q := q - 1)
                        (by simpa [IsOuterHash] using hbound.2 finalValue.1)
                        (output := finalOutput) hfinalOutput)
                    nextOutput hnextOutput
                · exact houtput
              have hnextLength : nextCandidates.length ≤ candidates.length + 1 :=
                appendPlannedCandidate_length_le candidates plan.candidate?
              omega
      | inr message =>
          have htail : output.2.length ≤ candidates.length + q := by
            apply support_runDirectDetailedPrivatePlanObserve_length_le
              (canonicalizeDirectDetailedPrivatePlanObserve table
                (fun nextContext remaining value nextCandidates =>
                  directDetailedBoundaryNormalizedPrivatePlanObserve parameter root ftsSecret
                    (next value.1) observe nextCandidates nextContext remaining table value.2))
              candidates context fuel table ((maskedSign parameter root ftsSecret message).run cache) q
            · intro nextContext remaining value nextCandidates nextOutput hnextOutput
              exact support_canonicalizeDirectDetailedPrivatePlanObserve_length_le table _
                nextContext remaining value nextCandidates q
                (by
                  intro finalContext finalRemaining
                    (finalValue : Option Signature × SplitHashCache)
                    finalCandidates finalOutput hfinalOutput
                  exact ih finalValue.1 finalCandidates finalContext finalRemaining finalValue.2
                    (q := q) (by simpa [IsOuterHash] using hbound.2 finalValue.1)
                    (output := finalOutput) hfinalOutput)
                nextOutput hnextOutput
            · exact houtput
          exact htail

theorem support_retainedResolvedFinalizationPrivatePlanObserve_length_le_zero
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

theorem support_granularDetailedRetainedRestNormalizedPrivatePlanObserve_length_le
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (candidates : List Probe) (q : Nat)
    (hbound : (retainedGameRestComputation adversary ⟨value.1, parameter⟩).IsQueryBoundP
      IsOuterHash q)
    (output : Bool × List Probe)
    (houtput : output ∈ support
      (granularDetailedRetainedRestNormalizedPrivatePlanObserve adversary parameter table
        ftsSecret context fuel value candidates)) :
    output.2.length ≤ candidates.length + q := by
  unfold granularDetailedRetainedRestNormalizedPrivatePlanObserve at houtput
  exact support_directDetailedBoundaryNormalizedPrivatePlanObserve_length_le parameter value.1
    ftsSecret (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
    (retainedResolvedFinalizationPrivatePlanObserve table value.1)
    candidates context fuel table value.2 q hbound
    (support_retainedResolvedFinalizationPrivatePlanObserve_length_le_zero table value.1)
    output houtput

end SphincsSecurity.Concrete.OtsProbeSimulation

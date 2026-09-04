import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivatePlanNormalized
import SphincsSecurity.Proof.OtsProbeResolvedAdaptiveClean
import SphincsSecurity.Proof.DirectQueryBudget

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
              let nextCandidates := appendPlannedCandidate candidates
                (rootAwarePlannedCandidate? parameter input context.state)
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
                appendPlannedCandidate_length_le candidates
                  (rootAwarePlannedCandidate? parameter input context.state)
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

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem support_directDetailedBoundaryNormalizedPrivatePlanObserve_length_le_of_expanded
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) →
      List Probe → ProbComp (Bool × List Probe))
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) (q : Nat)
    (hbound :
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        computation).IsQueryBoundP (fun query => query matches Sum.inr _) q)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hobserve : ∀ nextContext remaining value nextCandidates output,
      output ∈ support (observe nextContext remaining value nextCandidates) →
      output.2.length ≤ nextCandidates.length)
    (output : Bool × List Probe)
    (houtput : output ∈ support
      (directDetailedBoundaryNormalizedPrivatePlanObserve parameter root ftsSecret computation
        observe candidates context fuel table cache)) :
    output.2.length ≤ candidates.length + q := by
  induction computation using OracleComp.inductionOn generalizing
      candidates context fuel cache q output with
  | pure value =>
      simp only [directDetailedBoundaryNormalizedPrivatePlanObserve,
        OracleComp.construct_pure] at houtput
      exact (hobserve context fuel (value, cache) candidates output houtput).trans
        (Nat.le_add_right candidates.length q)
  | query_bind query next ih =>
      rw [directDetailedBoundaryNormalizedPrivatePlanObserve,
        OracleComp.construct_query_bind] at houtput
      cases query with
      | inl worldQuery =>
          rw [SphincsSecurity.simulateQ_expandedAdversaryImpl_query_bind_inl,
            OracleComp.isQueryBoundP_query_bind_iff] at hbound
          cases worldQuery with
          | inl n =>
              apply support_runDirectDetailedPrivatePlanObserve_length_le_of_done
                (canonicalizeDirectDetailedPrivatePlanObserve table
                  (fun nextContext remaining value nextCandidates =>
                    directDetailedBoundaryNormalizedPrivatePlanObserve parameter root ftsSecret
                      (next value.1) observe nextCandidates nextContext remaining table value.2))
                candidates context fuel table ((splitUniformImpl n).run cache) q
              · intro result hresult nextOutput hnextOutput
                have hcore :=
                  resolvedCore_of_done_runDirectResolvedDetailedFromTable_for_count
                    ((splitUniformImpl n).run cache) context fuel table result hconsistent hstarts
                    hresult
                exact support_canonicalizeDirectDetailedPrivatePlanObserve_length_le_at table _
                  result.context result.remaining result.value candidates q
                  (by
                    intro finalOutput hfinalOutput
                    exact ih result.value.1 candidates
                      (canonicalizeMaterializedValues table result.context) result.remaining
                      result.value.2 (q := q) (hbound.2 result.value.1)
                      (canonicalizeMaterializedValues_valuesConsistent table result.context
                        hcore.2.1)
                      (canonicalizeMaterializedValues_startTableAgrees table result.context)
                      (output := finalOutput) hfinalOutput)
                  nextOutput hnextOutput
              · exact houtput
          | inr input =>
              let plan := purePlanProbingHashQuery parameter input context.state
              let nextCandidates := appendPlannedCandidate candidates
                (rootAwarePlannedCandidate? parameter input context.state)
              have hpositive : 0 < q := by
                rcases hbound.1 with hnot | hpositive
                · exact (hnot (by simp)).elim
                · exact hpositive
              have htail : output.2.length ≤ nextCandidates.length + (q - 1) := by
                apply support_runDirectDetailedPrivatePlanObserve_length_le_of_done
                  (canonicalizeDirectDetailedPrivatePlanObserve table
                    (fun nextContext remaining value finalCandidates =>
                      directDetailedBoundaryNormalizedPrivatePlanObserve parameter root ftsSecret
                        (next value.1) observe finalCandidates nextContext remaining table value.2))
                  nextCandidates context fuel table
                    ((probingHashQueryAfterPlan parameter input plan).run cache) (q - 1)
                · intro result hresult nextOutput hnextOutput
                  have hcore := resolvedCore_of_done_runDirectResolvedDetailedFromTable_for_count
                    ((probingHashQueryAfterPlan parameter input plan).run cache)
                    context fuel table result hconsistent hstarts hresult
                  exact support_canonicalizeDirectDetailedPrivatePlanObserve_length_le_at table _
                    result.context result.remaining result.value nextCandidates (q - 1)
                    (by
                      intro finalOutput hfinalOutput
                      exact ih result.value.1 nextCandidates
                        (canonicalizeMaterializedValues table result.context) result.remaining
                        result.value.2 (q := q - 1) (hbound.2 result.value.1)
                        (canonicalizeMaterializedValues_valuesConsistent table result.context
                          hcore.2.1)
                        (canonicalizeMaterializedValues_startTableAgrees table result.context)
                        (output := finalOutput) hfinalOutput)
                    nextOutput hnextOutput
                · exact houtput
              have hnextLength : nextCandidates.length ≤ candidates.length + 1 :=
                appendPlannedCandidate_length_le candidates
                  (rootAwarePlannedCandidate? parameter input context.state)
              omega
      | inr message =>
          rw [SphincsSecurity.simulateQ_expandedAdversaryImpl_query_bind_inr] at hbound
          apply support_runDirectDetailedPrivatePlanObserve_length_le_of_done
            (canonicalizeDirectDetailedPrivatePlanObserve table
              (fun nextContext remaining value nextCandidates =>
                directDetailedBoundaryNormalizedPrivatePlanObserve parameter root ftsSecret
                  (next value.1) observe nextCandidates nextContext remaining table value.2))
            candidates context fuel table ((maskedSign parameter root ftsSecret message).run cache) q
          · intro result hresult nextOutput hnextOutput
            have hcore := resolvedCore_of_done_runDirectResolvedDetailedFromTable_for_count
              ((maskedSign parameter root ftsSecret message).run cache)
              context fuel table result hconsistent hstarts hresult
            have hdirect : some result ∈ support
                (runDirectResolvedFromTable context fuel table
                  ((maskedSign parameter root ftsSecret message).run cache)) :=
              mem_support_runDirectResolvedFromTable_of_done_detailed
                ((maskedSign parameter root ftsSecret message).run cache)
                context fuel table result hresult
            have hraw := raw_done_of_mem_runDirectResolvedFromTable
              ((maskedSign parameter root ftsSecret message).run cache)
              context fuel table result hdirect
            have hsign : result.value.1 ∈ support
                (scheme.sign
                  (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
                    SecretKey) message) := by
              exact maskedSign_done_output_mem_support parameter root table ftsSecret message
                context.state result.context.state cache result.value.2 fuel result.remaining
                result.value.1 hcore.2.2 (by
                  simpa only [SigningSpec, maskedExpandedAdversaryImpl, maskedSigningImpl]
                    using hraw)
            have htailBound := isQueryBoundP_of_bind hbound result.value.1 hsign
            exact support_canonicalizeDirectDetailedPrivatePlanObserve_length_le_at table _
              result.context result.remaining result.value candidates q
              (by
                intro finalOutput hfinalOutput
                exact ih result.value.1 candidates
                  (canonicalizeMaterializedValues table result.context) result.remaining
                  result.value.2
                  (q := q) htailBound
                  (canonicalizeMaterializedValues_valuesConsistent table result.context
                    hcore.2.1)
                  (canonicalizeMaterializedValues_startTableAgrees table result.context)
                  (output := finalOutput) hfinalOutput)
              nextOutput hnextOutput
          · exact houtput

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

theorem support_granularDetailedRetainedRestNormalizedPrivatePlanObserve_length_le_of_expanded
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (candidates : List Probe) (q : Nat)
    (hbound :
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, value.1, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
            SecretKey))
        (retainedGameRestComputation adversary ⟨value.1, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (output : Bool × List Probe)
    (houtput : output ∈ support
      (granularDetailedRetainedRestNormalizedPrivatePlanObserve adversary parameter table
        ftsSecret context fuel value candidates)) :
    output.2.length ≤ candidates.length + q := by
  unfold granularDetailedRetainedRestNormalizedPrivatePlanObserve at houtput
  exact support_directDetailedBoundaryNormalizedPrivatePlanObserve_length_le_of_expanded
    parameter value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
    (retainedResolvedFinalizationPrivatePlanObserve table value.1)
    candidates context fuel table value.2 q hbound hconsistent hstarts
    (support_retainedResolvedFinalizationPrivatePlanObserve_length_le_zero table value.1)
    output houtput

end SphincsSecurity.Concrete.OtsProbeSimulation

import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeChargedRootObservation
import SphincsSecurity.Proof.OtsProbeNativeRootHistoryTraceSampling

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem nativeTrace_storedRoot_facts
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (target : Position) (output : HashOutput) (result : ResolvedRunResult (α × SplitHashCache)) (history : List CanonicalQuerySelection)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hknown : context.positionValue target = some output)
    (htrace : (some result, history) ∈ support (runNativeQueryTrace parameter root ftsSecret computation context fuel table cache)) :
    result.table = table ∧ result.context.ValuesConsistent ∧ StartTableAgrees result.context.state table ∧
      DeferredCompletable table result.context ∧ result.context.positionValue target = some output := by
  induction computation using OracleComp.inductionOn generalizing context fuel table cache history with
  | pure value =>
      simp only [runNativeQueryTrace, OracleComp.construct_pure] at htrace
      split_ifs at htrace with hcomplete <;> simp only [mem_support_pure_iff, Prod.mk.injEq, Option.some.injEq] at htrace
      · obtain ⟨rfl, _⟩ := htrace
        exact ⟨rfl, hconsistent, hstarts, hcomplete, hknown⟩
      · simp at htrace
  | query_bind input next ih =>
      rw [runNativeQueryTrace_query_bind] at htrace
      by_cases hcomplete : DeferredCompletable table context
      · rw [if_pos hcomplete, mem_support_bind_iff] at htrace
        obtain ⟨middle, hmiddle, htail⟩ := htrace
        cases middle with
        | none => simp at htail
        | some middle =>
            simp only [mem_support_bind_iff] at htail
            obtain ⟨tail, htail, hreturn⟩ := htail
            simp only [mem_support_pure_iff, Prod.mk.injEq] at hreturn
            have htrace : (some result, tail.2) ∈ support
                (runNativeQueryTrace parameter root ftsSecret (next middle.value.1)
                  middle.context middle.remaining middle.table middle.value.2) := by
              simpa only [hreturn.1] using htail
            have hcore := resolvedCore_of_mem_runResolvedFromTable _ context fuel table middle hconsistent hstarts hmiddle
            have hvalue := positionValue_of_mem_runResolved _ context fuel table middle target output hknown hmiddle
            have hfacts := ih middle.value.1 middle.context middle.remaining middle.table middle.value.2 tail.2
              hcore.2.1 (by rw [hcore.1]; exact hcore.2.2) hvalue htrace
            simpa only [hcore.1] using hfacts
      · rw [if_neg hcomplete] at htrace
        simp at htrace

theorem finishNativeRootHistoryTrace_charged_of_stored
    (parameter : PublicParameter) (root : Digest) (target : Position) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) (OuterQueryCut α))
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (initialHistory : Finset Digest) (event : HashOutput × Option Digest → Prop)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (output : HashOutput) (hknown : context.positionValue target = some output)
    (result : ResolvedRunResult (OuterQueryCut α × SplitHashCache)) (history : List CanonicalQuerySelection)
    (htrace : (some result, history) ∈ support (runNativeQueryTrace parameter root ftsSecret computation context fuel table cache)) :
    finishNativeRootHistoryTrace parameter target table (observeChargedRootCut parameter target event) initialHistory (some result, history) =
      pure (decide (¬(.position target ∉ result.context.state.revealed ∧
        truncateHash output ∉ initialHistory ∪ nativeRootCandidateHistory parameter target history ∧
        event (output, chargedNativeRootCutCandidate parameter target result.context result.value.1)))) := by
  have hfacts := nativeTrace_storedRoot_facts parameter root ftsSecret computation context fuel table cache target output result history
    hconsistent hstarts hknown htrace
  rw [finishNativeRootHistoryTrace,
    privateResolutionObserve_chargedRootCut_of_known parameter target table event _ _ _ _ hfacts.2.1 hfacts.2.2.2.1 output hfacts.2.2.2.2]
  exact observeChargedRootCut_of_known parameter target event result.context result.remaining result.value _ output hfacts.2.2.2.2

end SphincsSecurity.Concrete.OtsProbeSimulation

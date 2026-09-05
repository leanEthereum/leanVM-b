import SphincsSecurity.Proof.OtsProbeSampledJointRootRisk

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem nativeTrace_completion_facts
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (α × SplitHashCache)) (history : List CanonicalQuerySelection)
    (completion : Coordinate → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hresult : (some result, history) ∈ support (runNativeQueryTrace parameter root ftsSecret computation context fuel table cache))
    (hcompletion : DeferredCompletion table result.context completion) :
    DeferredCompletion table context completion ∧
      ∀ selection ∈ history, selection.table = table ∧ selection.context.ValuesConsistent ∧
        DeferredCompletion table selection.context completion ∧ selection.context.state.revealed ⊆ result.context.state.revealed := by
  induction computation using OracleComp.inductionOn generalizing context fuel table cache history with
  | pure value =>
      simp only [runNativeQueryTrace, OracleComp.construct_pure] at hresult
      split_ifs at hresult <;> simp only [mem_support_pure_iff, Prod.mk.injEq, Option.some.injEq] at hresult
      · obtain ⟨rfl, rfl⟩ := hresult
        exact ⟨hcompletion, by simp⟩
      · simp at hresult
  | query_bind input next ih =>
      rw [runNativeQueryTrace_query_bind] at hresult
      by_cases hcomplete : DeferredCompletable table context
      · rw [if_pos hcomplete, mem_support_bind_iff] at hresult
        obtain ⟨middle, hmiddle, htail⟩ := hresult
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
            have hcore := resolvedCore_of_mem_runResolvedFromTable
              ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache)
              context fuel table middle hconsistent hstarts hmiddle
            have htailFacts := ih middle.value.1 middle.context middle.remaining middle.table middle.value.2 tail.2
              hcore.2.1 (by rw [hcore.1]; exact hcore.2.2) htrace (by rw [hcore.1]; exact hcompletion)
            rw [hcore.1] at htailFacts
            have hbefore := DeferredCompletion.of_mem_runResolvedFromTable _ context fuel table middle completion
              hconsistent hstarts hmiddle htailFacts.1
            refine ⟨hbefore, ?_⟩
            intro selection hselection
            rw [hreturn.2] at hselection
            rcases List.mem_cons.mp hselection with rfl | hselection
            · exact ⟨rfl, hconsistent, hbefore,
                (revealed_subset_of_mem_runResolvedFromTable _ context fuel table middle hmiddle).trans
                  (revealed_subset_of_mem_runNativeQueryTrace parameter root ftsSecret _ _ _ _ _ result tail.2 htrace)⟩
            · exact htailFacts.2 selection hselection
      · rw [if_neg hcomplete] at hresult
        simp at hresult

theorem DeferredCompletion.plannedCandidate_ne
    (parameter : PublicParameter) (input : HashInput) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (HashOutput × SplitHashCache))
    (completion : Coordinate → HashOutput) (candidate : Probe)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hcandidate : (purePlanProbingHashQuery parameter input context.state).candidate? = some candidate)
    (hhidden : candidate.coordinate ∉ context.state.revealed)
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table ((probingHashQuery parameter input).run cache)))
    (hcompletion : DeferredCompletion table result.context completion) :
    truncateHash (completion candidate.coordinate) ≠ candidate.candidate := by
  rw [runResolved_probingHashQuery_eq_afterPlan] at hresult
  unfold probingHashQueryAfterPlan executePlannedHashQuery at hresult
  rw [hcandidate] at hresult
  simp only [executeCandidate?] at hresult
  rw [StateT.run_bind, runResolvedFromTable_bind] at hresult
  unfold SphincsSecurity.Concrete.OtsProbeSimulation.probe at hresult
  rw [StateT.run_liftM, LazyRevealProbe.probeQuery,
    runResolvedFromTable_probe_query_bind] at hresult
  cases fuel with
  | zero => simp at hresult
  | succ remaining =>
      simp only [if_neg hhidden] at hresult
      let probeContext : DeferredContext :=
        { context with state := context.state.addPending candidate.coordinate candidate.candidate }
      have hbefore : DeferredCompletion table probeContext completion :=
        hcompletion.of_mem_runResolvedFromTable _ probeContext remaining table result completion
          (hconsistent.addPending candidate.coordinate candidate.candidate)
          (hstarts.addPending candidate.coordinate candidate.candidate) (by
            simpa [probeContext, runResolvedFromTable] using hresult)
      exact hbefore.2.2.1 candidate.coordinate candidate.candidate
        (by simp [probeContext, LazyRevealProbe.State.addPending])

theorem nativeTrace_plannedCandidate_ne
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (α × SplitHashCache)) (history : List CanonicalQuerySelection)
    (completion : Coordinate → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hresult : (some result, history) ∈ support (runNativeQueryTrace parameter root ftsSecret computation context fuel table cache))
    (hcompletion : DeferredCompletion table result.context completion) :
    ∀ selection ∈ history, ∀ input candidate,
      selection.input = .inl (.inr input) →
      (purePlanProbingHashQuery parameter input selection.context.state).candidate? = some candidate →
      candidate.coordinate ∉ result.context.state.revealed →
      truncateHash (completion candidate.coordinate) ≠ candidate.candidate := by
  induction computation using OracleComp.inductionOn generalizing context fuel table cache history with
  | pure value =>
      simp only [runNativeQueryTrace, OracleComp.construct_pure] at hresult
      split_ifs at hresult <;> simp only [mem_support_pure_iff, Prod.mk.injEq, Option.some.injEq] at hresult
      · obtain ⟨rfl, rfl⟩ := hresult
        simp
      · simp at hresult
  | query_bind query next ih =>
      rw [runNativeQueryTrace_query_bind] at hresult
      by_cases hcomplete : DeferredCompletable table context
      · rw [if_pos hcomplete, mem_support_bind_iff] at hresult
        obtain ⟨middle, hmiddle, htail⟩ := hresult
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
            have hmiddleStarts : StartTableAgrees middle.context.state middle.table := by
              rw [hcore.1]; exact hcore.2.2
            have hfinal : DeferredCompletion middle.table result.context completion := by
              rw [hcore.1]; exact hcompletion
            intro selection hselection input candidate hinput hcandidate hhidden
            rw [hreturn.2] at hselection
            rcases List.mem_cons.mp hselection with rfl | hselection
            · have hbefore := (nativeTrace_completion_facts parameter root ftsSecret _ _ _ _ _ result tail.2 completion
                hcore.2.1 hmiddleStarts htrace hfinal).1
              rw [hcore.1] at hbefore
              have hrevealed := (revealed_subset_of_mem_runResolvedFromTable _ context fuel table middle hmiddle).trans
                (revealed_subset_of_mem_runNativeQueryTrace parameter root ftsSecret _ _ _ _ _ result tail.2 htrace)
              cases hinput
              exact hbefore.plannedCandidate_ne parameter input context fuel table cache middle completion candidate
                hconsistent hstarts hcandidate (fun h => hhidden (hrevealed h)) hmiddle
            · exact ih middle.value.1 middle.context middle.remaining middle.table middle.value.2 tail.2
                hcore.2.1 hmiddleStarts htrace hfinal selection hselection input candidate hinput hcandidate hhidden
      · rw [if_neg hcomplete] at hresult
        simp at hresult

theorem nativeTrace_matchingFinalRoot_charged
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (α × SplitHashCache)) (history : List CanonicalQuerySelection)
    (completion : Coordinate → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hresult : (some result, history) ∈ support (runNativeQueryTrace parameter root ftsSecret computation context fuel table cache))
    (hcompletion : DeferredCompletion table result.context completion)
    (hsource : ¬UnknownSourceFinalRootMatch parameter (some result, history))
    (i : Fin history.length) (input : HashInput) (candidate : Probe)
    (lay : Layer) (tree : TreeIndex) (output : HashOutput)
    (hinput : (history.get i).input = .inl (.inr input))
    (hcandidate : NativeRootCandidateAt parameter input (history.get i).context candidate)
    (hcoordinate : candidate.coordinate = .position (layerRootPosition lay tree))
    (hvalue : result.context.positionValue (layerRootPosition lay tree) = some output)
    (hmatch : candidate.candidate = truncateHash output)
    (hhidden : .position (layerRootPosition lay tree) ∉ result.context.state.revealed)
    (hmat : LayerRootsMaterialized (history.get i).context) :
    ChargedNativeRootQuery parameter input (history.get i).context := by
  have hfacts := (nativeTrace_completion_facts parameter root ftsSecret computation context fuel table cache result history completion
    hconsistent hstarts hresult hcompletion).2 (history.get i) (List.get_mem _ _)
  rcases hcandidate.direct_or_charged_or_unknown_encoding (layerRootPosition lay tree)
      ⟨lay, tree, rfl⟩ hcoordinate (fun h => hhidden (hfacts.2.2.2 h)) hmat with hdirect | hcharged | ⟨hencoding, hunknown⟩
  · have hmiss := nativeTrace_plannedCandidate_ne parameter root ftsSecret computation context fuel table cache result history completion
      hconsistent hstarts hresult hcompletion (history.get i) (List.get_mem _ _) input candidate hinput hdirect
      (by rw [hcoordinate]; exact hhidden)
    rw [hcoordinate, hcompletion.eq_positionValue _ output hvalue] at hmiss
    exact False.elim (hmiss hmatch.symm)
  · exact hcharged
  · exact False.elim (hsource ⟨result, rfl, i, input, candidate, lay, tree, output,
      hinput, hencoding, hcoordinate, hvalue, hmatch, hunknown⟩)

end SphincsSecurity.Concrete.OtsProbeSimulation

import SphincsSecurity.Proof.OtsProbeNativeTraceCompletion

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem nativeRootSelectionGuess_some_iff
    (parameter : PublicParameter) (target : Position) (selection : CanonicalQuerySelection) (guess : Digest) :
    nativeRootSelectionGuess? parameter target selection = some guess ↔
      ∃ input candidate, selection.input = .inl (.inr input) ∧
        NativeRootCandidateAt parameter input selection.context candidate ∧
        candidate.coordinate = .position target ∧ candidate.candidate = guess := by
  cases hinput : selection.input with
  | inl query =>
      cases query with
      | inl n => simp [nativeRootSelectionGuess?, nativeRootSelectionCandidate?, hinput]
      | inr input =>
          simp only [nativeRootSelectionGuess?, nativeRootSelectionCandidate?, hinput]
          change (nativeRootCandidate? parameter input selection.context).bind
            (fun candidate => if candidate.coordinate = .position target then some candidate.candidate else none) = some guess ↔ _
          cases hcand : nativeRootCandidate? parameter input selection.context with
          | none =>
              simp only [Option.bind_none, reduceCtorEq, false_iff]
              rintro ⟨otherInput, candidate, heq, hat, _, _⟩
              cases heq
              rw [(nativeRootCandidate?_eq_some_iff parameter input selection.context candidate).mpr hat] at hcand
              contradiction
          | some candidate =>
              have hat := (nativeRootCandidate?_eq_some_iff parameter input selection.context candidate).mp hcand
              constructor
              · intro hguess
                simp only [Option.bind_some] at hguess
                split_ifs at hguess with hcoordinate
                · exact ⟨input, candidate, rfl, hat, hcoordinate, Option.some.inj hguess⟩
              · rintro ⟨otherInput, other, heq, hother, hcoordinate, hguess⟩
                cases heq
                have heq := nativeRootCandidateAt_unique hat hother
                subst other
                simp [hcoordinate, hguess]
  | inr message => simp [nativeRootSelectionGuess?, nativeRootSelectionCandidate?, hinput]

theorem nativeRootCandidateHistory_first_match
    (parameter : PublicParameter) (target : Position) (history : List CanonicalQuerySelection)
    (guess : Digest) (hmatch : guess ∈ nativeRootCandidateHistory parameter target history) :
    ∃ prior selection suffix, history = prior ++ selection :: suffix ∧
      guess ∉ nativeRootCandidateHistory parameter target prior ∧
      nativeRootSelectionGuess? parameter target selection = some guess := by
  induction history with
  | nil => simp [nativeRootCandidateHistory, nativeHashQueryHistory] at hmatch
  | cons selection history ih =>
      by_cases hhead : nativeRootSelectionGuess? parameter target selection = some guess
      · exact ⟨[], selection, history, rfl, by simp [nativeRootCandidateHistory, nativeHashQueryHistory], hhead⟩
      · have htail : guess ∈ nativeRootCandidateHistory parameter target history := by
          rw [nativeRootCandidateHistory_cons] at hmatch
          cases hg : nativeRootSelectionGuess? parameter target selection <;> simp_all [insertNativeRootGuess, eq_comm]
        obtain ⟨prior, selected, suffix, rfl, hbefore, hselected⟩ := ih htail
        refine ⟨selection :: prior, selected, suffix, rfl, ?_, hselected⟩
        rw [nativeRootCandidateHistory_cons]
        cases hg : nativeRootSelectionGuess? parameter target selection <;> simp_all [insertNativeRootGuess, eq_comm]

theorem ChargedNativeRootQuery.candidate_known
    {parameter : PublicParameter} {input : HashInput} {context : DeferredContext} {candidate : Probe}
    (hcharged : ChargedNativeRootQuery parameter input context)
    (hcandidate : NativeRootCandidateAt parameter input context candidate) (target : Position)
    (hcoordinate : candidate.coordinate = .position target) :
    ∃ output, context.positionValue target = some output := by
  rcases hcharged with hstructural | hencoding
  · have hquery := hstructural
    obtain ⟨parent, knownTarget, hat, hroot, hmem, _, hknown⟩ := hstructural
    have hstruct : StructuralLayerRootCandidateAt parameter input
        ⟨.position knownTarget, slotDigest (parent.children.idxOf knownTarget) input⟩ :=
      ⟨parent, knownTarget, hat, hroot, hmem, rfl⟩
    have heq := nativeRootCandidateAt_unique hcandidate
      (Or.inr (Or.inr ⟨hquery, hstruct⟩))
    have htarget : target = knownTarget := Coordinate.position.inj (hcoordinate.symm.trans (congrArg Probe.coordinate heq))
    subst target
    obtain ⟨lay, tree, level, nodeIdx, rfl⟩ := exists_node_of_layerRoot_mem_children hroot hmem
    have hchildren : purePeekPositionValues context.state (Position.node lay tree level nodeIdx).children ≠ none := by
      intro hnone
      exact hknown (by simp [purePeekTableInput, hnone])
    cases hstate : context.state.values (.position knownTarget) with
    | none => exact False.elim (hchildren ((purePeekPositionValues_eq_none_iff_missing _ _).mpr ⟨knownTarget, hmem, hstate⟩))
    | some output => exact ⟨output, by simp [DeferredContext.positionValue, hstate]⟩
  · obtain ⟨encoding, knownTarget, output, hat, hposition, hknown, _⟩ := hencoding.known
    have heq := nativeRootCandidateAt_unique hcandidate (Or.inr (Or.inl hat))
    have htarget : target = knownTarget := Coordinate.position.inj
      (hcoordinate.symm.trans ((congrArg Probe.coordinate heq).trans hposition))
    subst target
    exact ⟨output, hknown⟩

theorem nativeTrace_rootHistoryMatch_firstCharged
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (α × SplitHashCache)) (history : List CanonicalQuerySelection)
    (completion : Coordinate → HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hmat : LayerRootsMaterialized context) (hclosed : DeferredComputationsClosed context)
    (hresult : (some result, history) ∈ support (runNativeQueryTrace parameter root ftsSecret computation context fuel table cache))
    (hcompletion : DeferredCompletion table result.context completion)
    (hsource : ¬UnknownSourceFinalRootMatch parameter (some result, history))
    (lay : Layer) (tree : TreeIndex) (output : HashOutput)
    (hvalue : result.context.positionValue (layerRootPosition lay tree) = some output)
    (hhidden : .position (layerRootPosition lay tree) ∉ result.context.state.revealed)
    (hmatch : truncateHash output ∈ nativeRootCandidateHistory parameter (layerRootPosition lay tree) history) :
    ∃ prior selection suffix, history = prior ++ selection :: suffix ∧
      truncateHash output ∉ nativeRootCandidateHistory parameter (layerRootPosition lay tree) prior ∧
      selection.context.positionValue (layerRootPosition lay tree) = some output ∧
      .position (layerRootPosition lay tree) ∉ selection.context.state.revealed ∧
      chargedNativeRootQueryCandidate parameter (layerRootPosition lay tree) selection.input selection.context = some (truncateHash output) := by
  obtain ⟨prior, selection, suffix, hhistory, hprior, hguess⟩ :=
    nativeRootCandidateHistory_first_match parameter (layerRootPosition lay tree) history (truncateHash output) hmatch
  have hmem : selection ∈ history := by rw [hhistory]; simp
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hmem
  obtain ⟨input, candidate, hinput, hcandidate, hcoordinate, hguess⟩ :=
    (nativeRootSelectionGuess_some_iff parameter (layerRootPosition lay tree) selection (truncateHash output)).mp hguess
  have hselectionMat := (layerRootsMaterialized_runNativeQueryTrace parameter root ftsSecret computation context fuel table cache
    (some result, history) hmat hclosed hresult).2 selection hmem
  have hcharged := nativeTrace_matchingFinalRoot_charged parameter root ftsSecret computation context fuel table cache result history completion
    hconsistent hstarts hresult hcompletion hsource i input candidate lay tree output
    (by simpa only [hi] using hinput) (by simpa only [hi] using hcandidate) hcoordinate hvalue hguess hhidden
    (by simpa only [hi] using hselectionMat)
  rw [hi] at hcharged
  have hfacts := (nativeTrace_completion_facts parameter root ftsSecret computation context fuel table cache result history completion
    hconsistent hstarts hresult hcompletion).2 selection hmem
  obtain ⟨stored, hstored⟩ := hcharged.candidate_known hcandidate (layerRootPosition lay tree) hcoordinate
  have heq : stored = output := (hfacts.2.2.1.eq_positionValue _ stored hstored).symm.trans
    (hcompletion.eq_positionValue _ output hvalue)
  subst stored
  refine ⟨prior, selection, suffix, hhistory, hprior, hstored, fun h => hhidden (hfacts.2.2.2 h), ?_⟩
  rw [hinput]
  simp [chargedNativeRootQueryCandidate, hcharged,
    (nativeRootCandidate?_eq_some_iff parameter input selection.context candidate).mpr hcandidate, hcoordinate, hguess]

end SphincsSecurity.Concrete.OtsProbeSimulation

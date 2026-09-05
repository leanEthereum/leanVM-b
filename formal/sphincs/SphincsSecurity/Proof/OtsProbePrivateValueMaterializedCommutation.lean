import SphincsSecurity.Proof.OtsProbeResolvedPrivateInterpreter

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

theorem evalDist_resolveDeferredPositionValue_rebase_state
    (target : Position) (table : OtsSecretIndex → HashOutput) (left right : DeferredContext)
    (hview : FinalizationViewEq table left right) (hleft : left.Valid) (hright : right.Valid)
    (hcomplete : DeferredCompletable table left) (hvalues : left.values = right.values) :
    evalDist (Option.map (fun result : DeferredResolution =>
      { result with state := right.state.clearPending (.position target) }) <$>
        resolveDeferredPositionValue target left) =
      evalDist (resolveDeferredPositionValue target right) := by
  have hbase := relTriple_resolveDeferredPositionValue_of_finalizationViewEq table target
    left right hview hleft hright hcomplete
  have hleftSupport := SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
    (fun result => result ∈ support (resolveDeferredPositionValue target left)) (fun _ hresult => hresult)
  have hboth := SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleftSupport
  have hequal : RelTriple (resolveDeferredPositionValue target left) (resolveDeferredPositionValue target right)
      (fun leftResult rightResult => leftResult.map (fun result : DeferredResolution =>
        { result with state := right.state.clearPending (.position target) }) = rightResult) := by
    apply relTriple_post_mono hboth
    intro leftResult rightResult hrelation
    rcases hrelation with ⟨⟨hrelation, hleftResult⟩, hrightResult⟩
    cases leftResult with
    | none =>
        cases rightResult with
        | none => rfl
        | some rightResult => simp [FinalizationResolutionEq] at hrelation
    | some leftResult =>
        cases rightResult with
        | none => simp [FinalizationResolutionEq] at hrelation
        | some rightResult =>
            have houtputs : leftResult.output = rightResult.output := hrelation.1
            have haux := resolveDeferredPositionValue_values_eq_of_values_eq target left right
              leftResult rightResult hleftResult hrightResult hvalues houtputs
            have hstate := resolveDeferredPositionValue_state_eq_clearPending target right rightResult hrightResult
            cases leftResult with
            | mk leftContext leftOutput =>
                cases rightResult with
                | mk rightContext rightOutput =>
                    cases leftContext
                    cases rightContext
                    simp_all
  have hmapped := relTriple_map (R := Eq) (g := id) hequal
  simpa using evalDist_eq_of_relTriple_eqRel hmapped

theorem evalDist_resolveDeferredPositionValue_materialized_reveal
    (target revealed : Position) (context : DeferredContext)
    (revealedResult : DeferredResolution) (table : OtsSecretIndex → HashOutput)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hrevealed : some revealedResult ∈ support (resolveDeferredReveal table revealed context)) :
    evalDist (Option.map (fun result : DeferredResolution =>
      { result with state :=
          (context.state.clearPending (.position target)).materialize (.position revealed) revealedResult.output }) <$>
        resolveDeferredPositionValue target revealedResult.toDeferredContext) =
      evalDist (resolveDeferredPositionValue target (materializeResolvedPosition context revealed revealedResult)) := by
  let materialized := materializeResolvedPosition context revealed revealedResult
  have hstarts := startTableAgrees_of_deferredCompletable hcompletable
  have hrevealedValid := hvalid.of_resolveDeferredReveal table revealed revealedResult hrevealed
  have hstateValues := resolveDeferredReveal_preserves_state_values table revealed context revealedResult hrevealed
  have hresolved := resolveDeferredReveal_resolves table revealed context revealedResult hrevealed
  have hmaterializedValid := hvalid.materializeResolvedPosition_of revealed revealedResult
    hrevealedValid hstateValues hresolved
  have hrevealedCompletable := hcompletable.of_resolveDeferredReveal hvalid revealed revealedResult hrevealed
  have hmaterializedCompletable : DeferredCompletable table materialized := by
    obtain ⟨completion, hcompletion⟩ := hrevealedCompletable
    exact ⟨completion, (deferredCompletion_materializeResolvedReveal_iff revealed revealedResult hvalid
      hstarts hrevealed).2 hcompletion⟩
  have hview : FinalizationViewEq table materialized revealedResult.toDeferredContext :=
    finalizationViewEq_materializeResolvedReveal revealed revealedResult hvalid hstarts hrevealed hmaterializedCompletable
  have hdist := evalDist_resolveDeferredPositionValue_rebase_state target table revealedResult.toDeferredContext
    materialized hview.symm hrevealedValid hmaterializedValid hrevealedCompletable rfl
  simpa only [materialized, materializeResolvedPosition, ← clearPending_materialize_comm] using hdist

theorem evalDist_resolveDeferredPositionValue_materialized_chainStart
    (target : Position) (index : OtsSecretIndex) (context : DeferredContext)
    (revealedResult : DeferredResolution) (table : OtsSecretIndex → HashOutput)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hrevealed : resolveDeferredChainStart table index context = some revealedResult) :
    evalDist (Option.map (fun result : DeferredResolution =>
      { result with state :=
          (context.state.clearPending (.position target)).materialize index.coordinate revealedResult.output }) <$>
        resolveDeferredPositionValue target revealedResult.toDeferredContext) =
      evalDist (resolveDeferredPositionValue target (materializeResolvedChainStart context index revealedResult)) := by
  let materialized := materializeResolvedChainStart context index revealedResult
  have hstarts := startTableAgrees_of_deferredCompletable hcompletable
  have hrevealedValid := hvalid.of_resolveDeferredChainStart table index revealedResult hrevealed
  have hstateValues := resolveDeferredChainStart_state_values_eq table index context revealedResult hrevealed
  have hdeferredValues := resolveDeferredChainStart_deferred_values_eq table index context revealedResult hrevealed
  have hrevealedCompletable := hcompletable.of_resolveDeferredChainStart index revealedResult hrevealed
  have houtput := resolveDeferredChainStart_output_of_agrees table index context revealedResult hstarts hrevealed
  have hmaterializedValid : materialized.Valid := by
    dsimp only [materialized]
    rw [materializeResolvedChainStart, hdeferredValues]
    rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
    exact hvalid.materialize_chainStart lay tree leafIdx chainIdx revealedResult.output
  have hmaterializedCompletable : DeferredCompletable table materialized := by
    obtain ⟨completion, hcompletion⟩ := hrevealedCompletable
    exact ⟨completion, (deferredCompletion_materializeResolvedChainStart_iff index revealedResult hstarts
      houtput hstateValues hdeferredValues
      (resolveDeferredChainStart_pending_eq table index context revealedResult hrevealed)).2 hcompletion⟩
  have hview : FinalizationViewEq table materialized revealedResult.toDeferredContext :=
    finalizationViewEq_materializeResolvedChainStart index revealedResult hvalid hstarts hrevealed hmaterializedCompletable
  have hdist := evalDist_resolveDeferredPositionValue_rebase_state target table revealedResult.toDeferredContext
    materialized hview.symm hrevealedValid hmaterializedValid hrevealedCompletable rfl
  simpa only [materialized, materializeResolvedChainStart, ← clearPending_materialize_comm] using hdist

noncomputable def resolvePrivateThenMaterializedReveal
    (target revealed : Position) (table : OtsSecretIndex → HashOutput) (context : DeferredContext) :
    ProbComp (Option RevealedResolution) := do
  let privateResult ← resolveDeferredPositionValue target context
  match privateResult with
  | none => pure none
  | some privateResult =>
      let revealedResult ← resolveDeferredReveal table revealed privateResult.toDeferredContext
      pure (revealedResult.map fun result =>
        ⟨materializeResolvedPosition privateResult.toDeferredContext revealed result, result.output⟩)

noncomputable def resolveMaterializedRevealThenPrivate
    (target revealed : Position) (table : OtsSecretIndex → HashOutput) (context : DeferredContext) :
    ProbComp (Option RevealedResolution) := do
  let revealedResult ← resolveDeferredReveal table revealed context
  match revealedResult with
  | none => pure none
  | some revealedResult =>
      let privateResult ← resolveDeferredPositionValue target (materializeResolvedPosition context revealed revealedResult)
      pure (privateResult.map fun result => ⟨result.toDeferredContext, revealedResult.output⟩)

def materializePrivateRevealed (target revealed : Position) (context : DeferredContext)
    (result : RevealedResolution) : RevealedResolution :=
  ⟨{ state := (context.state.clearPending (.position target)).materialize (.position revealed) result.output
     values := result.context.values }, result.output⟩

theorem evalDist_resolvePrivateThenMaterializedReveal_eq_map
    (target revealed : Position) (table : OtsSecretIndex → HashOutput) (context : DeferredContext) :
    evalDist (resolvePrivateThenMaterializedReveal target revealed table context) =
      evalDist (Option.map (materializePrivateRevealed target revealed context) <$>
        resolvePositionThenResolver target (resolveDeferredReveal table revealed) context) := by
  unfold resolvePrivateThenMaterializedReveal resolvePositionThenResolver
  simp only [map_eq_bind_pure_comp, bind_assoc]
  apply evalDist_bind_congr
  intro privateResult hprivate
  cases privateResult with
  | none => simp
  | some privateResult =>
      have hstate := resolveDeferredPositionValue_state_eq_clearPending target context privateResult hprivate
      simp only
      rw [bind_assoc]
      apply evalDist_bind_congr
      intro revealedResult _
      cases revealedResult with
      | none => rfl
      | some revealedResult =>
          simp only [pure_bind, Function.comp_apply, Option.map_some, materializePrivateRevealed, materializeResolvedPosition]
          rw [hstate]

theorem evalDist_resolveMaterializedRevealThenPrivate_eq_map
    (target revealed : Position) (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context) :
    evalDist (resolveMaterializedRevealThenPrivate target revealed table context) =
      evalDist (Option.map (materializePrivateRevealed target revealed context) <$>
        resolveResolverThenPosition target (resolveDeferredReveal table revealed) context) := by
  unfold resolveMaterializedRevealThenPrivate resolveResolverThenPosition
  simp only [map_eq_bind_pure_comp, bind_assoc]
  apply evalDist_bind_congr
  intro revealedResult hrevealed
  cases revealedResult with
  | none => simp
  | some revealedResult =>
      have hdist := evalDist_resolveDeferredPositionValue_materialized_reveal target revealed context revealedResult table
        hvalid hcompletable hrevealed
      let observe := Option.map (fun result : DeferredResolution =>
        (⟨result.toDeferredContext, revealedResult.output⟩ : RevealedResolution))
      have hmapped : evalDist (observe <$> resolveDeferredPositionValue target
          (materializeResolvedPosition context revealed revealedResult)) =
          evalDist (observe <$> (Option.map (fun result : DeferredResolution =>
            { result with state :=
                (context.state.clearPending (.position target)).materialize (.position revealed) revealedResult.output }) <$>
              resolveDeferredPositionValue target revealedResult.toDeferredContext)) := by
        rw [evalDist_map, evalDist_map, hdist]
      simp only [map_eq_bind_pure_comp, bind_assoc] at hmapped
      apply hmapped.trans
      simp only
      rw [bind_assoc]
      apply evalDist_bind_congr
      intro privateResult _
      cases privateResult <;> rfl

theorem evalDist_resolvePrivateThenMaterializedReveal
    (target revealed : Position) (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context) :
    evalDist (resolvePrivateThenMaterializedReveal target revealed table context) =
      evalDist (resolveMaterializedRevealThenPrivate target revealed table context) := by
  rw [evalDist_resolvePrivateThenMaterializedReveal_eq_map,
    evalDist_resolveMaterializedRevealThenPrivate_eq_map target revealed table context hvalid hcompletable,
    evalDist_map, evalDist_map]
  exact congrArg _ (positionResolutionCommutes_reveal target table revealed context hvalid hcompletable)

end SphincsSecurity.Concrete.OtsProbeSimulation

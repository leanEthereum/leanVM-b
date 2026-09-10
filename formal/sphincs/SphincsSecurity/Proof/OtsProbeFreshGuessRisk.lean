import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeHashRisk
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateSafe

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

theorem resolvedContextFailureRisk_eq_finalize_coordinates
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext) (coordinates : List Coordinate)
    (hvalid : context.Valid) (hstarts : StartTableAgrees context.state table)
    (hcovered : PendingCovered coordinates context) (hnodup : coordinates.Nodup)
    (hcard : context.state.pending.card < Fintype.card Digest) :
    resolvedContextFailureRisk table context =
      Pr[fun result => result = none | finalizeResolvedCoordinates coordinates context table] := by
  have heq := (evalDist_finishResolvedRunIsNone_eq_finalize ⟨context, 0, (), table⟩ hvalid hstarts hcard).trans
    (evalDist_finalizeResolvedCoordinates_eq_dynamic table coordinates context hvalid hstarts hcovered hnodup hcard).symm
  have hprob := congrArg (fun distribution : SPMF Bool => distribution true) heq
  change Pr[= true | _] = Pr[= true | _] at hprob
  rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput, probEvent_map] at hprob
  simpa only [resolvedContextFailureRisk, resolvedFinalizationObserve, Function.comp_def,
    Option.isNone_iff_eq_none] using hprob

theorem completeResolved_addPending_self
    (context : DeferredContext) (coordinate : Coordinate) (candidate : Digest) (output : HashOutput) :
    ({ context with state := context.state.addPending coordinate candidate } : DeferredContext).completeResolved coordinate output =
      context.completeResolved coordinate output := by
  cases coordinate <;>
    simp [DeferredContext.completeResolved, LazyRevealProbe.State.complete, LazyRevealProbe.State.addPending,
      LazyRevealProbe.State.pendingAway, Finset.filter_insert]

theorem probEvent_finalize_fresh_addPending_le
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext) (position : Position)
    (candidate : Digest) (remaining : List Coordinate) (hvalue : context.positionValue position = none) :
    Pr[fun result => result = none | finalizeResolvedCoordinates (.position position :: remaining)
      { context with state := context.state.addPending (.position position) candidate } table] ≤
    Pr[fun result => result = none | finalizeResolvedCoordinates (.position position :: remaining) context table] +
      (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  classical
  have hnextValue : ({ context with state := context.state.addPending (.position position) candidate } :
      DeferredContext).positionValue position = none := hvalue
  rw [← SphincsSecurity.probEvent_uniform_truncateHash_eq candidate]
  change _ ≤ _ + Pr[fun output => truncateHash output = candidate | LazyRevealProbe.sampleHashOutput]
  rw [finalizeResolvedCoordinates_cons_position_of_unknown table position remaining _ hnextValue,
    finalizeResolvedCoordinates_cons_position_of_unknown table position remaining context hvalue,
    probEvent_bind_eq_tsum, probEvent_bind_eq_tsum, probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro output
  simp only [hitAt_addPending_self_iff, completeResolved_addPending_self]
  by_cases hold : context.state.hitAt (.position position) output
  · simp only [hold, true_or, ↓reduceIte, probEvent_pure, mul_one]
    exact le_add_of_nonneg_right bot_le
  · by_cases hnew : truncateHash output = candidate
    · simp only [hold, hnew, false_or, ↓reduceIte, probEvent_pure, mul_one]
      exact le_add_of_nonneg_left bot_le
    · simp [hold, hnew]

theorem resolvedContextFailureRisk_addPending_unknown_position
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext) (position : Position) (candidate : Digest)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hcard : context.state.pending.card + 1 < Fintype.card Digest)
    (hvalue : context.positionValue position = none) :
    resolvedContextFailureRisk table { context with state := context.state.addPending (.position position) candidate } ≤
      resolvedContextFailureRisk table context + (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  classical
  by_cases hcomplete : DeferredCompletable table context
  · have hvalid := valid_of_resolvedCore_completable table context hconsistent hstarts hcomplete
    have hmissing : context.state.values (.position position) = none := by
      unfold DeferredContext.positionValue at hvalue
      cases hstate : context.state.values (.position position) with
      | none => rfl
      | some output => simp [hstate] at hvalue
    let remaining := (context.state.coordinates.erase (.position position)).toList
    let coordinates := .position position :: remaining
    have hnodup : coordinates.Nodup := by
      exact List.nodup_cons.mpr ⟨by simp [remaining], Finset.nodup_toList _⟩
    have hmem : ∀ coordinate ∈ context.state.coordinates, coordinate ∈ coordinates := by
      intro coordinate hcoordinate
      by_cases heq : coordinate = .position position
      · simp [coordinates, heq]
      · simp [coordinates, remaining, heq, hcoordinate]
    have hcovered : PendingCovered coordinates context := by
      intro entry hentry
      apply hmem
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hentry)
    have hnextCovered : PendingCovered coordinates
        { context with state := context.state.addPending (.position position) candidate } := by
      intro entry hentry
      simp only [LazyRevealProbe.State.addPending, Finset.mem_insert] at hentry
      rcases hentry with rfl | hentry
      · simp [coordinates]
      · exact hcovered entry hentry
    have hnextCard : (context.state.addPending (.position position) candidate).pending.card < Fintype.card Digest :=
      (Finset.card_insert_le _ _).trans_lt hcard
    rw [resolvedContextFailureRisk_eq_finalize_coordinates table _ coordinates
        (hvalid.addPending_of_value_none _ candidate hmissing) (hstarts.addPending _ candidate)
        hnextCovered hnodup hnextCard,
      resolvedContextFailureRisk_eq_finalize_coordinates table context coordinates hvalid hstarts hcovered hnodup (by omega)]
    exact probEvent_finalize_fresh_addPending_le table context position candidate remaining hvalue
  · rw [resolvedContextFailureRisk_of_not_completable table context hcomplete]
    exact (resolvedContextFailureRisk_le_one table _).trans (le_add_of_nonneg_right bot_le)

theorem resolvedContextFailureRisk_addPending_unknown
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext) (coordinate : Coordinate) (candidate : Digest)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hcard : context.state.pending.card + 1 < Fintype.card Digest)
    (hvalue : resolvedCompletionValue table context coordinate = none) :
    resolvedContextFailureRisk table { context with state := context.state.addPending coordinate candidate } ≤
      resolvedContextFailureRisk table context + ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  cases coordinate with
  | chainStart => simp [resolvedCompletionValue] at hvalue
  | position position =>
      simpa only [show Fintype.card Digest = 2 ^ digestBits by simp] using
        resolvedContextFailureRisk_addPending_unknown_position table context position candidate hconsistent hstarts hcard hvalue

noncomputable def candidateFailureAllowance
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext) : Option Probe → ℝ≥0∞
  | none => 0
  | some candidate =>
      if candidate.coordinate ∈ context.state.revealed ∨
          (candidate.coordinate, candidate.candidate) ∈ context.state.pending then 0
      else match resolvedCompletionValue table context candidate.coordinate with
        | none => ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹
        | some output => if truncateHash output = candidate.candidate then 1 else 0

theorem resolvedContextFailureRisk_afterCandidate_le
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext) (candidate : Option Probe)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hcard : context.state.pending.card + 1 < Fintype.card Digest) :
    resolvedContextFailureRisk table (afterCandidateContext context candidate) ≤
      resolvedContextFailureRisk table context + candidateFailureAllowance table context candidate := by
  classical
  cases candidate with
  | none => simp [afterCandidateContext, candidateFailureAllowance]
  | some candidate =>
      by_cases hrevealed : candidate.coordinate ∈ context.state.revealed
      · simp [afterCandidateContext, candidateFailureAllowance, hrevealed]
      · by_cases hduplicate : (candidate.coordinate, candidate.candidate) ∈ context.state.pending
        · rw [resolvedContextFailureRisk_afterCandidate_of_duplicate table context candidate hduplicate]
          simp [candidateFailureAllowance, hduplicate]
        · simp only [afterCandidateContext, hrevealed, candidateFailureAllowance, hduplicate, or_self, ↓reduceIte]
          cases hvalue : resolvedCompletionValue table context candidate.coordinate with
          | none =>
              exact resolvedContextFailureRisk_addPending_unknown table context candidate.coordinate
                candidate.candidate hconsistent hstarts hcard hvalue
          | some output =>
              dsimp only
              by_cases hhit : truncateHash output = candidate.candidate
              · rw [if_pos hhit, resolvedContextFailureRisk_addPending_hit table context candidate.coordinate
                  candidate.candidate output hvalue hhit]
                exact le_add_of_nonneg_left bot_le
              · rw [if_neg hhit, resolvedContextFailureRisk_addPending_miss table context candidate.coordinate
                  candidate.candidate output hconsistent hstarts hvalue hhit, add_zero]

theorem probEvent_canonicalHashQuery_finished_le_initial_add_allowance
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : HashInput) (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hcard : context.state.pending.card + 1 < Fintype.card Digest) :
    Pr[fun verdict => verdict = true |
      canonicalChronologicalAdversaryImpl parameter root table ftsSecret (.inl (.inr input))
        context (fuel + 1) table cache >>= finishResolvedRunIsNone] ≤
      resolvedContextFailureRisk table context + candidateFailureAllowance table context
        (purePlanProbingHashQuery parameter input context.state).candidate? := by
  have hdist := evalDist_canonicalHashQuery_finished_eq_candidate parameter root table ftsSecret input
    context fuel cache hconsistent hstarts hcard
  have hprob := congrArg (fun distribution : SPMF Bool => distribution true) hdist
  change Pr[= true | _] = Pr[= true | _] at hprob
  rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput] at hprob
  exact hprob.trans_le (resolvedContextFailureRisk_afterCandidate_le table context _ hconsistent hstarts hcard)

end SphincsSecurity.Concrete.OtsProbeSimulation

import SphincsSecurity.Proof.OtsProbePrivateValueErasedComparison
import SphincsSecurity.Proof.OtsProbePrivateValueRawProbeRisk

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def privateErasedCandidate
    (target : Position) (select : Nat → α → Option Digest)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (output : HashOutput) : ProbComp (Option Digest) :=
  (fun result => result.bind (fun pair => select pair.1 pair.2)) <$>
    privateErasedPrefixValue target (replacePrivatePosition target output context) fuel table computation

noncomputable def privateErasedCandidateCharge
    (target : Position) (select : Nat → α → Option Digest)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) : ENNReal :=
  Pr[fun candidate => candidate ≠ none | privateErasedCandidate target select computation context fuel table 0]

theorem privateErasedCandidateCharge_le_one
    (target : Position) (select : Nat → α → Option Digest)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    privateErasedCandidateCharge target select computation context fuel table ≤ 1 := probEvent_le_one

theorem evalDist_privateErasedCandidate_eq
    (target : Position) (select : Nat → α → Option Digest)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (before after : HashOutput)
    (hstate : context.state.values (.position target) = none)
    (hpending : context.state.pendingAt (.position target) = ∅)
    (hsafe : computation.IsQueryBoundP (IsPrivatePositionDisclosure target) 0) :
    evalDist (privateErasedCandidate target select computation context fuel table before) =
      evalDist (privateErasedCandidate target select computation context fuel table after) :=
  evalDist_map_eq_of_evalDist_eq
    (evalDist_privateErasedPrefixValue_replace target before after computation context fuel table hstate hpending hsafe) _

theorem probEvent_privateResolvedSelectedCandidate_preloaded_le_erased
    (target : Position) (output : HashOutput) (select : Nat → α → Option Digest)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (bound : Nat)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hstate : context.state.values (.position target) = none)
    (hhidden : .position target ∉ context.state.revealed)
    (hpending : context.state.pendingAt (.position target) = ∅)
    (hsafe : computation.IsQueryBoundP (IsPrivatePositionDisclosure target) 0)
    (hcount : computation.IsQueryBoundP (IsPrivatePositionProbe target) bound) :
    Pr[PrivateCandidatePairHit | privateResolvedSelectedCandidate target select <$>
      runPrivateResolvedView target table (replacePrivatePosition target output context) fuel computation] ≤
      Pr[fun candidate => candidate = some (truncateHash output) |
        privateErasedCandidate target select computation context fuel table output] := by
  have hinitial : PrivateTargetState target output ∅ (replacePrivatePosition target output context) := by
    refine ⟨hstate, ?_, hhidden, hpending⟩
    simp [replacePrivatePosition, DeferredStructuralValues.install]
  have hc : (replacePrivatePosition target output context).ValuesConsistent := by
    intro position value hvalue
    by_cases heq : position = target
    · subst position
      simp [replacePrivatePosition, hstate] at hvalue
    · simpa [replacePrivatePosition, DeferredStructuralValues.install, heq] using hconsistent position value hvalue
  have hs : StartTableAgrees (replacePrivatePosition target output context).state table := hstarts
  rw [probEvent_congr' (fun _ _ => Iff.rfl)
    (evalDist_privateResolvedSelectedCandidate_preloaded target output select computation _ fuel table ∅ bound
      hinitial hc hs hsafe hcount), probEvent_map]
  unfold privateErasedCandidate
  rw [probEvent_map]
  have hevent (result : Option (Nat × α)) :
      PrivateCandidatePairHit (result.bind (fun pair => (select pair.1 pair.2).map (fun digest => (output, digest)))) ↔
        result.bind (fun pair => select pair.1 pair.2) = some (truncateHash output) := by
    cases result with
    | none => simp [PrivateCandidatePairHit]
    | some result => cases hselect : select result.1 result.2 <;> simp [PrivateCandidatePairHit, hselect]
  simp only [Function.comp_def]
  rw [probEvent_congr' (fun result _ => hevent result) rfl]
  exact probEvent_runResolvedLiveValue_le_privateErasedPrefixValue target output computation _ fuel table _ (by simp)
    hc hs hinitial hsafe

theorem probEvent_privateResolvedSelectedCandidate_le_erased_charge
    (target : Position) (select : Nat → α → Option Digest)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (bound : Nat)
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hensured : .position target ∈ context.state.ensured)
    (hstate : context.state.values (.position target) = none) (hvalue : context.values target = none)
    (hhidden : .position target ∉ context.state.revealed)
    (hpending : context.state.pendingAt (.position target) = ∅)
    (hsafe : computation.IsQueryBoundP (IsPrivatePositionDisclosure target) 0)
    (hcount : computation.IsQueryBoundP (IsPrivatePositionProbe target) bound) :
    Pr[PrivateCandidatePairHit | privateResolvedSelectedCandidate target select <$>
      runPrivateResolvedView target table context fuel computation] ≤
      privateErasedCandidateCharge target select computation context fuel table * (Fintype.card Digest : ENNReal)⁻¹ := by
  let run := privateErasedCandidate target select computation context fuel table
  have hsame : ∀ output, True → evalDist (run output) = evalDist (run 0) := by
    intro output _
    exact evalDist_privateErasedCandidate_eq target select computation context fuel table output 0 hstate hpending hsafe
  apply le_trans (b := Pr[fun pair => pair.2 = some (truncateHash pair.1) | filteredPrivateGuess (fun _ => True) run])
  · rw [probEvent_map, probEvent_congr' (fun _ _ => Iff.rfl)
      (evalDist_runPrivateResolvedView_eq_uniform target computation context fuel table hvalid hcomplete hensured hstate hvalue)]
    unfold filteredPrivateGuess
    rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
    apply ENNReal.tsum_le_tsum
    intro output
    have hclean : ¬context.state.hitAt (.position target) output := by
      simp [LazyRevealProbe.State.hitAt, hpending]
    have hclear : (completePrivatePosition target context output).toDeferredContext = replacePrivatePosition target output context := by
      simp [completePrivatePosition, replacePrivatePosition,
        clearPending_eq_self_of_pendingAt_empty context.state (.position target) hpending]
    simp only [if_neg hclean, if_true, hclear]
    apply mul_le_mul' le_rfl
    have hpair : Pr[fun pair : HashOutput × Option Digest => pair.2 = some (truncateHash pair.1) |
        run output >>= fun candidate => pure (output, candidate)] =
        Pr[fun candidate => candidate = some (truncateHash output) | run output] :=
      probEvent_bind_pure_comp (run output) (fun candidate => (output, candidate)) _
    rw [hpair]
    rw [← probEvent_map]
    exact probEvent_privateResolvedSelectedCandidate_preloaded_le_erased target output select computation context fuel table bound
      hvalid.valuesConsistent (startTableAgrees_of_deferredCompletable hcomplete) hstate hhidden hpending hsafe hcount
  · exact probEvent_filteredPrivateGuess_hit_le_common (fun _ => True) run (run 0) hsame

theorem probEvent_privateResolvedRawCandidate_le_erased_charge
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hensured : .position target ∈ context.state.ensured)
    (hstate : context.state.values (.position target) = none) (hvalue : context.values target = none)
    (hhidden : .position target ∉ context.state.revealed)
    (hpending : context.state.pendingAt (.position target) = ∅) :
    Pr[PrivateCandidatePairHit | privateResolvedSelectedCandidate target (privateRawCutCandidate target) <$>
      runPrivateResolvedView target table context fuel (privatePositionProbeCutAt target computation ordinal)] ≤
      privateErasedCandidateCharge target (privateRawCutCandidate target) (privatePositionProbeCutAt target computation ordinal)
        context fuel table * (Fintype.card Digest : ENNReal)⁻¹ :=
  probEvent_privateResolvedSelectedCandidate_le_erased_charge target _ _ context fuel table ordinal
    hvalid hcomplete hensured hstate hvalue hhidden hpending
    (privatePositionProbeCutAt_no_disclosure target computation ordinal)
    (privatePositionProbeCutAt_probe_bound target computation ordinal)

end SphincsSecurity.Concrete.OtsProbeSimulation

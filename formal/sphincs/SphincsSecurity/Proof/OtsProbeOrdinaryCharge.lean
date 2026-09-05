import SphincsSecurity.Proof.OtsProbePlannedCharge

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

noncomputable def ordinaryChargeStep (input : (LazyRevealProbe.World Coordinate).Domain)
    (next : (LazyRevealProbe.World Coordinate).Range input → DeferredContext → Nat → ℝ≥0∞)
    (context : DeferredContext) (fuel : Nat) : ℝ≥0∞ :=
  match input with
  | .uniform n => ∑' output, Pr[= output | (liftM (unifSpec.query n) : ProbComp _)] * next output context fuel
  | .hashOutput => ∑' output, Pr[= output | LazyRevealProbe.sampleHashOutput] * next output context fuel
  | .ensure coordinate => next () { context with state := context.state.ensure coordinate } fuel
  | .probe coordinate candidate =>
      match fuel with
      | 0 => 0
      | remaining + 1 =>
          if coordinate ∈ context.state.revealed then next () context remaining
          else (LazyRevealProbe.pendingProbeCharge context.state coordinate candidate : ℝ≥0∞) +
            next () { context with state := context.state.addPending coordinate candidate } remaining
  | .peek coordinate => next (context.state.values coordinate) context fuel
  | .publish coordinate => next () { context with state := context.state.publish coordinate } fuel
  | .reveal coordinate =>
      match context.state.values coordinate with
      | some output => next output context fuel
      | none =>
          match coordinate with
          | .chainStart _ _ _ _ => ∑' output, Pr[= output | LazyRevealProbe.sampleHashOutput] *
              if context.state.hitAt coordinate output then 0
              else next output { context with state := context.state.materialize coordinate output } fuel
          | .position position =>
              match context.values position with
              | some output =>
                  if context.state.hitAt coordinate output then 0
                  else next output { context with state := context.state.materialize coordinate output } fuel
              | none => ∑' output, Pr[= output | LazyRevealProbe.sampleHashOutput] *
                  if context.state.hitAt coordinate output then 0
                  else next output
                    { state := context.state.materialize coordinate output
                      values := context.values.install position output } fuel

noncomputable def ordinaryContinuationCharge {α : Type}
    (post : DeferredContext → Nat → α → ℝ≥0∞)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) : DeferredContext → Nat → ℝ≥0∞ :=
  OracleComp.construct (fun value context fuel => post context fuel value)
    (fun input _ next => ordinaryChargeStep input next) computation

theorem ordinaryContinuationCharge_query_bind {α : Type}
    (post : DeferredContext → Nat → α → ℝ≥0∞) (input : (LazyRevealProbe.World Coordinate).Domain)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) :
    ordinaryContinuationCharge post (OracleSpec.query input >>= next) context fuel =
      ordinaryChargeStep input (fun output => ordinaryContinuationCharge post (next output)) context fuel := rfl

theorem ordinaryContinuationCharge_bind {α β : Type}
    (post : DeferredContext → Nat → β → ℝ≥0∞)
    (left : OracleComp (LazyRevealProbe.World Coordinate) α)
    (next : α → OracleComp (LazyRevealProbe.World Coordinate) β) (context : DeferredContext) (fuel : Nat) :
    ordinaryContinuationCharge post (left >>= next) context fuel =
      ordinaryContinuationCharge (fun context fuel value => ordinaryContinuationCharge post (next value) context fuel)
        left context fuel := by
  induction left using OracleComp.inductionOn generalizing context fuel with
  | pure value => simp only [pure_bind, ordinaryContinuationCharge, OracleComp.construct_pure]
  | query_bind input continuation ih =>
      rw [bind_assoc, ordinaryContinuationCharge_query_bind, ordinaryContinuationCharge_query_bind]
      apply congrArg (fun tail => ordinaryChargeStep input tail context fuel)
      funext output nextContext remaining
      exact ih output nextContext remaining

theorem ordinaryContinuationCharge_zero_of_probeFree {α : Type}
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe 0) (context : DeferredContext) (fuel : Nat) :
    ordinaryContinuationCharge (fun _ _ _ => 0) computation context fuel = 0 := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value => rfl
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [ordinaryContinuationCharge_query_bind, ordinaryChargeStep.eq_def]
      cases input with
      | uniform n =>
          apply ENNReal.tsum_eq_zero.mpr
          intro output
          dsimp only
          rw [ih output (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output) context fuel, mul_zero]
      | hashOutput =>
          apply ENNReal.tsum_eq_zero.mpr
          intro output
          dsimp only
          rw [ih output (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output) context fuel, mul_zero]
      | ensure coordinate =>
          exact ih () (by simpa [LazyRevealProbe.IsProbe] using hbound.2 ())
            { context with state := context.state.ensure coordinate } fuel
      | peek coordinate =>
          exact ih _ (by simpa [LazyRevealProbe.IsProbe] using hbound.2 _ ) context fuel
      | publish coordinate =>
          exact ih () (by simpa [LazyRevealProbe.IsProbe] using hbound.2 ())
            { context with state := context.state.publish coordinate } fuel
      | probe coordinate candidate => simpa [LazyRevealProbe.IsProbe] using hbound.1
      | reveal coordinate =>
          dsimp only
          cases hvalue : context.state.values coordinate with
          | some output => exact ih output (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output) context fuel
          | none =>
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  apply ENNReal.tsum_eq_zero.mpr
                  intro output
                  dsimp only
                  rw [ih output (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output)]
                  simp only [ite_self, mul_zero]
              | position position =>
                  dsimp only
                  cases hprivate : context.values position with
                  | some output =>
                      dsimp only
                      rw [ih output (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output)]
                      exact ite_self _
                  | none =>
                      apply ENNReal.tsum_eq_zero.mpr
                      intro output
                      rw [ih output (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output)]
                      simp only [ite_self, mul_zero]

theorem ordinaryContinuationCharge_zero_bind_of_tail_probeFree {α β : Type}
    (left : OracleComp (LazyRevealProbe.World Coordinate) α)
    (next : α → OracleComp (LazyRevealProbe.World Coordinate) β)
    (hnext : ∀ value, (next value).IsQueryBoundP LazyRevealProbe.IsProbe 0)
    (context : DeferredContext) (fuel : Nat) :
    ordinaryContinuationCharge (fun _ _ _ => 0) (left >>= next) context fuel =
      ordinaryContinuationCharge (fun _ _ _ => 0) left context fuel := by
  rw [ordinaryContinuationCharge_bind]
  have hpost : (fun context fuel value => ordinaryContinuationCharge (fun _ _ _ => 0) (next value) context fuel) =
      (fun _ _ _ => 0) := by
    funext context fuel value
    exact ordinaryContinuationCharge_zero_of_probeFree (next value) (hnext value) context fuel
  rw [hpost]

theorem executeCandidate_ordinaryCharge_le (candidate : Option Probe) (cache : SplitHashCache)
    (context : DeferredContext) (fuel : Nat) :
    ordinaryContinuationCharge (fun _ _ _ => 0) ((executeCandidate? candidate).run cache) context fuel ≤
      unmaterializedCandidateCharge context.state candidate := by
  cases candidate with
  | none => simp [executeCandidate?, ordinaryContinuationCharge, unmaterializedCandidateCharge]
  | some candidate =>
      change ordinaryContinuationCharge (fun _ _ _ => 0)
        (LazyRevealProbe.probeQuery candidate.coordinate candidate.candidate >>= fun _ => pure ((), cache)) context fuel ≤ _
      rw [LazyRevealProbe.probeQuery, ordinaryContinuationCharge_query_bind, ordinaryChargeStep.eq_def]
      cases fuel with
      | zero => exact bot_le
      | succ remaining =>
          by_cases hrevealed : candidate.coordinate ∈ context.state.revealed
          · simp only [hrevealed, ↓reduceIte, unmaterializedCandidateCharge, ordinaryContinuationCharge,
              OracleComp.construct_pure, Nat.cast_zero, le_refl]
          · simp only [hrevealed, ↓reduceIte, unmaterializedCandidateCharge, ordinaryContinuationCharge,
              OracleComp.construct_pure, add_zero, le_refl]

theorem probingHashQueryAfterRootAwarePublicPlan_ordinaryCharge_add_materialized_le_one
    (parameter : PublicParameter) (input : HashInput) (publicState : LazyRevealProbe.State Coordinate)
    (plan : PlannedHashQuery) (cache : SplitHashCache) (context : DeferredContext) (fuel : Nat) :
    ordinaryContinuationCharge (fun _ _ _ => 0)
        ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run cache) context fuel +
      (materializedCandidateCharge context.state (rootAwareCandidateForPlan? parameter input plan) : ℝ≥0∞) ≤ 1 := by
  unfold probingHashQueryAfterRootAwarePublicPlan
  rw [StateT.run_bind, ordinaryContinuationCharge_zero_bind_of_tail_probeFree _
    (fun result : Unit × SplitHashCache => (probingHashQueryPublicAction parameter input publicState plan.action).run result.2)
    (fun result => probingHashQueryPublicAction_probeFree parameter input publicState plan.action result.2)]
  apply (add_le_add (executeCandidate_ordinaryCharge_le _ cache context fuel) le_rfl).trans
  rw [← Nat.cast_add, ← Nat.cast_one]
  exact Nat.cast_le.mpr (candidateCharge_sum_le_one context.state _)

theorem probEvent_safeOrdinary_le_continuationCharge {α : Type}
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (observe : (OtsSecretIndex → HashOutput) → DeferredContext → Nat → α → ProbComp Bool)
    (post : DeferredContext → Nat → α → ℝ≥0∞)
    (hpost : ∀ context fuel value,
      Pr[fun hit : Bool => hit = true | do
        let base ← sampleOtsHashTable
        observe (completedStartTable context.state base) context fuel value] ≤
      (post context fuel value + (context.state.unmaterializedPending.card : ℝ≥0∞)) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹)
    (context : DeferredContext) (fuel : Nat) :
    Pr[fun hit : Bool => hit = true |
      runDirectDetailedSafeOrdinaryWithCompletionTable observe context fuel computation] ≤
      (ordinaryContinuationCharge post computation context fuel +
        (context.state.unmaterializedPending.card : ℝ≥0∞)) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      rw [runDirectDetailedSafeOrdinaryWithCompletionTable_pure]
      exact hpost context fuel value
  | query_bind input next ih =>
      rw [ordinaryContinuationCharge_query_bind, ordinaryChargeStep.eq_def]
      cases input with
      | uniform n =>
          rw [runDirectDetailedSafeOrdinaryWithCompletionTable_uniform_query_bind]
          exact AdaptiveRevealProbe.probEvent_bind_le_expectedCharge _ _ _ _ _ fun output => ih output context fuel
      | hashOutput =>
          rw [runDirectDetailedSafeOrdinaryWithCompletionTable_hashOutput_query_bind]
          exact AdaptiveRevealProbe.probEvent_bind_le_expectedCharge _ _ _ _ _ fun output => ih output context fuel
      | ensure coordinate =>
          rw [runDirectDetailedSafeOrdinaryWithCompletionTable_ensure_query_bind]
          exact ih () { context with state := context.state.ensure coordinate } fuel
      | peek coordinate =>
          rw [runDirectDetailedSafeOrdinaryWithCompletionTable_peek_query_bind]
          exact ih (context.state.values coordinate) context fuel
      | publish coordinate =>
          rw [runDirectDetailedSafeOrdinaryWithCompletionTable_publish_query_bind]
          exact ih () { context with state := context.state.publish coordinate } fuel
      | probe coordinate candidate =>
          rw [runDirectDetailedSafeOrdinaryWithCompletionTable_probe_query_bind]
          cases fuel with
          | zero => simp
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · simp only [hrevealed, ↓reduceIte]
                exact ih () context remaining
              · simp only [hrevealed, ↓reduceIte]
                apply (ih () { context with state := context.state.addPending coordinate candidate } remaining).trans_eq
                rw [context.state.unmaterializedPending_card_addPending_eq_charge, Nat.cast_add]
                change (ordinaryContinuationCharge post (next ())
                    { context with state := context.state.addPending coordinate candidate } remaining +
                    ((context.state.unmaterializedPending.card : ℝ≥0∞) +
                      LazyRevealProbe.pendingProbeCharge context.state coordinate candidate)) * _ =
                  ((LazyRevealProbe.pendingProbeCharge context.state coordinate candidate : ℝ≥0∞) +
                    ordinaryContinuationCharge post (next ())
                      { context with state := context.state.addPending coordinate candidate } remaining +
                    context.state.unmaterializedPending.card) * _
                congr 1
                ac_rfl
      | reveal coordinate =>
          rw [runDirectDetailedSafeOrdinaryWithCompletionTable_reveal_query_bind]
          dsimp only
          cases hvalue : context.state.values coordinate with
          | some output => exact ih output context fuel
          | none =>
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  exact LazyRevealProbe.materialize_probability_le_charge context.state _ hvalue
                    (fun output state => runDirectDetailedSafeOrdinaryWithCompletionTable observe
                      { context with state := state } fuel (next output)) _
                    (fun output => ih output { context with state := context.state.materialize _ output } fuel)
              | position position =>
                  dsimp only
                  cases hprivate : context.values position with
                  | some output =>
                      by_cases hhit : context.state.hitAt (.position position) output
                      · simp only [hhit, ↓reduceIte, probEvent_pure, Bool.false_eq_true]
                        exact bot_le
                      · simp only [hhit, ↓reduceIte]
                        apply (ih output { context with state := context.state.materialize (.position position) output } fuel).trans
                        apply mul_le_mul' (add_le_add le_rfl _) le_rfl
                        rw [context.state.unmaterializedPending_materialize]
                        exact Nat.cast_le.mpr (context.state.unmaterializedPending_clearPending_card_le _)
                  | none =>
                      exact LazyRevealProbe.materialize_probability_le_charge context.state _ hvalue
                        (fun output state => runDirectDetailedSafeOrdinaryWithCompletionTable observe
                          { state := state, values := context.values.install position output } fuel (next output)) _
                        (fun output => ih output
                          { state := context.state.materialize _ output, values := context.values.install position output } fuel)

end SphincsSecurity.Concrete.OtsProbeSimulation

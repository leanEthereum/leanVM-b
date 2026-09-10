import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.CanonicalProbeCache

namespace SphincsSecurity.Concrete.CanonicalProbeRouting

open _root_.OracleComp OracleSpec RetainedObservation
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

abbrev HashStep := HashInput → ExternalMemory → SPMF (Option HashOutput × ExternalMemory)

noncomputable def externalImpl (step : HashStep) : QueryImpl OracleWorld (OptionT (StateT ExternalMemory SPMF))
  | .inl input => OptionT.mk <| StateT.mk fun memory =>
      (liftM (PMF.uniformOfFintype (unifSpec.Range input)) : SPMF _) >>= fun answer => pure (some answer, memory)
  | .inr input => OptionT.mk <| StateT.mk (step input)

noncomputable def externalRun {Result : Type} (step : HashStep) (computation : OracleComp OracleWorld Result)
    (memory : ExternalMemory) : SPMF (Option Result × ExternalMemory) :=
  (OptionT.run (simulateQ (externalImpl step) computation)).run memory

theorem externalRun_pure {Result : Type} (step : HashStep) (value : Result) (memory : ExternalMemory) :
    externalRun step (pure value) memory = pure (some value, memory) := by
  simp only [externalRun, simulateQ_pure, OptionT.run_pure, StateT.run_pure]

theorem externalRun_query_bind {Result : Type} (step : HashStep) (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld Result) (memory : ExternalMemory) :
    externalRun step (liftM (OracleWorld.query input) >>= next) memory =
      ((externalImpl step input).run.run memory >>= fun result =>
        match result.1 with
        | none => pure (none, result.2)
        | some answer => externalRun step (next answer) result.2) := by
  simp only [externalRun, simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind]
  apply congrArg (fun continuation => (externalImpl step input).run.run memory >>= continuation)
  funext result
  rcases result with ⟨answer, memory⟩
  cases answer <;> rfl

theorem externalRun_preserves {Result : Type} (step : HashStep) (property : ExternalMemory → Prop)
    (hstep : ∀ input memory, property memory → ∀ result, step input memory result ≠ 0 → property result.2)
    (computation : OracleComp OracleWorld Result) (memory : ExternalMemory) (hinitial : property memory)
    (result : Option Result × ExternalMemory) (hresult : externalRun step computation memory result ≠ 0) :
    property result.2 := by
  induction computation using OracleComp.inductionOn generalizing memory result with
  | pure value =>
      simp only [externalRun_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact hinitial
  | query_bind input next ih =>
      rw [externalRun_query_bind] at hresult
      cases input with
      | inl input =>
          simp only [externalImpl, OptionT.run_mk, StateT.run_mk, bind_assoc, pure_bind] at hresult
          obtain ⟨answer, _, hnext⟩ := (bind_nonzero _ _ _).mp hresult
          exact ih answer memory hinitial result hnext
      | inr input =>
          simp only [externalImpl, OptionT.run_mk, StateT.run_mk] at hresult
          obtain ⟨⟨answer, after⟩, hanswer, hnext⟩ := (bind_nonzero _ _ _).mp hresult
          have hafter := hstep input memory hinitial (answer, after) hanswer
          cases answer with
          | none =>
              simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hnext
              subst result
              exact hafter
          | some answer => exact ih answer after hafter result hnext

theorem externalRun_congr {Result : Type} (left right : HashStep) (property : ExternalMemory → Prop)
    (heq : ∀ input memory, property memory → left input memory = right input memory)
    (hstep : ∀ input memory, property memory → ∀ result, left input memory result ≠ 0 → property result.2)
    (computation : OracleComp OracleWorld Result) (memory : ExternalMemory) (hinitial : property memory) :
    externalRun left computation memory = externalRun right computation memory := by
  induction computation using OracleComp.inductionOn generalizing memory with
  | pure value => simp only [externalRun_pure]
  | query_bind input next ih =>
      rw [externalRun_query_bind, externalRun_query_bind]
      cases input with
      | inl input =>
          simp only [externalImpl, OptionT.run_mk, StateT.run_mk, bind_assoc, pure_bind]
          apply congrArg (fun continuation => (liftM (PMF.uniformOfFintype (unifSpec.Range input)) : SPMF _) >>= continuation)
          funext answer
          exact ih answer memory hinitial
      | inr input =>
          simp only [externalImpl, OptionT.run_mk, StateT.run_mk]
          rw [← heq input memory hinitial]
          apply RetainedObservation.bind_congr
          rintro ⟨answer, after⟩ hanswer
          cases answer with
          | none => rfl
          | some answer => exact ih answer after (hstep input memory hinitial (some answer, after) hanswer)

def IsHashQuery : OracleWorld.Domain → Prop
  | .inl _ => False
  | .inr _ => True

theorem externalRun_bind_const {Result Other : Type} (step : HashStep)
    (hstep : ∀ input memory (next : SPMF Other), (step input memory >>= fun _ => next) = next)
    (computation : OracleComp OracleWorld Result) (memory : ExternalMemory) (after : SPMF Other) :
    (externalRun step computation memory >>= fun _ => after) = after := by
  induction computation using OracleComp.inductionOn generalizing memory with
  | pure value => simp only [externalRun_pure, pure_bind]
  | query_bind input next ih =>
      rw [externalRun_query_bind, bind_assoc]
      cases input with
      | inl input =>
          simp only [externalImpl, OptionT.run_mk, StateT.run_mk, bind_assoc, pure_bind, ih]
          exact lift_bind_const _ after
      | inr input =>
          simp only [externalImpl, OptionT.run_mk, StateT.run_mk]
          calc
            _ = (step input memory >>= fun _ => after) := by
              apply congrArg (fun continuation => step input memory >>= continuation)
              funext result
              rcases result with ⟨answer, memory⟩
              cases answer with
              | none => exact pure_bind _ _
              | some answer => exact ih answer memory
            _ = after := hstep input memory after

theorem externalRun_hashCalls_le {Result : Type} (step : HashStep) (property : ExternalMemory → Prop)
    (hstep : ∀ input memory, property memory → ∀ result, step input memory result ≠ 0 →
      property result.2 ∧ result.2.hashCalls = memory.hashCalls + 1)
    (computation : OracleComp OracleWorld Result) (memory : ExternalMemory) (hinitial : property memory)
    (budget : Nat) (hbound : computation.IsQueryBoundP IsHashQuery budget)
    (result : Option Result × ExternalMemory) (hresult : externalRun step computation memory result ≠ 0) :
    result.2.hashCalls ≤ memory.hashCalls + budget := by
  induction computation using OracleComp.inductionOn generalizing memory budget result with
  | pure value =>
      simp only [externalRun_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact Nat.le_add_right _ _
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      rw [externalRun_query_bind] at hresult
      cases input with
      | inl input =>
          simp only [IsHashQuery, if_false] at hbound
          simp only [externalImpl, OptionT.run_mk, StateT.run_mk, bind_assoc, pure_bind] at hresult
          obtain ⟨answer, _, hnext⟩ := (bind_nonzero _ _ _).mp hresult
          exact ih answer memory hinitial budget (hbound.2 answer) result hnext
      | inr input =>
          simp only [IsHashQuery, if_true, not_true_eq_false, false_or] at hbound
          have hpos : 0 < budget := hbound.1
          simp only [externalImpl, OptionT.run_mk, StateT.run_mk] at hresult
          obtain ⟨⟨answer, after⟩, hanswer, hnext⟩ := (bind_nonzero _ _ _).mp hresult
          have hafter := hstep input memory hinitial (answer, after) hanswer
          have hcost : after.hashCalls = memory.hashCalls + 1 := hafter.2
          cases answer with
          | none =>
              simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hnext
              subst result
              change after.hashCalls ≤ memory.hashCalls + budget
              omega
          | some answer =>
              have hnext := ih answer after hafter.1 (budget - 1) (hbound.2 answer) result hnext
              omega

variable (parameter : PublicParameter) (words : OtsReferenceWords)
  (disclosed : Index → FtsTree → FtsLeaf → Prop) (known actual : Labels)
  (replies publicReplies : CanonicalGraphLabels)
  (outside : HashInput → ExternalMemory → PMF HashOutput)

noncomputable def stoppedExternalRun {Result : Type} (computation : OracleComp OracleWorld Result) (memory : ExternalMemory) :=
  externalRun (fun input memory => stoppedStep parameter words disclosed known actual replies input (outside input memory) memory)
    computation memory

noncomputable def routedExternalRun {Result : Type} (computation : OracleComp OracleWorld Result) (memory : ExternalMemory) :=
  externalRun (fun input memory => routedStep parameter words disclosed known actual publicReplies input (outside input memory) memory)
    computation memory

theorem stoppedExternalRun_eq_routed {Result : Type}
    (hagrees : PublicAgreement words disclosed known actual)
    (hreplies : ∀ position, ¬CanonicalCoordinate.Hidden words disclosed (.graph position) →
      publicReplies position = replies position)
    (computation : OracleComp OracleWorld Result) (memory : ExternalMemory)
    (hclean : CacheClean parameter words disclosed actual memory.cache) :
    stoppedExternalRun parameter words disclosed known actual replies outside computation memory =
      routedExternalRun parameter words disclosed known actual publicReplies outside computation memory := by
  apply externalRun_congr _ _ (fun memory => CacheClean parameter words disclosed actual memory.cache)
  · intro input memory hclean
    exact stoppedStep_eq_routed parameter words disclosed known actual hagrees replies publicReplies hreplies
      input (outside input memory) memory hclean
  · intro input memory hclean result hresult
    exact (stoppedStep_preserves hclean result hresult).1
  · exact hclean

theorem stoppedExternalRun_cacheClean {Result : Type}
    (computation : OracleComp OracleWorld Result) (memory : ExternalMemory)
    (hclean : CacheClean parameter words disclosed actual memory.cache)
    (result : Option Result × ExternalMemory)
    (hresult : stoppedExternalRun parameter words disclosed known actual replies outside computation memory result ≠ 0) :
    CacheClean parameter words disclosed actual result.2.cache :=
  externalRun_preserves _ (fun memory => CacheClean parameter words disclosed actual memory.cache)
    (fun _ _ hclean result hresult => (stoppedStep_preserves hclean result hresult).1)
    computation memory hclean result hresult

theorem stoppedExternalRun_hashCalls_le {Result : Type}
    (computation : OracleComp OracleWorld Result) (memory : ExternalMemory)
    (hclean : CacheClean parameter words disclosed actual memory.cache)
    (budget : Nat) (hbound : computation.IsQueryBoundP IsHashQuery budget)
    (result : Option Result × ExternalMemory)
    (hresult : stoppedExternalRun parameter words disclosed known actual replies outside computation memory result ≠ 0) :
    result.2.hashCalls ≤ memory.hashCalls + budget :=
  externalRun_hashCalls_le _ (fun memory => CacheClean parameter words disclosed actual memory.cache)
    (fun _ _ hclean result hresult => ⟨(stoppedStep_preserves hclean result hresult).1,
      (stoppedStep_preserves hclean result hresult).2.1⟩)
    computation memory hclean budget hbound result hresult

theorem stoppedExternalRun_probes_le_hashCalls {Result : Type}
    (computation : OracleComp OracleWorld Result) (memory : ExternalMemory)
    (hclean : CacheClean parameter words disclosed actual memory.cache) (hinitial : memory.probes ≤ memory.hashCalls)
    (result : Option Result × ExternalMemory)
    (hresult : stoppedExternalRun parameter words disclosed known actual replies outside computation memory result ≠ 0) :
    result.2.probes ≤ result.2.hashCalls := by
  have h := externalRun_preserves _
    (fun memory => CacheClean parameter words disclosed actual memory.cache ∧ memory.probes ≤ memory.hashCalls)
    (fun _ _ h result hresult => ⟨(stoppedStep_preserves h.1 result hresult).1,
      stoppedStep_probes_le_hashCalls h.1 h.2 result hresult⟩)
    computation memory ⟨hclean, hinitial⟩ result hresult
  exact h.2

theorem stoppedExternalRun_probes_le {Result : Type}
    (computation : OracleComp OracleWorld Result) (memory : ExternalMemory)
    (hclean : CacheClean parameter words disclosed actual memory.cache) (hinitial : memory.probes ≤ memory.hashCalls)
    (budget : Nat) (hbound : computation.IsQueryBoundP IsHashQuery budget)
    (result : Option Result × ExternalMemory)
    (hresult : stoppedExternalRun parameter words disclosed known actual replies outside computation memory result ≠ 0) :
    result.2.probes ≤ memory.hashCalls + budget :=
  (stoppedExternalRun_probes_le_hashCalls parameter words disclosed known actual replies outside
    computation memory hclean hinitial result hresult).trans
    (stoppedExternalRun_hashCalls_le parameter words disclosed known actual replies outside
      computation memory hclean budget hbound result hresult)

theorem stoppedExternalRun_bind_const {Result Other : Type}
    (computation : OracleComp OracleWorld Result) (memory : ExternalMemory) (after : SPMF Other) :
    (stoppedExternalRun parameter words disclosed known actual replies outside computation memory >>= fun _ => after) = after :=
  externalRun_bind_const _
    (fun input memory next => stoppedStep_bind_const parameter words disclosed known actual replies input
      (outside input memory) memory next)
    computation memory after

end SphincsSecurity.Concrete.CanonicalProbeRouting

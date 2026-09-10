import SphincsSecurity.Proof.RetainedResidualBudget
import SphincsSecurity.Proof.FtsProbeVerifierSource

namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open InterleavedResidual (Routing)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

theorem fixedSourceRun_bind {A B : Type} {inputs : Finset HashInput} (context : Context inputs)
    (computation : OracleComp (OracleWorld + SigningSpec) A)
    (next : A → OracleComp (OracleWorld + SigningSpec) B) (memory : Memory) :
    fixedSourceRun context (computation >>= next) memory =
      (fixedSourceRun context computation memory >>= fun result =>
        result.1.elim (pure (none, result.2)) (fun value => fixedSourceRun context (next value) result.2)) := by
  simp only [fixedSourceRun, simulateQ_bind, OptionT.run_bind, Option.elimM, StateT.run_bind]
  apply congrArg (_ >>= ·)
  funext result
  rcases result with ⟨value, after⟩
  cases value <;> rfl

theorem fixedSourceRun_map {A B : Type} {inputs : Finset HashInput} (context : Context inputs)
    (f : A → B) (computation : OracleComp (OracleWorld + SigningSpec) A) (memory : Memory) :
    fixedSourceRun context (f <$> computation) memory =
      (fun result => (f <$> result.1, result.2)) <$> fixedSourceRun context computation memory := by
  rw [map_eq_bind_pure_comp, fixedSourceRun_bind, map_eq_bind_pure_comp]
  apply congrArg (_ >>= ·)
  funext result
  rcases result with ⟨value, after⟩
  cases value <;> simp only [Option.elim_none, Option.elim_some, Function.comp_def, fixedSourceRun_pure] <;> rfl

theorem fixedSourceImpl_world_run {inputs : Finset HashInput} (context : Context inputs)
    (input : OracleWorld.Domain) (memory : Memory) :
    (fixedSourceImpl context (.inl input)).run.run memory =
      (fixedByteImpl context.key.parameter context.words context.auxiliary.selections memory.routing context.actual context.oracle input).run.run memory := by
  simp only [fixedSourceImpl, OptionT.run_mk, StateT.run_mk, fixedByteRun, simulateQ_spec_query]

theorem fixedByteImpl_history (parameter : PublicParameter) (words : OtsReferenceWords) (selections : ReferenceFamily)
    (routing : Routing) (actual : Labels) (oracle : QueryImpl HashSpec Id) (input : OracleWorld.Domain) (memory : Memory)
    (result : Option (OracleWorld.Range input) × Memory)
    (hresult : (fixedByteImpl parameter words selections routing actual oracle input).run.run memory result ≠ 0) :
    result.2.history = memory.history := by
  cases input with
  | inl input =>
      simp only [fixedByteImpl, OptionT.run_mk, StateT.run_mk, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨value, _, hresult⟩ := hresult
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      rfl
  | inr input =>
      simp only [fixedByteImpl, OptionT.run_mk, StateT.run_mk, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact afterReply_history parameter memory input _ _

theorem fixedByteRun_history {Result : Type} (parameter : PublicParameter) (words : OtsReferenceWords) (selections : ReferenceFamily)
    (routing : Routing) (actual : Labels) (oracle : QueryImpl HashSpec Id) (computation : OracleComp OracleWorld Result)
    (memory : Memory) (result : Option Result × Memory)
    (hresult : fixedByteRun parameter words selections routing actual oracle computation memory result ≠ 0) :
    result.2.history = memory.history := by
  induction computation using OracleComp.inductionOn generalizing memory result with
  | pure value =>
      simp only [fixedByteRun_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      rfl
  | query_bind input next ih =>
      rw [fixedByteRun_query_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨⟨answer, middle⟩, hmiddle, hresult⟩ := hresult
      have hhistory := fixedByteImpl_history parameter words selections routing actual oracle input memory (answer, middle) hmiddle
      cases answer with
      | none =>
          simp only [Option.elim_none, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          exact hhistory
      | some answer => exact (ih answer middle result hresult).trans hhistory

theorem fixedSourceRun_world {Result : Type} {inputs : Finset HashInput} (context : Context inputs)
    (computation : OracleComp OracleWorld Result) (memory : Memory) :
    fixedSourceRun context (FtsProbeSimulation.liftOracleWorldLeft computation) memory =
      fixedByteRun context.key.parameter context.words context.auxiliary.selections memory.routing
        context.actual context.oracle computation memory := by
  induction computation using OracleComp.inductionOn generalizing memory with
  | pure value => simp only [FtsProbeSimulation.liftOracleWorldLeft, liftM_pure, fixedSourceRun_pure, fixedByteRun_pure]
  | query_bind input next ih =>
      rw [FtsProbeSimulation.liftOracleWorldLeft_query_bind, fixedSourceRun_query_bind, fixedByteRun_query_bind, fixedSourceImpl_world_run]
      apply RetainedObservation.bind_congr
      rintro ⟨answer, after⟩ hafter
      have hrouting := congrArg Prod.fst (fixedByteImpl_history context.key.parameter context.words context.auxiliary.selections
        memory.routing context.actual context.oracle input memory (answer, after) hafter)
      change after.routing = memory.routing at hrouting
      cases answer with
      | none => rfl
      | some answer =>
          simp only [Option.elim_some]
          rw [ih answer after, hrouting]

end SphincsSecurity.Concrete.RetainedResidual

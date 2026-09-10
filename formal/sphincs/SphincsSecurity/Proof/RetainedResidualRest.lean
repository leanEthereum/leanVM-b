import SphincsSecurity.Proof.RetainedResidualWorld
import SphincsSecurity.Proof.RetainedWorldCoverBudget

namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open FtsProbeSimulation (unloggedRetainedRestComputation liftOracleWorldLeft)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

def finishRest (result : Option (Forgery × Bool) × Memory) : Option Bool × Memory :=
  (result.1.map (fun value => decide (SigningTranscript.Valid result.2.log ∧ ¬SigningTranscript.Contains result.2.log value.1) && value.2), result.2)

noncomputable def finalizeProgram {inputs : Finset HashInput} (context : Context inputs) (forgery : Forgery) : OracleComp (World inputs) Bool := do
  let log ← signingTranscript inputs
  let checked ← externalProgram inputs context.key.parameter context.words context.auxiliary.selections
    (scheme.verify ⟨context.key.root, context.key.parameter⟩ forgery.message forgery.signature)
  pure (decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && checked)

theorem observedRun_map {A B : Type} {inputs : Finset HashInput} (context : Context inputs)
    (f : A → B) (computation : OracleComp (World inputs) A) (state : State inputs) :
    observedRun context.environment context.actual context.auxiliary.seed (f <$> computation) state =
      (fun result => (f <$> result.1, result.2)) <$> observedRun context.environment context.actual context.auxiliary.seed computation state := by
  rw [map_eq_bind_pure_comp]
  unfold Context.environment
  rw [observedRun_bind, map_eq_bind_pure_comp]
  apply congrArg (_ >>= ·)
  funext result
  rcases result with ⟨value, after⟩
  cases value <;> simp only [Option.elim_none, Option.elim_some, Function.comp_def, observedRun, runWith_pure] <;> rfl

theorem observedRun_transcript_bind {Result : Type} {inputs : Finset HashInput} (context : Context inputs)
    (next : QueryLog SigningSpec → OracleComp (World inputs) Result) (state : State inputs) :
    observedRun context.environment context.actual context.auxiliary.seed (signingTranscript inputs >>= next) state =
      observedRun context.environment context.actual context.auxiliary.seed (next state.memory.log) state := by
  rw [signingTranscript, observedRun, runWith_query_bind]
  simp only [observedImpl, Context.environment, environment, OptionT.run_mk, StateT.run_mk,
    SPMF.lift_pure, pure_bind, Option.elim_some, observedRun]

theorem observedRun_finalize_memory {inputs : Finset HashInput} (context : Context inputs) (forgery : Forgery)
    (hinputs : hashInputs (scheme.verify ⟨context.key.root, context.key.parameter⟩ forgery.message forgery.signature) ⊆ inputs)
    (state : State inputs) (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcompatible : Compatible context state.memory) :
    forgetState <$> observedRun context.environment context.actual context.auxiliary.seed (finalizeProgram context forgery) state =
      finishRest <$> fixedSourceRun context
        ((fun checked => (forgery, checked)) <$> liftOracleWorldLeft (scheme.verify ⟨context.key.root, context.key.parameter⟩ forgery.message forgery.signature)) state.memory := by
  rw [finalizeProgram, observedRun_transcript_bind]
  change forgetState <$> observedRun context.environment context.actual context.auxiliary.seed
    ((fun checked => decide (SigningTranscript.Valid state.memory.log ∧ ¬SigningTranscript.Contains state.memory.log forgery) && checked) <$>
      externalProgram inputs context.key.parameter context.words context.auxiliary.selections
        (scheme.verify ⟨context.key.root, context.key.parameter⟩ forgery.message forgery.signature)) state = _
  rw [observedRun_map, fixedSourceRun_map, fixedSourceRun_world]
  have h := context.external_memory _ hinputs state hcovered hcompatible
  have hmap := congrArg (fun law : SPMF (Option Bool × Memory) =>
    (fun result => ((fun checked => decide (SigningTranscript.Valid state.memory.log ∧ ¬SigningTranscript.Contains state.memory.log forgery) && checked) <$> result.1, result.2)) <$> law) h
  simp only [Functor.map_map, forgetState] at hmap
  simp only [Functor.map_map, forgetState]
  rw [hmap]
  simp only [map_eq_bind_pure_comp, Function.comp_def]
  apply RetainedObservation.bind_congr
  rintro ⟨checked, after⟩ hafter
  have hhistory := fixedByteRun_history context.key.parameter context.words context.auxiliary.selections state.memory.routing
    context.actual context.oracle _ state.memory (checked, after) hafter
  have hlog := congrArg (fun history => history.2.1) hhistory
  change after.log = state.memory.log at hlog
  cases checked <;> simp only [finishRest, hlog] <;> rfl

theorem observedRun_rest_memory {inputs : Finset HashInput} (context : Context inputs) (adversary : Adversary)
    (hinputs : sourceInputs context.key (adversary.main ⟨context.key.root, context.key.parameter⟩) ⊆ inputs)
    (hverify : ∀ forgery : Forgery, hashInputs (scheme.verify ⟨context.key.root, context.key.parameter⟩ forgery.message forgery.signature) ⊆ inputs)
    (state : State inputs) (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcompatible : Compatible context state.memory) :
    forgetState <$> observedRun context.environment context.actual context.auxiliary.seed
      (restProgram inputs context.key.parameter context.key.root context.words context.auxiliary.selections adversary) state =
      finishRest <$> fixedSourceRun context (unloggedRetainedRestComputation adversary ⟨context.key.root, context.key.parameter⟩) state.memory := by
  change forgetState <$> observedRun context.environment context.actual context.auxiliary.seed
    (simulateQ (adversaryImpl inputs context.key.parameter context.key.root context.words context.auxiliary.selections)
      (adversary.main ⟨context.key.root, context.key.parameter⟩) >>= finalizeProgram context) state = _
  unfold Context.environment
  rw [observedRun_bind, map_bind, unloggedRetainedRestComputation, fixedSourceRun_bind, map_bind,
    ← observedRun_source_memory context _ hinputs state hcovered hcompatible, bind_map_left]
  apply RetainedObservation.bind_congr
  rintro ⟨forgery, after⟩ hafter
  cases forgery with
  | none => simp only [Option.elim_none, map_pure, forgetState, finishRest, Option.map_none]
  | some forgery =>
      have hcovered' := observedRun_rowsCovered context.key.parameter inputs context.encoding context.words context.publicReplies
        context.auxiliary.selections context.auxiliary.rows context.actual context.auxiliary.seed _ state hcovered (some forgery, after) hafter
      have hcompatible' := observedRun_source_compatible context _ hinputs state hcovered hcompatible forgery after hafter
      exact observedRun_finalize_memory context forgery (hverify forgery) after hcovered' hcompatible'

theorem observedRun_rest_hashCalls_le {inputs : Finset HashInput} (context : Context inputs) (adversary : Adversary)
    (hinputs : sourceInputs context.key (adversary.main ⟨context.key.root, context.key.parameter⟩) ⊆ inputs)
    (hverify : ∀ forgery : Forgery, hashInputs (scheme.verify ⟨context.key.root, context.key.parameter⟩ forgery.message forgery.signature) ⊆ inputs)
    (q : Nat) (hbound : (gameRest scheme adversary ⟨context.key.root, context.key.parameter⟩ context.key).IsQueryBoundP (· matches .inr _) q)
    (state : State inputs) (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcompatible : Compatible context state.memory) (result : Option Bool × State inputs)
    (hresult : observedRun context.environment context.actual context.auxiliary.seed
      (restProgram inputs context.key.parameter context.key.root context.words context.auxiliary.selections adversary) state result ≠ 0) :
    result.2.memory.external.hashCalls ≤ state.memory.external.hashCalls + q := by
  have h := map_nonzero _ forgetState result hresult
  rw [observedRun_rest_memory context adversary hinputs hverify state hcovered hcompatible,
    map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at h
  obtain ⟨source, hsource, heq⟩ := h
  simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at heq
  have hcost := fixedSourceRun_hashCalls_le context _ q
    (FtsProbeSimulation.expanded_unloggedRetainedRest_queryBound adversary context.key q hbound) state.memory source hsource
  have hmemory := congrArg Prod.snd heq
  change result.2.memory = source.2 at hmemory
  rw [hmemory]
  exact hcost

end SphincsSecurity.Concrete.RetainedResidual

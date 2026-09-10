import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.ResidualByteRun

namespace SphincsSecurity.Concrete.ResidualByteFrontend

open _root_.OracleComp OracleSpec CanonicalProbeRouting HiddenLabelObservation ResidualByteAction
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs
set_option backward.isDefEq.respectTransparency false

noncomputable def checkedResult {Memory : Type} (reject : HashInput → HashOutput → Prop) (input : HashInput)
    (result : Option HashOutput × Memory) : Option HashOutput × Memory :=
  (result.1.bind (fun answer => if reject input answer then none else some answer), result.2)

noncomputable def checkedHashQuery {inputs : Finset HashInput} (reject : HashInput → HashOutput → Prop)
    (input : inputs) : OracleComp (World inputs) HashOutput := do
  let answer ← hashQuery input
  if reject input.val answer then liftM ((World inputs).query (.inl .stop)) else pure answer

noncomputable def checkedTranslate (inputs : Finset HashInput) (reject : HashInput → HashOutput → Prop) :
    QueryImpl OracleWorld (OracleComp (World inputs))
  | .inl input => liftM ((World inputs).query (.inl (.random input)))
  | .inr input => if hin : input ∈ inputs then checkedHashQuery reject ⟨input, hin⟩ else pure (0 : HashOutput)

theorem checkedExternalRun_hashCalls_le {Result : Type} (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known actual : Labels)
    (reject : HashInput → HashOutput → Prop) (oracle : HashInput → HashOutput)
    (computation : OracleComp OracleWorld Result) (memory : ExternalMemory)
    (budget : Nat) (hbound : computation.IsQueryBoundP IsHashQuery budget)
    (result : Option Result × ExternalMemory)
    (hresult : externalRun (fun input memory => pure (checkedResult reject input
      (fixedStep parameter words disclosed known actual oracle input memory))) computation memory result ≠ 0) :
    result.2.hashCalls ≤ memory.hashCalls + budget := by
  apply externalRun_hashCalls_le _ (fun _ => True) _ computation memory trivial budget hbound result hresult
  intro input memory _ result hresult
  simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
  subst result
  exact ⟨trivial, fixedStep_hashCalls parameter words disclosed known actual oracle input memory⟩

variable (parameter : PublicParameter) (inputs : Finset HashInput) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels) (actions : inputs → Action inputs)

theorem observedRun_stop (actual : Labels) (seed : inputs → HashOutput) (state : State inputs) :
    AdaptiveResidualLabels.observedRun (environment parameter inputs words disclosed known actions) actual seed
      (liftM ((World inputs).query (.inl .stop)) : OracleComp (World inputs) HashOutput) state = pure (none, state) := by
  simp only [AdaptiveResidualLabels.observedRun, AdaptiveResidualLabels.runWith, simulateQ_spec_query,
    AdaptiveResidualLabels.observedImpl, environment, OptionT.run_mk, StateT.run_mk, SPMF.lift_pure, pure_bind]

theorem observedRun_checkedHashQuery (reject : HashInput → HashOutput → Prop) (actual : Labels)
    (seed : inputs → HashOutput) (input : inputs) (state : State inputs) :
    AdaptiveResidualLabels.observedRun (environment parameter inputs words disclosed known actions) actual seed
      (checkedHashQuery reject input) state =
        pure (checkedResult reject input.val (hashQueryResult parameter inputs words disclosed known actions actual seed input state)) := by
  rw [checkedHashQuery, observedRun_bind, observedRun_hashQuery, pure_bind]
  generalize hresult : hashQueryResult parameter inputs words disclosed known actions actual seed input state = result
  rcases result with ⟨answer, after⟩
  cases answer with
  | none => rfl
  | some answer =>
      dsimp only [Option.elim_some, checkedResult, Option.bind_some]
      by_cases hreject : reject input.val answer
      · simp only [if_pos hreject, observedRun_stop]
      · simp only [if_neg hreject, AdaptiveResidualLabels.observedRun, AdaptiveResidualLabels.runWith_pure]

noncomputable def checkedByteRun {Result : Type} (reject : HashInput → HashOutput → Prop) (actual : Labels)
    (seed : inputs → HashOutput) (computation : OracleComp OracleWorld Result) (state : State inputs) :
    SPMF (Option Result × State inputs) :=
  AdaptiveResidualLabels.observedRun (environment parameter inputs words disclosed known actions) actual seed
    (simulateQ (checkedTranslate inputs reject) computation) state

theorem checkedByteRun_pure {Result : Type} (reject : HashInput → HashOutput → Prop) (actual : Labels)
    (seed : inputs → HashOutput) (value : Result) (state : State inputs) :
    checkedByteRun parameter inputs words disclosed known actions reject actual seed (pure value) state = pure (some value, state) := by
  simp only [checkedByteRun, simulateQ_pure, AdaptiveResidualLabels.observedRun, AdaptiveResidualLabels.runWith_pure]

theorem checkedByteRun_random_bind {Result : Type} (reject : HashInput → HashOutput → Prop) (actual : Labels)
    (seed : inputs → HashOutput) (input : unifSpec.Domain)
    (next : unifSpec.Range input → OracleComp OracleWorld Result) (state : State inputs) :
    checkedByteRun parameter inputs words disclosed known actions reject actual seed
      (liftM (OracleWorld.query (.inl input)) >>= next) state =
        ((liftM (PMF.uniformOfFintype (unifSpec.Range input)) : SPMF _) >>= fun answer =>
          checkedByteRun parameter inputs words disclosed known actions reject actual seed (next answer) state) := by
  simp only [checkedByteRun, simulateQ_bind, simulateQ_spec_query, checkedTranslate]
  rw [AdaptiveResidualLabels.observedRun, AdaptiveResidualLabels.runWith_query_bind]
  simp only [AdaptiveResidualLabels.observedImpl, environment, OptionT.run_mk, StateT.run_mk,
    ← PMF.monad_map_eq_map, liftM_map, bind_map_left, bind_assoc, pure_bind, Option.elim_some]
  rfl

theorem checkedByteRun_hash_bind {Result : Type} (reject : HashInput → HashOutput → Prop) (actual : Labels)
    (seed : inputs → HashOutput) (input : HashInput) (hin : input ∈ inputs)
    (next : HashOutput → OracleComp OracleWorld Result) (state : State inputs) :
    checkedByteRun parameter inputs words disclosed known actions reject actual seed
      (liftM (OracleWorld.query (.inr input)) >>= next) state =
        let result := checkedResult reject input
          (hashQueryResult parameter inputs words disclosed known actions actual seed ⟨input, hin⟩ state)
        result.1.elim (pure (none, result.2)) (fun answer =>
          checkedByteRun parameter inputs words disclosed known actions reject actual seed (next answer) result.2) := by
  simp only [checkedByteRun, simulateQ_bind, simulateQ_spec_query, checkedTranslate, dif_pos hin]
  rw [observedRun_bind, observedRun_checkedHashQuery, pure_bind]
  rfl

theorem checkedByteRun_eq_fixed {Result : Type} (reject : HashInput → HashOutput → Prop) (actual : Labels)
    (seed : inputs → HashOutput) (oracle : HashInput → HashOutput)
    (hlocal : ∀ input, Local input (actions input))
    (hfresh : ∀ input : inputs, ResidualByteAction.eval actual seed (actions input) =
      fixedAnswer parameter words disclosed actual oracle input.val)
    (computation : OracleComp OracleWorld Result) (hinputs : hashInputs computation ⊆ inputs)
    (state : State inputs) (hcovered : RowsCovered inputs state)
    (hmatches : CacheMatches oracle state.memory.cache) (hclean : CacheClean parameter words disclosed actual state.memory.cache) :
    forget <$> checkedByteRun parameter inputs words disclosed known actions reject actual seed computation state =
      externalRun (fun input memory => pure (checkedResult reject input
        (fixedStep parameter words disclosed known actual oracle input memory))) computation state.memory := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [checkedByteRun_pure, externalRun_pure, map_pure, forget]
  | query_bind input next ih =>
      have hnext : ∀ answer, hashInputs (next answer) ⊆ inputs :=
        fun answer => (hashInputs_next_subset input next answer).trans hinputs
      cases input with
      | inl input =>
          rw [checkedByteRun_random_bind, externalRun_query_bind]
          simp only [externalImpl, OptionT.run_mk, StateT.run_mk, bind_assoc, pure_bind, map_bind]
          apply congrArg ((liftM (PMF.uniformOfFintype (unifSpec.Range input)) : SPMF _) >>= ·)
          funext answer
          exact ih answer (hnext answer) state hcovered hmatches hclean
      | inr input =>
          change HashOutput → OracleComp OracleWorld Result at next
          have hmem := mem_hashInputs_hash_bind (α := Result) input next
          have hin : input ∈ inputs := hinputs hmem
          rw [checkedByteRun_hash_bind parameter inputs words disclosed known actions reject actual seed input hin,
            externalRun_query_bind]
          simp only [externalImpl, OptionT.run_mk, StateT.run_mk, pure_bind]
          have hproject := hashQueryResult_eq_fixed parameter inputs words disclosed known actions
            actual seed oracle ⟨input, hin⟩ state hcovered (hlocal ⟨input, hin⟩) hmatches hclean (hfresh ⟨input, hin⟩)
          dsimp only at hproject
          rw [← hproject]
          have hafter := fixedStep_preserves parameter words disclosed known actual oracle input state.memory hmatches hclean
          rw [← hproject] at hafter
          have hcovered' := hashQueryResult_rowsCovered parameter inputs words disclosed known actions
            actual seed state hcovered ⟨input, hin⟩
          generalize hresult : hashQueryResult parameter inputs words disclosed known actions actual seed ⟨input, hin⟩ state = result at *
          rcases result with ⟨answer, after⟩
          cases answer with
          | none => simp only [checkedResult, Option.bind_none, Option.elim_none, map_pure, forget]
          | some answer =>
              simp only [checkedResult, Option.bind_some]
              split
              · simp only [Option.elim_none, map_pure, forget]
              · exact ih answer (hnext answer) after hcovered' hafter.1 hafter.2.1

end SphincsSecurity.Concrete.ResidualByteFrontend

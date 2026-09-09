import SphincsSecurity.Proof.PrefixBytePrior

namespace SphincsSecurity.Concrete.ResidualByteFrontend

open _root_.OracleComp OracleSpec ENNReal CanonicalProbeRouting HiddenLabelObservation ResidualByteAction
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

def ReplyClean (reject : HashInput → HashOutput → Prop) (cache : ExternalCache) : Prop :=
  ∀ input answer, cache input = some answer → ¬reject input answer

theorem replyClean_empty (reject : HashInput → HashOutput → Prop) : ReplyClean reject (fun _ => none) := by
  intro input answer hcache
  cases hcache

theorem replyClean_store (reject : HashInput → HashOutput → Prop) (cache : ExternalCache)
    (hclean : ReplyClean reject cache) (input : HashInput) (answer : HashOutput) (hsafe : ¬reject input answer) :
    ReplyClean reject (Function.update cache input (some answer)) := by
  intro other value hcache
  by_cases heq : other = input
  · subst other
    rw [Function.update_self, Option.some.injEq] at hcache
    subst value
    exact hsafe
  · rw [Function.update_of_ne heq] at hcache
    exact hclean other value hcache

theorem checkedFixedStep_replyClean (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known actual : Labels)
    (reject : HashInput → HashOutput → Prop) (oracle : HashInput → HashOutput)
    (input : HashInput) (memory : ExternalMemory) (hclean : ReplyClean reject memory.cache)
    (answer : HashOutput)
    (hanswer : (checkedResult reject input (fixedStep parameter words disclosed known actual oracle input memory)).1 = some answer) :
    ReplyClean reject (checkedResult reject input (fixedStep parameter words disclosed known actual oracle input memory)).2.cache := by
  unfold checkedResult fixedStep at hanswer ⊢
  cases hfixed : fixedAnswer parameter words disclosed actual oracle input with
  | none => simp only [hfixed, Option.bind_none, reduceCtorEq] at hanswer
  | some output =>
      simp only [hfixed, Option.bind_some, Option.elim_some] at hanswer ⊢
      split at hanswer
      · contradiction
      · rename_i hsafe
        exact replyClean_store reject memory.cache hclean input output hsafe

theorem externalRun_preserves_live {Result : Type} (step : HashStep) (property : ExternalMemory → Prop)
    (hstep : ∀ input memory, property memory → ∀ result, step input memory result ≠ 0 → result.1 ≠ none → property result.2)
    (computation : OracleComp OracleWorld Result) (memory : ExternalMemory) (hinitial : property memory)
    (result : Option Result × ExternalMemory) (hresult : externalRun step computation memory result ≠ 0)
    (hlive : result.1 ≠ none) : property result.2 := by
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
          obtain ⟨answer, _, hnext⟩ := (RetainedObservation.bind_nonzero _ _ _).mp hresult
          exact ih answer memory hinitial result hnext hlive
      | inr input =>
          simp only [externalImpl, OptionT.run_mk, StateT.run_mk] at hresult
          obtain ⟨⟨answer, after⟩, hanswer, hnext⟩ := (RetainedObservation.bind_nonzero _ _ _).mp hresult
          cases answer with
          | none =>
              simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hnext
              subst result
              exact False.elim (hlive rfl)
          | some answer =>
              exact ih answer after (hstep input memory hinitial (some answer, after) hanswer (by simp)) result hnext hlive

theorem checkedExternalRun_replyClean {Result : Type} (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known actual : Labels)
    (reject : HashInput → HashOutput → Prop) (oracle : HashInput → HashOutput)
    (computation : OracleComp OracleWorld Result) (memory : ExternalMemory) (hclean : ReplyClean reject memory.cache)
    (result : Option Result × ExternalMemory)
    (hresult : externalRun (fun input memory => pure (checkedResult reject input
      (fixedStep parameter words disclosed known actual oracle input memory))) computation memory result ≠ 0)
    (hlive : result.1 ≠ none) : ReplyClean reject result.2.cache := by
  apply externalRun_preserves_live _ (fun memory => ReplyClean reject memory.cache) _ computation memory hclean result hresult hlive
  intro input memory hclean result hresult hlive
  simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
  subst result
  generalize hanswer : (checkedResult reject input (fixedStep parameter words disclosed known actual oracle input memory)).1 = answer at hlive
  cases answer with
  | none => exact False.elim (hlive rfl)
  | some answer => exact checkedFixedStep_replyClean parameter words disclosed known actual reject oracle input memory hclean answer hanswer

def ReturnedMatch {Memory : Type} (reject : HashInput → HashOutput → Prop) (input : HashInput)
    (result : Option HashOutput × Memory) : Prop :=
  ∃ answer, result.1 = some answer ∧ reject input answer

theorem returnedMatch_some {Memory : Type} (reject : HashInput → HashOutput → Prop)
    (input : HashInput) (answer : HashOutput) (memory : Memory) :
    ReturnedMatch reject input (some answer, memory) ↔ reject input answer := by
  simp [ReturnedMatch]

variable (parameter : PublicParameter) (inputs : Finset HashInput) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels) (actions : inputs → Action inputs)

theorem lazyRun_prepare_bind {Result : Type} (input : inputs)
    (next : Action inputs → OracleComp (World inputs) Result) (state : State inputs) :
    AdaptiveResidualLabels.lazyRun (environment parameter inputs words disclosed known actions)
      (liftM ((World inputs).query (.inl (.prepare input))) >>= next) state =
        let prepared := prepare parameter inputs words disclosed known actions input state.memory
        AdaptiveResidualLabels.lazyRun (environment parameter inputs words disclosed known actions)
          (next prepared.1) { state with memory := prepared.2 } := by
  rw [AdaptiveResidualLabels.lazyRun, AdaptiveResidualLabels.runWith_query_bind]
  simp only [AdaptiveResidualLabels.lazyImpl, environment, OptionT.run_mk, StateT.run_mk,
    SPMF.lift_pure, pure_bind, Option.elim_some, AdaptiveResidualLabels.lazyRun]

theorem lazyRun_execute_known (answer : HashOutput) (state : State inputs) :
    AdaptiveResidualLabels.lazyRun (environment parameter inputs words disclosed known actions)
      (execute (.known answer)) state = pure (some answer, state) := by
  exact AdaptiveResidualLabels.runWith_pure _ answer state

theorem lazyRun_execute_read (input : inputs) (state : State inputs) :
    AdaptiveResidualLabels.lazyRun (environment parameter inputs words disclosed known actions)
      (execute (.read input)) state =
        (fun answer => (some answer, AdaptiveResidualLabels.readState
          (environment parameter inputs words disclosed known actions) state input answer)) <$>
          ResidualTableCompletion.reply state.rows input := by
  simp only [AdaptiveResidualLabels.lazyRun, execute, AdaptiveResidualLabels.runWith, simulateQ_spec_query,
    AdaptiveResidualLabels.lazyImpl, OptionT.run_mk, StateT.run_mk, map_eq_bind_pure_comp, Function.comp_def]

theorem lazyImpl_rowsCovered (input : (World inputs).Domain) (state : State inputs) (hcovered : RowsCovered inputs state)
    (result : Option ((World inputs).Range input) × State inputs)
    (hresult : (AdaptiveResidualLabels.lazyImpl (environment parameter inputs words disclosed known actions) input).run.run state result ≠ 0) :
    RowsCovered inputs result.2 := by
  cases input with
  | inl input =>
      cases input with
      | prepare input =>
          simp only [AdaptiveResidualLabels.lazyImpl, environment, OptionT.run_mk, StateT.run_mk,
            SPMF.lift_pure, pure_bind, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          exact prepare_rowsCovered parameter inputs words disclosed known actions state hcovered input
      | random input =>
          simp only [AdaptiveResidualLabels.lazyImpl, environment, OptionT.run_mk, StateT.run_mk,
            ← PMF.monad_map_eq_map, liftM_map, bind_map_left] at hresult
          obtain ⟨answer, _, hresult⟩ := (RetainedObservation.bind_nonzero _ _ _).mp hresult
          simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          exact hcovered
      | stop =>
          simp only [AdaptiveResidualLabels.lazyImpl, environment, OptionT.run_mk, StateT.run_mk,
            SPMF.lift_pure, pure_bind, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          exact hcovered
      | account cost =>
          simp only [AdaptiveResidualLabels.lazyImpl, environment, OptionT.run_mk, StateT.run_mk,
            SPMF.lift_pure, pure_bind, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          exact hcovered
  | inr input =>
      cases input with
      | read input =>
          simp only [AdaptiveResidualLabels.lazyImpl, OptionT.run_mk, StateT.run_mk] at hresult
          obtain ⟨answer, _, hresult⟩ := (RetainedObservation.bind_nonzero _ _ _).mp hresult
          simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          exact rowsCovered_store inputs state hcovered state.candidates input answer
      | probe input test =>
          simp only [AdaptiveResidualLabels.lazyImpl, OptionT.run_mk, StateT.run_mk] at hresult
          cases hrow : state.rows input with
          | some answer =>
              simp only [hrow, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
              subst result
              exact rowsCovered_store inputs state hcovered state.candidates input answer
          | none =>
              rw [hrow] at hresult
              rcases (RetainedObservation.observe_nonzero _ _ _ _).mp hresult with ⟨_, hstop⟩ | ⟨answer, _, hnext⟩
              · simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hstop
                subst result
                exact hcovered
              · simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hnext
                subst result
                exact rowsCovered_store inputs state hcovered (test.restrict state.candidates answer) input answer
      | disclose coordinate =>
          simp only [AdaptiveResidualLabels.lazyImpl, OptionT.run_mk, StateT.run_mk] at hresult
          obtain ⟨value, _, hresult⟩ := (RetainedObservation.bind_nonzero _ _ _).mp hresult
          simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          exact hcovered

theorem lazyRun_rowsCovered {Result : Type} (computation : OracleComp (World inputs) Result)
    (state : State inputs) (hcovered : RowsCovered inputs state) (result : Option Result × State inputs)
    (hresult : AdaptiveResidualLabels.lazyRun (environment parameter inputs words disclosed known actions) computation state result ≠ 0) :
    RowsCovered inputs result.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [AdaptiveResidualLabels.lazyRun, AdaptiveResidualLabels.runWith_pure,
        ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact hcovered
  | query_bind input next ih =>
      rw [AdaptiveResidualLabels.lazyRun, AdaptiveResidualLabels.runWith_query_bind] at hresult
      obtain ⟨⟨answer, after⟩, hanswer, hnext⟩ := (RetainedObservation.bind_nonzero _ _ _).mp hresult
      have hafter := lazyImpl_rowsCovered parameter inputs words disclosed known actions input state hcovered (answer, after) hanswer
      cases answer with
      | none =>
          simp only [Option.elim_none, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hnext
          subst result
          exact hafter
      | some answer => exact ih answer after hafter result hnext

omit actions in
theorem prefix_encoding_actions (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
    (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (hselect : ∀ position, FirstSuccessTable.select decodeEncodingOutput (fun counter => rows (position, counter)) = selections position)
    (input : inputs) (position : EncodingPosition) (hat : AtEncodingPosition parameter input.val position) :
    (∃ answer, freshPrefix parameter inputs hencoding words disclosed known publicReplies selections rows input = .known answer ∧
      ¬PublicEncodingMatch.Match parameter (knownEncodingMessage known) words selections input.val answer) ∨
    freshPrefix parameter inputs hencoding words disclosed known publicReplies selections rows input = .read input := by
  have hroute : route parameter words disclosed known input.val = .outside := by
    rw [route, (decodePosition_none_iff parameter input.val).mpr (fun other => hat.not_atPosition other)]
    rfl
  unfold freshPrefix
  rw [hroute]
  cases hrow : knownEncodingRowAt parameter inputs hencoding known input with
  | none => exact Or.inr rfl
  | some row =>
      simp only [Option.elim_some]
      by_cases hkept : FirstSuccessPrefix.familyKept selections row
      · simp only [if_pos hkept]
        apply Or.inl
        refine ⟨rows row, rfl, ?_⟩
        have heq := (knownEncodingRowAt_some parameter inputs hencoding known input row).mp hrow
        rw [← heq]
        exact PublicEncodingMatch.protected_not_match parameter inputs hencoding known words selections rows row (hselect row.1) hkept
      · exact Or.inr (if_neg hkept)

omit actions in
theorem prob_prefixHashQuery_encodingMatch_le (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
    (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (hselect : ∀ position, FirstSuccessTable.select decodeEncodingOutput (fun counter => rows (position, counter)) = selections position)
    (input : inputs) (state : State inputs) (hcovered : RowsCovered inputs state)
    (hclean : ReplyClean (PublicEncodingMatch.Match parameter (knownEncodingMessage known) words selections) state.memory.cache) :
    Pr[ReturnedMatch (PublicEncodingMatch.Match parameter (knownEncodingMessage known) words selections) input.val |
      AdaptiveResidualLabels.lazyRun
        (prefixEnvironment parameter inputs hencoding words disclosed known publicReplies selections rows) (hashQuery input) state] ≤
      (Fintype.card Digest : ENNReal)⁻¹ := by
  by_cases hexists : ∃ position, AtEncodingPosition parameter input.val position
  · obtain ⟨position, hat⟩ := hexists
    rw [hashQuery, lazyRun_prepare_bind]
    cases hcache : state.memory.cache input.val with
    | some answer =>
        rw [prepare_cached parameter inputs words disclosed known _ input state.memory answer hcache, lazyRun_execute_known]
        simp only [probEvent_pure, returnedMatch_some, if_neg (hclean input.val answer hcache), zero_le]
    | none =>
        have hfresh := rowsCovered_fresh inputs state hcovered input hcache
        rcases prefix_encoding_actions parameter inputs words disclosed known hencoding publicReplies selections rows hselect input position hat with
          ⟨answer, haction, hsafe⟩ | haction
        · simp only [prepare, hcache, haction]
          rw [lazyRun_execute_known]
          simp only [probEvent_pure, returnedMatch_some, if_neg hsafe, zero_le]
        · simp only [prepare, hcache, haction]
          rw [lazyRun_execute_read]
          simp only [ResidualTableCompletion.reply, hfresh]
          simpa only [probEvent_map, Function.comp_def, returnedMatch_some] using
            PublicEncodingMatch.prob_match_le parameter (knownEncodingMessage known) words selections input.val
  · have hzero : Pr[ReturnedMatch (PublicEncodingMatch.Match parameter (knownEncodingMessage known) words selections) input.val |
        AdaptiveResidualLabels.lazyRun
          (prefixEnvironment parameter inputs hencoding words disclosed known publicReplies selections rows) (hashQuery input) state] = 0 := by
      apply probEvent_eq_zero
      rintro result _ ⟨answer, _, position, hat, _⟩
      exact hexists ⟨position, hat⟩
    rw [hzero]
    exact bot_le

omit disclosed known actions in
theorem initialPrefixByteRun_replyClean {Result : Type}
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (exposedValues : InitialPublicLabels words)
    (high : CanonicalGraphHighHalves) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (computation : OracleComp OracleWorld Result) (hinputs : hashInputs computation ⊆ inputs)
    (result : Option Result × ExternalMemory)
    (hresult : (forget <$> AdaptiveResidualLabels.lazyRun
      (prefixEnvironment parameter inputs hencoding words (fun _ _ _ => False) (initialKnown words exposedValues)
        (coordinateGraphLabels (initialKnown words exposedValues) high) selections rows)
      (simulateQ (checkedTranslate inputs
        (PublicEncodingMatch.Match parameter (knownEncodingMessage (initialKnown words exposedValues)) words selections)) computation)
      (initialByteState inputs words exposedValues)) result ≠ 0)
    (hlive : result.1 ≠ none) :
    ReplyClean (PublicEncodingMatch.Match parameter (knownEncodingMessage (initialKnown words exposedValues)) words selections) result.2.cache := by
  rw [← initialPrefixByteRun_erasure parameter inputs hencoding words exposedValues high selections rows computation hinputs] at hresult
  obtain ⟨labels, hlabels, hresult⟩ := (RetainedObservation.bind_nonzero _ _ _).mp hresult
  obtain ⟨seed, _, hresult⟩ := (RetainedObservation.bind_nonzero _ _ _).mp hresult
  have hagrees := initialKnown_agrees words exposedValues labels hlabels
  have heq := PublicEncodingMatch.known_eq_original parameter words (fun _ _ _ => False) (initialKnown words exposedValues)
    (coordinateOtsSecrets labels) (coordinateFtsSecrets labels) (coordinateGraphLabels labels high)
    (by simpa only [coordinateGraphLabels_value] using hagrees) selections
  dsimp only at hresult
  rw [← heq] at hresult
  exact checkedExternalRun_replyClean parameter words (fun _ _ _ => False) (initialKnown words exposedValues) labels _ _
    computation emptyMemory (replyClean_empty _) result hresult hlive

omit disclosed known actions in
theorem initialPrefixByteRun_next_encodingMatch_le {Result : Type}
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (exposedValues : InitialPublicLabels words)
    (high : CanonicalGraphHighHalves) (auxiliary : ReferenceEncodingAuxiliary)
    (hauxiliary : auxiliary ∈ referenceEncodingAuxiliarySample.support)
    (computation : OracleComp OracleWorld Result) (hinputs : hashInputs computation ⊆ inputs)
    (result : Option Result × State inputs)
    (hresult : AdaptiveResidualLabels.lazyRun
      (prefixEnvironment parameter inputs hencoding words (fun _ _ _ => False) (initialKnown words exposedValues)
        (coordinateGraphLabels (initialKnown words exposedValues) high) auxiliary.selections auxiliary.rows)
      (simulateQ (checkedTranslate inputs
        (PublicEncodingMatch.Match parameter (knownEncodingMessage (initialKnown words exposedValues)) words auxiliary.selections)) computation)
      (initialByteState inputs words exposedValues) result ≠ 0)
    (hlive : result.1 ≠ none) (input : inputs) :
    Pr[ReturnedMatch (PublicEncodingMatch.Match parameter (knownEncodingMessage (initialKnown words exposedValues)) words auxiliary.selections) input.val |
      AdaptiveResidualLabels.lazyRun
        (prefixEnvironment parameter inputs hencoding words (fun _ _ _ => False) (initialKnown words exposedValues)
          (coordinateGraphLabels (initialKnown words exposedValues) high) auxiliary.selections auxiliary.rows)
        (hashQuery input) result.2] ≤ (Fintype.card Digest : ENNReal)⁻¹ := by
  have hproject : (forget <$> AdaptiveResidualLabels.lazyRun
      (prefixEnvironment parameter inputs hencoding words (fun _ _ _ => False) (initialKnown words exposedValues)
        (coordinateGraphLabels (initialKnown words exposedValues) high) auxiliary.selections auxiliary.rows)
      (simulateQ (checkedTranslate inputs
        (PublicEncodingMatch.Match parameter (knownEncodingMessage (initialKnown words exposedValues)) words auxiliary.selections)) computation)
      (initialByteState inputs words exposedValues)) (forget result) ≠ 0 := by
    rw [map_eq_bind_pure_comp]
    apply (RetainedObservation.bind_nonzero _ _ _).mpr
    exact ⟨result, hresult, by simp [SPMF.pure_apply]⟩
  have hclean := initialPrefixByteRun_replyClean parameter inputs words hencoding exposedValues high auxiliary.selections auxiliary.rows
    computation hinputs (forget result) hproject hlive
  have hcovered := lazyRun_rowsCovered parameter inputs words (fun _ _ _ => False) (initialKnown words exposedValues)
    (freshPrefix parameter inputs hencoding words (fun _ _ _ => False) (initialKnown words exposedValues)
      (coordinateGraphLabels (initialKnown words exposedValues) high) auxiliary.selections auxiliary.rows)
    _ (initialByteState inputs words exposedValues) (rowsCovered_empty inputs emptyMemory (initialAllowed words exposedValues)) result hresult
  exact prob_prefixHashQuery_encodingMatch_le parameter inputs words (fun _ _ _ => False) (initialKnown words exposedValues)
    hencoding (coordinateGraphLabels (initialKnown words exposedValues) high) auxiliary.selections auxiliary.rows
    (referenceEncodingAuxiliarySample_select auxiliary hauxiliary) input result.2 hcovered hclean

end SphincsSecurity.Concrete.ResidualByteFrontend

import SphincsSecurity.Proof.ResidualByteCorrespondence

namespace SphincsSecurity.Concrete.ResidualByteFrontend

open _root_.OracleComp OracleSpec CanonicalProbeRouting HiddenLabelObservation ResidualByteAction
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs
set_option backward.isDefEq.respectTransparency false

noncomputable def translate (inputs : Finset HashInput) : QueryImpl OracleWorld (OracleComp (World inputs))
  | .inl input => liftM ((World inputs).query (.inl (.random input)))
  | .inr input => if hin : input ∈ inputs then hashQuery ⟨input, hin⟩ else pure (0 : HashOutput)

def forget {Result : Type} {inputs : Finset HashInput} (result : Option Result × State inputs) :
    Option Result × ExternalMemory := (result.1, result.2.memory)

variable (parameter : PublicParameter) (inputs : Finset HashInput) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels) (actions : inputs → Action inputs)

noncomputable def byteRun {Result : Type} (actual : Labels) (seed : inputs → HashOutput)
    (computation : OracleComp OracleWorld Result) (state : State inputs) : SPMF (Option Result × State inputs) :=
  AdaptiveResidualLabels.observedRun (environment parameter inputs words disclosed known actions)
    actual seed (simulateQ (translate inputs) computation) state

theorem observedRun_bind {A B : Type} (actual : Labels) (seed : inputs → HashOutput)
    (computation : OracleComp (World inputs) A) (next : A → OracleComp (World inputs) B) (state : State inputs) :
    AdaptiveResidualLabels.observedRun (environment parameter inputs words disclosed known actions)
      actual seed (computation >>= next) state =
        (AdaptiveResidualLabels.observedRun (environment parameter inputs words disclosed known actions)
          actual seed computation state >>= fun result =>
            result.1.elim (pure (none, result.2)) (fun answer =>
              AdaptiveResidualLabels.observedRun (environment parameter inputs words disclosed known actions)
                actual seed (next answer) result.2)) := by
  simp only [AdaptiveResidualLabels.observedRun, AdaptiveResidualLabels.runWith, simulateQ_bind,
    OptionT.run_bind, Option.elimM, StateT.run_bind]
  apply congrArg (fun continuation =>
    (simulateQ (AdaptiveResidualLabels.observedImpl
      (environment parameter inputs words disclosed known actions) actual seed) computation).run.run state >>= continuation)
  funext result
  rcases result with ⟨answer, state⟩
  cases answer <;> rfl

theorem byteRun_pure {Result : Type} (actual : Labels) (seed : inputs → HashOutput) (value : Result) (state : State inputs) :
    byteRun parameter inputs words disclosed known actions actual seed (pure value) state =
      pure (some value, state) := by
  simp only [byteRun, simulateQ_pure, AdaptiveResidualLabels.observedRun, AdaptiveResidualLabels.runWith_pure]

theorem byteRun_random_bind {Result : Type} (actual : Labels) (seed : inputs → HashOutput)
    (input : unifSpec.Domain) (next : unifSpec.Range input → OracleComp OracleWorld Result) (state : State inputs) :
    byteRun parameter inputs words disclosed known actions actual seed
      (liftM (OracleWorld.query (.inl input)) >>= next) state =
        ((liftM (PMF.uniformOfFintype (unifSpec.Range input)) : SPMF _) >>= fun answer =>
          byteRun parameter inputs words disclosed known actions actual seed (next answer) state) := by
  simp only [byteRun, simulateQ_bind, simulateQ_spec_query, translate]
  rw [AdaptiveResidualLabels.observedRun, AdaptiveResidualLabels.runWith_query_bind]
  simp only [AdaptiveResidualLabels.observedImpl, environment, OptionT.run_mk, StateT.run_mk,
    ← PMF.monad_map_eq_map, liftM_map, bind_map_left, bind_assoc, pure_bind, Option.elim_some]
  rfl

theorem byteRun_hash_bind {Result : Type} (actual : Labels) (seed : inputs → HashOutput)
    (input : HashInput) (hin : input ∈ inputs) (next : HashOutput → OracleComp OracleWorld Result) (state : State inputs) :
    byteRun parameter inputs words disclosed known actions actual seed
      (liftM (OracleWorld.query (.inr input)) >>= next) state =
        let result := hashQueryResult parameter inputs words disclosed known actions actual seed ⟨input, hin⟩ state
        result.1.elim (pure (none, result.2)) (fun answer =>
          byteRun parameter inputs words disclosed known actions actual seed (next answer) result.2) := by
  simp only [byteRun, simulateQ_bind, simulateQ_spec_query, translate, dif_pos hin]
  rw [observedRun_bind, observedRun_hashQuery, pure_bind]
  rfl

theorem byteRun_eq_fixed {Result : Type} (actual : Labels) (seed : inputs → HashOutput)
    (oracle : HashInput → HashOutput)
    (hlocal : ∀ input, Local input (actions input))
    (hfresh : ∀ input : inputs, ResidualByteAction.eval actual seed
      (actions input) =
        fixedAnswer parameter words disclosed actual oracle input.val)
    (computation : OracleComp OracleWorld Result) (hinputs : hashInputs computation ⊆ inputs)
    (state : State inputs) (hcovered : RowsCovered inputs state)
    (hmatches : CacheMatches oracle state.memory.cache) (hclean : CacheClean parameter words disclosed actual state.memory.cache) :
    forget <$> byteRun parameter inputs words disclosed known actions actual seed computation state =
      externalRun (fun input memory => pure (fixedStep parameter words disclosed known actual oracle input memory)) computation state.memory := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [byteRun_pure, externalRun_pure, map_pure, forget]
  | query_bind input next ih =>
      have hnext : ∀ answer, hashInputs (next answer) ⊆ inputs :=
        fun answer => (hashInputs_next_subset input next answer).trans hinputs
      cases input with
      | inl input =>
          rw [byteRun_random_bind, externalRun_query_bind]
          simp only [externalImpl, OptionT.run_mk, StateT.run_mk, bind_assoc, pure_bind, map_bind]
          apply congrArg ((liftM (PMF.uniformOfFintype (unifSpec.Range input)) : SPMF _) >>= ·)
          funext answer
          exact ih answer (hnext answer) state hcovered hmatches hclean
      | inr input =>
          change HashOutput → OracleComp OracleWorld Result at next
          have hmem := mem_hashInputs_hash_bind (α := Result) input next
          have hin : input ∈ inputs := hinputs hmem
          rw [byteRun_hash_bind parameter inputs words disclosed known actions actual seed input hin,
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
          generalize hresult : hashQueryResult parameter inputs words disclosed known actions
            actual seed ⟨input, hin⟩ state = result at *
          rcases result with ⟨answer, after⟩
          cases answer with
          | none => simp only [Option.elim_none, map_pure, forget]
          | some answer => exact ih answer (hnext answer) after hcovered' hafter.1 hafter.2.1

theorem byteRun_eq_original {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels) (publicReplies : CanonicalGraphLabels)
    (rows : CanonicalEncodingRows)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (replies : CanonicalGraphLabels)
    (hagrees : PublicAgreement words disclosed known (CanonicalCoordinate.value otsSecret ftsSecret replies))
    (hreplies : ∀ position, ¬CanonicalCoordinate.Hidden words disclosed (.graph position) → publicReplies position = replies position)
    (seed : inputs → HashOutput) (computation : OracleComp OracleWorld Result) (hinputs : hashInputs computation ⊆ inputs)
    (state : State inputs) (hcovered : RowsCovered inputs state)
    (hmatches : CacheMatches (programmedHash parameter otsSecret ftsSecret replies
      (finiteHashAnswer ∅ inputs (canonicalReferenceResidual parameter inputs hencoding replies rows seed))) state.memory.cache)
    (hclean : CacheClean parameter words disclosed (CanonicalCoordinate.value otsSecret ftsSecret replies) state.memory.cache) :
    let oracle := programmedHash parameter otsSecret ftsSecret replies
      (finiteHashAnswer ∅ inputs (canonicalReferenceResidual parameter inputs hencoding replies rows seed))
    forget <$> byteRun parameter inputs words disclosed known (fresh parameter inputs hencoding words disclosed known publicReplies rows)
      (CanonicalCoordinate.value otsSecret ftsSecret replies) seed computation state =
        externalRun (fun input memory => pure (fixedStep parameter words disclosed known
          (CanonicalCoordinate.value otsSecret ftsSecret replies) oracle input memory)) computation state.memory :=
  byteRun_eq_fixed parameter inputs words disclosed known (fresh parameter inputs hencoding words disclosed known publicReplies rows) _ seed _
    (fresh_local parameter inputs hencoding words disclosed known publicReplies rows)
    (fun input => fresh_eq_original parameter inputs hencoding words disclosed known otsSecret ftsSecret replies publicReplies
      hagrees hreplies rows seed input) computation hinputs state hcovered hmatches hclean

noncomputable abbrev wholeByteRun {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels) (publicReplies : CanonicalGraphLabels)
    (rows : CanonicalEncodingRows) (actual : Labels) (seed : inputs → HashOutput)
    (computation : OracleComp OracleWorld Result) (state : State inputs) :=
  byteRun parameter inputs words disclosed known (fresh parameter inputs hencoding words disclosed known publicReplies rows)
    actual seed computation state

end SphincsSecurity.Concrete.ResidualByteFrontend

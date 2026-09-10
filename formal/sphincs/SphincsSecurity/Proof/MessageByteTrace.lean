import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.PrefixBytePrior
import SphincsSecurity.Proof.ReferenceAuxiliarySigning

namespace SphincsSecurity.Concrete.ResidualByteFrontend

open _root_.OracleComp OracleSpec CanonicalProbeRouting
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs
set_option backward.isDefEq.respectTransparency false

def MessageOnly {Result : Type} (parameter : PublicParameter) (computation : OracleComp OracleWorld Result) : Prop :=
  ∀ input ∈ hashInputs computation, FtsProbeSimulation.MessageHashInput parameter input

theorem messageOnly_pure {Result : Type} (parameter : PublicParameter) (value : Result) :
    MessageOnly parameter (pure value) := by
  intro input hinput
  simp only [hashInputs_pure, Finset.notMem_empty] at hinput

theorem messageOnly_query_bind {Result : Type} (parameter : PublicParameter) (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld Result)
    (hhead : match input with | .inl _ => True | .inr input => FtsProbeSimulation.MessageHashInput parameter input)
    (htail : ∀ answer, MessageOnly parameter (next answer)) :
    MessageOnly parameter (liftM (OracleWorld.query input) >>= next) := by
  intro row hrow
  rw [hashInputs_query_bind, Finset.mem_union] at hrow
  rcases hrow with hheadRow | htailRow
  · cases input with
    | inl _ => simp only [Finset.notMem_empty] at hheadRow
    | inr input =>
        obtain rfl := Finset.mem_singleton.mp hheadRow
        exact hhead
  · obtain ⟨answer, _, hrow⟩ := Finset.mem_biUnion.mp htailRow
    exact htail answer row hrow

theorem messageOnly_bind {A B : Type} (parameter : PublicParameter) (first : OracleComp OracleWorld A)
    (next : A → OracleComp OracleWorld B) (hfirst : MessageOnly parameter first)
    (hnext : ∀ answer, MessageOnly parameter (next answer)) : MessageOnly parameter (first >>= next) := by
  induction first using OracleComp.inductionOn with
  | pure value => simpa only [pure_bind] using hnext value
  | query_bind input tail ih =>
      rw [bind_assoc]
      apply messageOnly_query_bind parameter input _
      · cases input with
        | inl _ => trivial
        | inr input => exact hfirst input (mem_hashInputs_hash_bind input tail)
      · intro answer
        exact ih answer (fun row hrow => hfirst row ((hashInputs_next_subset input tail answer) hrow))

theorem messageOnly_lift_prob {Result : Type} (parameter : PublicParameter) (computation : ProbComp Result) :
    MessageOnly parameter (liftM computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => rw [liftM_pure]; exact messageOnly_pure parameter value
  | query_bind input next ih =>
      rw [liftM_bind]
      exact messageOnly_query_bind parameter (.inl input) _ trivial ih

noncomputable def applyBoundary (memory : ExternalMemory) (trace : SigningBoundaryTrace) : ExternalMemory :=
  ⟨trace.messageCalls.foldl (fun cache entry => Function.update cache entry.1 (some entry.2)) memory.cache,
    memory.hashCalls + trace.hashCalls, memory.probes⟩

theorem applyBoundary_one (memory : ExternalMemory) : applyBoundary memory 1 = memory := by
  cases memory
  rfl

theorem applyBoundary_mul (memory : ExternalMemory) (left right : SigningBoundaryTrace) :
    applyBoundary memory (left * right) = applyBoundary (applyBoundary memory left) right := by
  simp only [applyBoundary, SigningBoundaryTrace.messageCalls_mul, SigningBoundaryTrace.hashCalls_mul,
    List.foldl_append, Nat.add_assoc]

noncomputable def messageStep (oracle : QueryImpl HashSpec Id) (input : HashInput) (memory : ExternalMemory) :
    Option HashOutput × ExternalMemory :=
  (some (oracle input), storeReply { memory with hashCalls := memory.hashCalls + 1 } input (oracle input))

theorem applyBoundary_message (parameter : PublicParameter) (input : HashInput) (output : HashOutput)
    (hmessage : FtsProbeSimulation.MessageHashInput parameter input) (memory : ExternalMemory) :
    applyBoundary memory (signingBoundaryTrace parameter (.inr input) output) =
      storeReply { memory with hashCalls := memory.hashCalls + 1 } input output := by
  rw [signingBoundaryTrace, if_pos hmessage]
  rfl

theorem fixedBoundaryRun_query_bind {Result : Type} (parameter : PublicParameter) (oracle : QueryImpl HashSpec Id)
    (input : OracleWorld.Domain) (next : OracleWorld.Range input → OracleComp OracleWorld Result) :
    fixedBoundaryRun parameter oracle (liftM (OracleWorld.query input) >>= next) =
      fixedHashWorld oracle input >>= fun answer =>
        (fun result => (result.1, signingBoundaryTrace parameter input answer * result.2)) <$>
          fixedBoundaryRun parameter oracle (next answer) := by
  simp [fixedBoundaryRun, QueryImpl.withTrace_apply]

theorem externalRun_message_trace {Result : Type} (parameter : PublicParameter) (oracle : QueryImpl HashSpec Id)
    (computation : OracleComp OracleWorld Result) (hmessage : MessageOnly parameter computation) (memory : ExternalMemory) :
    externalRun (fun input memory => pure (messageStep oracle input memory)) computation memory =
      (fun result => (some result.1, applyBoundary memory result.2)) <$> 𝒟[fixedBoundaryRun parameter oracle computation] := by
  induction computation using OracleComp.inductionOn generalizing memory with
  | pure value => simp only [externalRun_pure, fixedBoundaryRun_pure, evalDist_pure, map_pure, applyBoundary_one]
  | query_bind input next ih =>
      have hnext : ∀ answer, MessageOnly parameter (next answer) :=
        fun answer row hrow => hmessage row ((hashInputs_next_subset input next answer) hrow)
      rw [externalRun_query_bind, fixedBoundaryRun_query_bind]
      cases input with
      | inl input =>
          simp only [externalImpl, OptionT.run_mk, StateT.run_mk, fixedHashWorld, evalDist_bind,
            evalDist_query, signingBoundaryTrace, one_mul, evalDist_map, bind_assoc, pure_bind, map_bind]
          apply congrArg ((liftM (PMF.uniformOfFintype (unifSpec.Range input)) : SPMF _) >>= ·)
          funext answer
          simpa only [Functor.map_map, Function.comp_def] using ih answer (hnext answer) memory
      | inr input =>
          have hat := hmessage input (mem_hashInputs_hash_bind input next)
          simp only [externalImpl, OptionT.run_mk, StateT.run_mk, messageStep, fixedHashWorld,
            pure_bind, evalDist_map, Functor.map_map]
          change externalRun (fun input memory => pure (messageStep oracle input memory)) (next (oracle input))
            (messageStep oracle input memory).2 = _
          rw [ih (oracle input) (hnext (oracle input))]
          congr 1
          funext result
          rw [applyBoundary_mul, applyBoundary_message parameter input (oracle input) hat]
          rfl

theorem message_not_encoding (parameter : PublicParameter) (input : HashInput)
    (hmessage : FtsProbeSimulation.MessageHashInput parameter input) (position : EncodingPosition) :
    ¬AtEncodingPosition parameter input position := by
  obtain ⟨payload, rfl⟩ := hmessage
  rintro ⟨other, heq⟩
  have hdomain := (tweakableHashInput_injective parameter (by trivial) (by trivial) heq).1
  simp only [EncodingPosition.domain, reduceCtorEq] at hdomain

theorem checkedFixedStep_message (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known actual : Labels) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) (oracle : QueryImpl HashSpec Id) (input : HashInput)
    (hmessage : FtsProbeSimulation.MessageHashInput parameter input) (memory : ExternalMemory) :
    checkedResult (PublicEncodingMatch.Match parameter messages words selections) input
      (fixedStep parameter words disclosed known actual oracle input memory) = messageStep oracle input memory := by
  have hdecode : decodePosition parameter input = none := by
    obtain ⟨payload, rfl⟩ := hmessage
    exact decodePosition_message parameter payload
  have hbad : ¬CanonicalProbeRouting.Bad parameter words disclosed actual input (oracle input) := by
    rintro ⟨position, hat, _⟩
    exact (decodePosition_none_iff parameter input).mp hdecode position hat
  have hmatch : ¬PublicEncodingMatch.Match parameter messages words selections input (oracle input) := by
    rintro ⟨position, hat, _⟩
    exact message_not_encoding parameter input hmessage position hat
  simp only [checkedResult, fixedStep, fixedAnswer, if_neg hbad, Option.bind_some, if_neg hmatch,
    Option.elim_some, messageStep, charge, route, hdecode, Option.elim_none]
  cases memory.cache input <;> simp only [Nat.add_zero]

theorem externalRun_congr_inputs {Result : Type} (left right : HashStep) (computation : OracleComp OracleWorld Result)
    (heq : ∀ input ∈ hashInputs computation, ∀ memory, left input memory = right input memory)
    (memory : ExternalMemory) : externalRun left computation memory = externalRun right computation memory := by
  induction computation using OracleComp.inductionOn generalizing memory with
  | pure value => simp only [externalRun_pure]
  | query_bind input next ih =>
      have hnext : ∀ answer row, row ∈ hashInputs (next answer) → ∀ memory, left row memory = right row memory :=
        fun answer row hrow => heq row ((hashInputs_next_subset input next answer) hrow)
      rw [externalRun_query_bind, externalRun_query_bind]
      cases input with
      | inl input =>
          simp only [externalImpl, OptionT.run_mk, StateT.run_mk, bind_assoc, pure_bind]
          apply congrArg ((liftM (PMF.uniformOfFintype (unifSpec.Range input)) : SPMF _) >>= ·)
          funext answer
          exact ih answer (hnext answer) memory
      | inr input =>
          simp only [externalImpl, OptionT.run_mk, StateT.run_mk]
          rw [heq input (mem_hashInputs_hash_bind input next) memory]
          apply congrArg (right input memory >>= ·)
          funext result
          rcases result with ⟨answer, after⟩
          cases answer with
          | none => rfl
          | some answer => exact ih answer (hnext answer) after

theorem checkedExternalRun_message_trace {Result : Type} (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known actual : Labels) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) (oracle : QueryImpl HashSpec Id)
    (computation : OracleComp OracleWorld Result) (hmessage : MessageOnly parameter computation) (memory : ExternalMemory) :
    externalRun (fun input memory => pure (checkedResult (PublicEncodingMatch.Match parameter messages words selections) input
      (fixedStep parameter words disclosed known actual oracle input memory))) computation memory =
      (fun result => (some result.1, applyBoundary memory result.2)) <$> 𝒟[fixedBoundaryRun parameter oracle computation] := by
  rw [externalRun_congr_inputs _ (fun input memory => pure (messageStep oracle input memory)) computation
    (fun input hin memory => congrArg pure (checkedFixedStep_message parameter words disclosed known actual messages selections oracle input
      (hmessage input hin) memory)) memory]
  exact externalRun_message_trace parameter oracle computation hmessage memory

theorem initialPrefixByteRun_message_trace {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (exposedValues : InitialPublicLabels words) (high : CanonicalGraphHighHalves) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (computation : OracleComp OracleWorld Result) (hinputs : hashInputs computation ⊆ inputs) (hmessage : MessageOnly parameter computation) :
    let known := initialKnown words exposedValues
    (forget <$> AdaptiveResidualLabels.lazyRun
      (prefixEnvironment parameter inputs hencoding words (fun _ _ _ => False) known (coordinateGraphLabels known high) selections rows)
      (simulateQ (checkedTranslate inputs (PublicEncodingMatch.Match parameter (knownEncodingMessage known) words selections)) computation)
      (initialByteState inputs words exposedValues)) =
    (UniformTableCompletion.complete (initialAllowed words exposedValues) >>= fun labels =>
      ResidualTableCompletion.completeRows (fun _ : inputs => none) >>= fun seed =>
      let graph := coordinateGraphLabels labels high
      let oracle := programmedHash parameter (coordinateOtsSecrets labels) (coordinateFtsSecrets labels) graph
        (finiteHashAnswer ∅ inputs (canonicalPrefixResidual parameter inputs hencoding graph selections rows seed))
      (fun result => (some result.1, applyBoundary emptyMemory result.2)) <$> 𝒟[fixedBoundaryRun parameter oracle computation]) := by
  dsimp only
  rw [← initialPrefixByteRun_erasure parameter inputs hencoding words exposedValues high selections rows computation hinputs]
  apply congrArg (UniformTableCompletion.complete (initialAllowed words exposedValues) >>= ·)
  funext labels
  apply congrArg (ResidualTableCompletion.completeRows (fun _ : inputs => none) >>= ·)
  funext seed
  exact checkedExternalRun_message_trace parameter words (fun _ _ _ => False) (initialKnown words exposedValues) labels _ selections _
    computation hmessage emptyMemory

end SphincsSecurity.Concrete.ResidualByteFrontend

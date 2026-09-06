import SphincsSecurity.Proof.OtsProbeResolvedOrdinaryHash
import SphincsSecurity.Proof.OtsProbeEncodingExhaustion
import SphincsSecurity.Proof.OtsProbeNativeCacheMonotone

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem mem_support_otsSignFrom_none_of_masked
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (secret : ChainIndex → Digest) (message : Digest) (attempts counter : Nat)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (Option (Counter × (ChainIndex → Digit)) × SplitHashCache))
    (hresult : some result ∈ support (runResolvedFromTable context fuel table
      ((maskedOtsSignFrom parameter lay tree leafIdx message attempts counter).run cache)))
    (hfailed : result.value.1 = none) :
    (none, ordinaryQueryCache result.value.2) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (otsSignFrom parameter lay tree leafIdx secret message attempts counter)).run (ordinaryQueryCache cache)) := by
  induction attempts generalizing counter context fuel table cache result with
  | zero =>
      simp only [maskedOtsSignFrom, StateT.run_pure, runResolvedFromTable, construct_pure, mem_support_pure_iff,
        Option.some.injEq] at hresult
      subst result
      simp [otsSignFrom]
  | succ attempts ih =>
      rw [maskedOtsSignFrom, StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
      obtain ⟨encodedOption, hencoded, hrest⟩ := hresult
      rw [runResolved_simulateQ_ordinaryHashImpl, support_map] at hencoded
      obtain ⟨encoded, hencoded, heq⟩ := hencoded
      subst encodedOption
      dsimp only [ordinaryResolvedResult] at hrest
      cases hvalue : encoded.1 with
      | none =>
          simp only [hvalue] at hrest
          have htail := ih (counter + 1) context fuel table (replaceOrdinaryCache cache encoded.2) result hrest hfailed
          rw [ordinaryQueryCache_replaceOrdinaryCache] at htail
          rw [otsSignFrom, simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
          refine ⟨encoded, hencoded, ?_⟩
          simpa only [hvalue] using htail
      | some encoding =>
          simp only [hvalue, StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hrest
          obtain ⟨ensuredOption, hensured, hreturn⟩ := hrest
          cases ensuredOption with
          | none => simp at hreturn
          | some ensured =>
              simp [runResolvedFromTable] at hreturn
              subst result
              simp at hfailed

theorem encodingInputsExhausted_of_mem_failed_maskedOtsSign
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (Option (Counter × (ChainIndex → Digit)) × SplitHashCache))
    (hresult : some result ∈ support (runResolvedFromTable context fuel table
      ((maskedOtsSign parameter lay tree leafIdx message).run cache)))
    (hfailed : result.value.1 = none) :
    EncodingInputsExhausted (encodingRetryInputs parameter ⟨lay, tree, leafIdx⟩ message) (ordinaryQueryCache result.value.2) := by
  have hconcrete := mem_support_otsSignFrom_none_of_masked parameter lay tree leafIdx (fun _ => 0) message
    encodingAttemptLimit 0 context fuel table cache result hresult hfailed
  obtain ⟨_, f, hagrees, hfailed, hcached⟩ := exists_answerFn_replay_of_mem_support _ _ _ _ hconcrete
  exact encodingInputsExhausted_of_otsSign_none f _ parameter lay tree leafIdx (fun _ => 0) message hagrees hcached hfailed

theorem encodingInputsExhausted_of_mem_failed_maskedOtsLayerAfterMessage
    (parameter : PublicParameter) (index : Index) (lay : Layer) (message : Digest)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (Option (Counter × (ChainIndex → Digit)) × SplitHashCache))
    (hresult : some result ∈ support (runResolvedFromTable context fuel table
      ((maskedOtsLayerAfterMessage parameter index lay message).run cache)))
    (hfailed : result.value.1 = none) :
    EncodingInputsExhausted (encodingRetryInputs parameter ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩ message)
      (ordinaryQueryCache result.value.2) := by
  rw [maskedOtsLayerAfterMessage, StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨selectedOption, hselected, hrest⟩ := hresult
  cases selectedOption with
  | none => simp at hrest
  | some selected =>
      cases hvalue : selected.value.1 with
      | none =>
          simp [hvalue, runResolvedFromTable] at hrest
          subst result
          exact encodingInputsExhausted_of_mem_failed_maskedOtsSign parameter lay _ _ message
            context fuel table cache selected hselected hvalue
      | some chosen =>
          simp only [hvalue, StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hrest
          obtain ⟨pathOption, hpath, hreturn⟩ := hrest
          cases pathOption with
          | none => simp at hreturn
          | some path =>
              simp [runResolvedFromTable] at hreturn
              subst result
              simp at hfailed

theorem encodingInputsExhausted_of_mem_failed_chronologicalLayerAfterMessage
    (parameter : PublicParameter) (index : Index) (lay : Layer) (message : Digest)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (Option ChronologicalLayerPart × SplitHashCache))
    (hresult : some result ∈ support (runResolvedFromTable context fuel table
      ((maskedChronologicalLayerAfterMessage parameter index lay message).run cache)))
    (hfailed : result.value.1 = none) :
    EncodingInputsExhausted (encodingRetryInputs parameter ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩ message)
      (ordinaryQueryCache result.value.2) := by
  rw [maskedChronologicalLayerAfterMessage, StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨selectedOption, hselected, hrest⟩ := hresult
  cases selectedOption with
  | none => simp at hrest
  | some selected =>
      cases hvalue : selected.value.1 with
      | none =>
          simp [hvalue, runResolvedFromTable] at hrest
          subst result
          exact encodingInputsExhausted_of_mem_failed_maskedOtsLayerAfterMessage parameter index lay message
            context fuel table cache selected hselected hvalue
      | some chosen =>
          simp only [hvalue, StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hrest
          obtain ⟨publishedOption, hpublished, hreturn⟩ := hrest
          cases publishedOption with
          | none => simp at hreturn
          | some published =>
              simp [runResolvedFromTable] at hreturn
              subst result
              simp at hfailed

end SphincsSecurity.Concrete.OtsProbeSimulation

import SphincsSecurity.Proof.OtsProbeEncodingPotential
import SphincsSecurity.Proof.EncodingExhaustionBound

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option exponentiation.threshold 512

def ResolvedEncodingInputsExhausted (inputs : Finset HashInput) :
    Option (ResolvedRunResult (α × SplitHashCache)) → Prop
  | none => False
  | some result => EncodingInputsExhausted inputs (ordinaryQueryCache result.value.2)

theorem probEvent_resolved_encodingInputsExhausted_le
    (inputs : Finset HashInput)
    (computation : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hbound : ResolvedCachePotentialBound (encodingCachePotential inputs) computation)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    Pr[ResolvedEncodingInputsExhausted inputs | runResolvedFromTable context fuel table (computation.run cache)] ≤
      encodingCachePotential inputs cache := by
  apply le_trans _ (hbound context fuel table cache)
  rw [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  cases result with
  | none => simp [ResolvedEncodingInputsExhausted, resolvedCachePotential]
  | some result =>
      by_cases hexhausted : EncodingInputsExhausted inputs (ordinaryQueryCache result.value.2)
      · simp [ResolvedEncodingInputsExhausted, resolvedCachePotential, encodingCachePotential, hexhausted,
          encodingExhaustionPotential_eq_one_of_exhausted inputs _ hexhausted]
      · simp [ResolvedEncodingInputsExhausted, hexhausted]

theorem probEvent_resolved_encodingInputsExhausted_empty_le_pow
    (inputs : Finset HashInput)
    (computation : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hbound : ResolvedCachePotentialBound (encodingCachePotential inputs) computation)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    Pr[ResolvedEncodingInputsExhausted inputs | runResolvedFromTable context fuel table (computation.run emptySplitHashCache)] ≤
      (1 - (TargetSum.validDigests.card : ENNReal) / (Fintype.card Digest : ENNReal)) ^ inputs.card := by
  have h := probEvent_resolved_encodingInputsExhausted_le inputs computation hbound context fuel table emptySplitHashCache
  simpa only [encodingCachePotential, show ordinaryQueryCache emptySplitHashCache = ∅ from rfl,
    encodingExhaustionPotential_empty_cache, encodingInvalidProbability, probEvent_uniform_encoding_invalid] using h

def ResolvedAnyEncodingInputsExhausted : Option (ResolvedRunResult (α × SplitHashCache)) → Prop
  | none => False
  | some result => AnyEncodingInputsExhausted (ordinaryQueryCache result.value.2)

theorem probEvent_resolved_anyEncodingInputsExhausted_le_inv216
    (computation : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hbound : ∀ parameter position message, ResolvedCachePotentialBound
      (encodingCachePotential (encodingRetryInputs parameter position message)) computation)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    Pr[ResolvedAnyEncodingInputsExhausted | runResolvedFromTable context fuel table (computation.run emptySplitHashCache)] ≤
      ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  let family := PublicParameter × EncodingPosition × Digest
  let run := runResolvedFromTable context fuel table (computation.run emptySplitHashCache)
  let event := fun choice : family => ResolvedEncodingInputsExhausted (α := α) (encodingRetryInputs choice.1 choice.2.1 choice.2.2)
  have hunion := probEvent_exists_finset_le_sum (Finset.univ : Finset family) run event
  have hleft : (fun result => ∃ choice ∈ (Finset.univ : Finset family), event choice result) =
      (ResolvedAnyEncodingInputsExhausted : Option (ResolvedRunResult (α × SplitHashCache)) → Prop) := by
    funext result
    apply propext
    cases result with
    | none => simp [event, ResolvedEncodingInputsExhausted, ResolvedAnyEncodingInputsExhausted]
    | some result =>
        simp only [Finset.mem_univ, true_and, event, ResolvedEncodingInputsExhausted,
          ResolvedAnyEncodingInputsExhausted, AnyEncodingInputsExhausted]
        constructor
        · rintro ⟨choice, hchoice⟩
          exact ⟨choice.1, choice.2.1, choice.2.2, hchoice⟩
        · rintro ⟨parameter, position, message, hchoice⟩
          exact ⟨(parameter, position, message), hchoice⟩
  rw [hleft] at hunion
  apply hunion.trans
  apply le_trans _ encoding_exhaustion_global_bound_le_inv216
  calc
    _ ≤ ∑ _choice : family,
        (1 - (TargetSum.validDigests.card : ENNReal) / (Fintype.card Digest : ENNReal)) ^ encodingAttemptLimit := by
      apply Finset.sum_le_sum
      intro choice _
      have h := probEvent_resolved_encodingInputsExhausted_empty_le_pow _ computation
        (hbound choice.1 choice.2.1 choice.2.2) context fuel table
      rw [encodingRetryInputs_card] at h
      exact h
    _ = _ := by
      have hcard : Fintype.card family = 3 * 2 ^ 294 := by
        have hposition : Fintype.card EncodingPosition = Fintype.card (Layer × TreeIndex × LeafIndex) :=
          Fintype.card_congr
            { toFun := fun position => (position.lay, position.tree, position.leafIdx)
              invFun := fun fields => ⟨fields.1, fields.2.1, fields.2.2⟩
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl }
        change Fintype.card (PublicParameter × EncodingPosition × Digest) = _
        rw [Fintype.card_prod, Fintype.card_prod, hposition]
        norm_num [publicParameterBits, digestBits, numLayers, totalHeight, maxLayerHeight]
      rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]

theorem probEvent_resolved_ordinaryRom_anyEncodingInputsExhausted_le_inv216
    (computation : OracleComp OracleWorld α) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    Pr[ResolvedAnyEncodingInputsExhausted |
      runResolvedFromTable context fuel table ((simulateQ ordinaryRomImpl computation).run emptySplitHashCache)] ≤
      ((2 ^ 216 : Nat) : ENNReal)⁻¹ :=
  probEvent_resolved_anyEncodingInputsExhausted_le_inv216 _
    (fun _ _ _ => resolvedCachePotentialBound_ordinaryRom_encoding _ computation) context fuel table

end SphincsSecurity.Concrete.OtsProbeSimulation

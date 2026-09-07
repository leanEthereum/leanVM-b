import SphincsSecurity.Proof.TargetMixedGrowthPolynomial

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def targetMixedSigningGrowth (key : SecretKey) (before after : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Fin m → Finset FtsTree) (required : Finset FtsTree) : ENNReal :=
  (normalizedTargetCacheProduct key.parameter after (tweakableHashInput key.parameter .message payload) target groups -
    normalizedTargetCacheProduct key.parameter before (tweakableHashInput key.parameter .message payload) target groups) *
      normalizedTargetLogProduct key after log payload target required

noncomputable def newTargetMixedGrowthWeight (key : SecretKey) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Fin m → Finset FtsTree) (required : Finset FtsTree) (source : FewTimeView) : ENNReal :=
  targetMixedGrowthPolynomial
    (fun slot => normalizedCachedTargetSubsetMatch key.parameter before (tweakableHashInput key.parameter .message payload) target (groups slot))
    (normalizedTargetLogMatch key before log payload target) groups required target source

theorem signWithView_targetCacheProduct_le_new (key : SecretKey) (message : Message) (before after : QueryCache HashSpec)
    (signature : Option Signature) (view : Option FewTimeView)
    (hresult : ((signature, view), after) ∈ support ((simulateQ romImpl (signWithView key message)).run before))
    (targetInput : HashInput) (target : FewTimeView) (groups : Fin m → Finset FtsTree) (newPayload : HashInput) (output : HashOutput)
    (hfresh : before (tweakableHashInput key.parameter .message newPayload) = none)
    (hafter : after (tweakableHashInput key.parameter .message newPayload) = some output)
    (hadmissible : Admissible (truncateMessageDigest output)) :
    normalizedTargetCacheProduct key.parameter after targetInput target groups ≤
      normalizedTargetCacheProduct key.parameter before targetInput target groups +
        targetCacheArrivalPolynomial (fun slot => normalizedCachedTargetSubsetMatch key.parameter before targetInput target (groups slot))
          groups target (hashOutputFewTimeView output) := by
  unfold normalizedTargetCacheProduct
  rw [targetCacheProduct_add_arrival]
  apply Finset.prod_le_prod'
  intro slot _
  rw [signWithView_normalizedCachedTargetSubsetMatch_of_new key message before after signature view hresult targetInput newPayload target (groups slot) output hfresh hafter hadmissible]
  apply add_le_add le_rfl
  split_ifs
  · exact bot_le
  · exact le_rfl

theorem signWithView_targetLogProduct_le_view (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target source : FewTimeView) (required : Finset FtsTree)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)) (hview : result.1.2 = some source) :
    normalizedTargetLogProduct key result.2 (log ++ [⟨message, result.1.1⟩]) payload target required ≤
      ∏ tree ∈ required, (normalizedTargetLogMatch key before log payload target tree + normalizedSourceSubsetMatch target source {tree}) := by
  exact Finset.prod_le_prod' (fun tree _ =>
    signWithView_normalizedTargetLogMatch_le key message before log payload target source tree hsigned result hresult hview)

theorem signWithView_targetMixedGrowth_le_new (key : SecretKey) (message : Message) (before after : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (groups : Fin m → Finset FtsTree) (required : Finset FtsTree)
    (signature : Option Signature) (view : Option FewTimeView)
    (hresult : ((signature, view), after) ∈ support ((simulateQ romImpl (signWithView key message)).run before))
    (hsigned : SigningDigestsCached key.parameter before key.root log) (newPayload : HashInput) (output : HashOutput)
    (hfresh : before (tweakableHashInput key.parameter .message newPayload) = none)
    (hafter : after (tweakableHashInput key.parameter .message newPayload) = some output)
    (hadmissible : Admissible (truncateMessageDigest output)) :
    targetMixedSigningGrowth key before after (log ++ [⟨message, signature⟩]) payload target groups required ≤
      newTargetMixedGrowthWeight key before log payload target groups required (hashOutputFewTimeView output) := by
  have hproduct := signWithView_targetCacheProduct_le_new key message before after signature view hresult
    (tweakableHashInput key.parameter .message payload) target groups newPayload output hfresh hafter hadmissible
  obtain ⟨_, _, _, _, _, _, hview, _⟩ := signWithView_new_admissible_selected key message before after signature view hresult
    newPayload output hfresh hafter hadmissible
  have hlog := signWithView_targetLogProduct_le_view key message before log payload target (hashOutputFewTimeView output)
    required hsigned ((signature, view), after) hresult hview
  exact mul_le_mul' (tsub_le_iff_right.mpr (hproduct.trans_eq (add_comm _ _))) hlog

theorem signWithView_targetMixedGrowth_le_newEvents (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (groups : Fin m → Finset FtsTree) (required : Finset FtsTree)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)) :
    targetMixedSigningGrowth key before result.2 (log ++ [⟨message, result.1.1⟩]) payload target groups required ≤
      ∑' source, if NewAdmissibleSignerView before key (· = source) result then
        newTargetMixedGrowthWeight key before log payload target groups required source else 0 := by
  by_cases hnew : NewAdmissibleSignerView before key (fun _ => True) result
  · obtain ⟨newPayload, output, hfresh, hafter, hadmissible, _⟩ := hnew
    have hbound := signWithView_targetMixedGrowth_le_new key message before result.2 log payload target groups required
      result.1.1 result.1.2 hresult hsigned newPayload output hfresh hafter hadmissible
    apply hbound.trans
    have hevent : NewAdmissibleSignerView before key (· = hashOutputFewTimeView output) result :=
      ⟨newPayload, output, hfresh, hafter, hadmissible, rfl⟩
    exact (le_of_eq (if_pos hevent).symm).trans (ENNReal.le_tsum (hashOutputFewTimeView output))
  · have hcache := simulateQ_romImpl_cache_le (signWithView key message) before result hresult
    have hnoNew (input : HashInput) (output : HashOutput) (hfresh : before input = none)
        (hmessage : MessageHashInput key.parameter input) (hafter : result.2 input = some output) :
        ¬ Admissible (truncateMessageDigest output) := by
      intro hadmissible
      obtain ⟨newPayload, rfl⟩ := hmessage
      exact hnew ⟨newPayload, output, hfresh, hafter, hadmissible, trivial⟩
    have hcounts (slot : Fin m) : normalizedCachedTargetSubsetMatch key.parameter result.2
        (tweakableHashInput key.parameter .message payload) target (groups slot) =
        normalizedCachedTargetSubsetMatch key.parameter before (tweakableHashInput key.parameter .message payload) target (groups slot) := by
      simp only [normalizedCachedTargetSubsetMatch_eq_weight]
      exact cacheMessageWeight_of_no_new key.parameter _ before result.2 hcache hnoNew
    simp only [targetMixedSigningGrowth, normalizedTargetCacheProduct, hcounts, tsub_self, zero_mul, zero_le]

theorem expected_signWithView_targetMixedGrowth_le_uniform (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (groups : Fin m → Finset FtsTree) (required : Finset FtsTree)
    (hsigned : SigningDigestsCached key.parameter before key.root log) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      targetMixedSigningGrowth key before result.2 (log ++ [⟨message, result.1.1⟩]) payload target groups required) ≤
      ∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] * newTargetMixedGrowthWeight key before log payload target groups required source := by
  apply le_trans ?_ (expected_newAdmissibleSignerView_weight_le key message before (newTargetMixedGrowthWeight key before log payload target groups required))
  calc
    _ ≤ ∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
        ∑' source, if NewAdmissibleSignerView before key (· = source) result then newTargetMixedGrowthWeight key before log payload target groups required source else 0 := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)
      · exact mul_le_mul' le_rfl (signWithView_targetMixedGrowth_le_newEvents key message before log payload target groups required hsigned result hresult)
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
    _ = _ := by
      simp only [← ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro source
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro result
      split_ifs <;> simp

end SphincsSecurity.Concrete

import SphincsSecurity.Proof.ExpectedNewTargetEnvelope
import SphincsSecurity.Proof.TargetCacheEnvelope
import SphincsSecurity.Proof.RawIndexCacheEnvelope

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def cachedTargetEnvelope (key : SecretKey) (q signatures : Nat) (state : CoverLogState)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) : ENNReal :=
  cacheMessageWeight key.parameter (fun input target => targetCacheEnvelope key q (payloadOf input) target signatures state groups remaining) state.1

noncomputable def newCachedTargetEnvelope (key : SecretKey) (q signatures : Nat) (before : QueryCache HashSpec) (after : CoverLogState)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) : ENNReal :=
  cacheMessageWeight key.parameter (fun input target => if before input = none then
    targetCacheEnvelope key q (payloadOf input) target signatures after groups remaining else 0) after.1

theorem cachedTargetEnvelope_split (key : SecretKey) (q signatures : Nat) (before : QueryCache HashSpec) (after : CoverLogState)
    (hcache : before ≤ after.1) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    cachedTargetEnvelope key q signatures after groups remaining =
      cacheMessageWeight key.parameter (fun input target => targetCacheEnvelope key q (payloadOf input) target signatures after groups remaining) before +
        newCachedTargetEnvelope key q signatures before after groups remaining :=
  cacheMessageWeight_of_le key.parameter _ before after.1 hcache

theorem newCachedTargetEnvelope_le_fixed (key : SecretKey) (q signatures : Nat) (before : QueryCache HashSpec) (after : CoverLogState)
    (hcache : before ≤ after.1) (hcap : QueryCache.enncard after.1 ≤ q)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    newCachedTargetEnvelope key q signatures before after groups remaining ≤
      newTargetEnvelopeCharge key before after.1 after.2 (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) (cacheSlotCount q before) signatures groups remaining := by
  apply cacheMessageWeight_mono
  intro input target
  split_ifs
  · exact targetShapeEnvelope_queries_mono _ _ _ signatures _ (cacheSlotCount_antitone q before after.1 hcache hcap) groups remaining hvalid
  · exact le_rfl

theorem expected_logTraced_sign_newCachedTargetEnvelope_le (key : SecretKey) (q signatures : Nat)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) (message : Message)
    (hcap : ∀ result ∈ support ((logTracedMappedAdversaryImpl key (.inr message)).run state), QueryCache.enncard result.2.1 ≤ q)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      newCachedTargetEnvelope key q signatures state.1 result.2 groups remaining) ≤
      (Fintype.card Index : ENNReal)⁻¹ * rawIndexCacheEnvelope key q signatures state groups remaining := by
  calc
    _ ≤ ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
        newTargetEnvelopeCharge key state.1 result.2.1 result.2.2 (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
          (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) (cacheSlotCount q state.1) signatures groups remaining := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key (.inr message)).run state)
      · exact mul_le_mul' le_rfl (newCachedTargetEnvelope_le_fixed key q signatures state.1 result.2
          (logTracedMappedAdversaryImpl_cache_le key (.inr message) state result hresult) (hcap result hresult) groups remaining hvalid)
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
    _ ≤ _ := by
      rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
      have hrun : (unloggedMappedAdversaryImpl key (.inr message)).run state.1 =
          (fun result => (result.1.1, result.2)) <$> (simulateQ romImpl (signWithView key message)).run state.1 :=
        (simulateQ_signWithView_fst_run key message state.1).symm
      rw [hrun, tsum_probOutput_map_mul]
      have h := expected_signWithView_newTargetEnvelopeCharge_le key message state.1 state.2 hsigned
        (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) (cacheSlotCount q state.1) signatures groups remaining hvalid
      apply h.trans_eq
      unfold rawIndexCacheEnvelope observedRawIndexShapeVector
      rw [targetShapeEnvelope_lift _ _ _ _ _ _ groups remaining hvalid]

end SphincsSecurity.Concrete

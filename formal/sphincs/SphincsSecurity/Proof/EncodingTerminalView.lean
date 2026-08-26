import SphincsSecurity.Proof.EncodingTerminalLatent
import SphincsSecurity.Proof.EncodingRisk
import SphincsSecurity.Proof.TerminalView

/-!
# Encoding chronology in the viewed terminal game

The generic final-continuation classifier is instantiated with the exact adversary state and verifier run retained by the observational game.
-/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

namespace Concrete

theorem ViewedEncodingCollisionWitness.encodingBad
    {parameter : PublicParameter}
    {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    {result : (Digest × Forgery × Bool) × ViewedFullTraceState}
    (hwitness : ViewedEncodingCollisionWitness parameter otsSecret ftsSecret result) :
    EncodingBad result.2.cache
      ⟨parameter, result.1.1, otsSecret, ftsSecret⟩ := by
  obtain ⟨f, digest, hf, hvalid, hnovel, hdigest, hadmissible, hcollision⟩ := hwitness
  exact hcollision.encodingBad hf

noncomputable def viewedCleanEncodingRisk
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState) : ℝ≥0∞ :=
  open Classical in
    if Bad parameter otsSecret ftsSecret result.2.cache then
      0
    else
      encodingTotalRiskPotential result.2.cache
        ⟨parameter, result.1.1, otsSecret, ftsSecret⟩

theorem probEvent_clean_viewedEncodingCollision_le_expectedRisk
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (oa : ProbComp ((Digest × Forgery × Bool) × ViewedFullTraceState)) :
    Pr[fun result => ¬ Bad parameter otsSecret ftsSecret result.2.cache ∧
        ViewedEncodingCollisionWitness parameter otsSecret ftsSecret result | oa] ≤
      ∑' result, Pr[= result | oa] *
        viewedCleanEncodingRisk parameter otsSecret ftsSecret result := by
  classical
  rw [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hevent : ¬ Bad parameter otsSecret ftsSecret result.2.cache ∧
      ViewedEncodingCollisionWitness parameter otsSecret ftsSecret result
  · rw [if_pos hevent, viewedCleanEncodingRisk, if_neg hevent.1]
    exact le_mul_of_one_le_right bot_le
      (one_le_encodingTotalRiskPotential_of_encodingBad hevent.2.encodingBad)
  · rw [if_neg hevent]
    exact bot_le

theorem gameAfterSecretsWithViewTrace_encodingBad_finalOutcome
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState)
    (hmem : result ∈ support
      (gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret))
    (hfinite : Finite result.2.cache)
    (hstructuralClean : ¬ Bad parameter otsSecret ftsSecret result.2.cache)
    (hbad : EncodingBad result.2.cache
      ⟨parameter, result.1.1, otsSecret, ftsSecret⟩) :
    ∃ (adversaryCache : QueryCache HashSpec) (position : EncodingPosition),
      HasEncodingTarget result.2.cache
          ⟨parameter, result.1.1, otsSecret, ftsSecret⟩ position
        ∧ FinalLatentEncodingAtOutcome
          ⟨parameter, result.1.1, otsSecret, ftsSecret⟩ position result.2.trace
            adversaryCache result.2.cache := by
  rw [gameAfterSecretsWithViewTrace, mem_support_bind_iff] at hmem
  obtain ⟨⟨root, rootCache⟩, hroot, hrest⟩ := hmem
  rw [mem_support_bind_iff] at hrest
  obtain ⟨restResult, hrest, hpureRoot⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hpureRoot
  subst result
  rw [gameRestWithViewTrace, mem_support_bind_iff] at hrest
  obtain ⟨⟨forgery, state⟩, hadversary, hfinish⟩ := hrest
  rw [mem_support_bind_iff] at hfinish
  obtain ⟨⟨⟨verified, targetView⟩, finalCache⟩, hverify, hpure⟩ := hfinish
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst restResult
  let publicKey : PublicKey := ⟨root, parameter⟩
  let secretKey : SecretKey := ⟨parameter, root, otsSecret, ftsSecret⟩
  let initialState : ViewedFullTraceState :=
    ⟨rootCache, ⟨[], [], []⟩, [], none⟩
  have hrootRun : (root, rootCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅) := by
    simpa only [simulateQ_romImpl_liftM] using hroot
  have hbase : (forgery, state.base) ∈ support
      ((simulateQ (fullTracedMappedAdversaryImpl secretKey)
        (adversary.main publicKey)).run initialState.base) := by
    rw [← viewedFullTracedMappedAdversaryImpl_projection secretKey
      (adversary.main publicKey) initialState, support_map]
    exact ⟨(forgery, state), by simpa only [initialState, publicKey, secretKey] using hadversary,
      rfl⟩
  have hchain : FullAdversaryTrace.CacheChain rootCache state.trace.intervals state.cache :=
    fullTracedMappedAdversaryImpl_cacheChain secretKey (adversary.main publicKey)
      rootCache rootCache ⟨[], [], []⟩ (forgery, state.base) (by rfl) hbase
  have hvalid : state.trace.ValidIntervals secretKey :=
    fullTracedMappedAdversaryImpl_validIntervals secretKey (adversary.main publicKey)
      rootCache ⟨[], [], []⟩ (forgery, state.base)
      (by simp [FullAdversaryTrace.ValidIntervals]) hbase
  have hinvariants := fullTracedMappedAdversaryImpl_interval_invariants secretKey
    (adversary.main publicKey) rootCache ⟨[], [], []⟩ (forgery, state.base)
    (by simp [FullAdversaryTrace.Consistent])
    (by simp [FullAdversaryTrace.IntervalsLe])
    (by simp [FullAdversaryTrace.Chronological]) hbase
  have hverifyLe : state.cache ≤ finalCache :=
    simulateQ_romImpl_cache_le
      (liftM (verifyWithView publicKey forgery.message forgery.signature) :
        OracleComp OracleWorld (Bool × FewTimeView))
      state.cache ((verified, targetView), finalCache) hverify
  have hintervals : state.trace.IntervalsLe finalCache := fun entry hentry =>
    ⟨(hinvariants.2.1 entry hentry).1.trans hverifyLe,
      (hinvariants.2.1 entry hentry).2.trans hverifyLe⟩
  have hrootEncodingNone : ∀ (position : EncodingPosition) (payload : HashInput),
      rootCache (tweakableHashInput parameter position.domain payload) = none := by
    intro position payload
    exact treeRoot_cache_encoding_none parameter topLayer rootTree
      (otsSecret topLayer rootTree) root rootCache hrootRun position.lay position.tree
      position.leafIdx payload
  obtain ⟨position, htarget, houtcome⟩ := encodingBad_finalOutcome hchain hvalid
    hintervals hfinite hstructuralClean hrootEncodingNone hverify hbad
  exact ⟨state.cache, position, htarget, houtcome⟩

theorem gameAfterSecretsWithViewTrace_encodingBad_finalOutcome_of_queryBound
    (adversary : Adversary) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState)
    (hmem : result ∈ support
      (gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret))
    (hstructuralClean : ¬ Bad parameter otsSecret ftsSecret result.2.cache)
    (hbad : EncodingBad result.2.cache
      ⟨parameter, result.1.1, otsSecret, ftsSecret⟩) :
    ∃ (adversaryCache : QueryCache HashSpec) (position : EncodingPosition),
      HasEncodingTarget result.2.cache
          ⟨parameter, result.1.1, otsSecret, ftsSecret⟩ position
        ∧ FinalLatentEncodingAtOutcome
          ⟨parameter, result.1.1, otsSecret, ftsSecret⟩ position result.2.trace
            adversaryCache result.2.cache := by
  have hbase : (result.1, result.2.base) ∈ support
      (gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret) := by
    rw [← gameAfterSecretsWithViewTrace_projection adversary parameter otsSecret ftsSecret,
      support_map]
    exact ⟨result, hmem, rfl⟩
  have hcard : QueryCache.enncard result.2.cache ≤ q :=
    gameAfterSecretsWithFullTrace_support_enncard_le adversary q hq parameter hparameter
      otsSecret hots ftsSecret hfts (result.1, result.2.base) hbase
  exact gameAfterSecretsWithViewTrace_encodingBad_finalOutcome adversary parameter otsSecret
    ftsSecret result hmem (Finite.of_enncard_le hcard) hstructuralClean hbad

end Concrete

end SphincsSecurity

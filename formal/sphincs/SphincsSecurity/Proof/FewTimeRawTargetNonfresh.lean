import SphincsSecurity.Proof.FewTimeRawTargetClassify

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

def ViewedHonestProperFewTimeLeakWitness (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :=
  ViewedTerminalWitnessFor parameter otsSecret ftsSecret
    fun f cache secretKey signingLog forgery index leaves =>
      ProperFewTimeLeak f cache secretKey signingLog index leaves ∧
        FullyHonestOpening f cache secretKey index leaves forgery.signature

noncomputable instance (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    DecidablePred (ViewedHonestProperFewTimeLeakWitness parameter otsSecret ftsSecret) :=
  fun _ => Classical.propDecidable _

theorem probEvent_exists_fixedRawTargetViewedTerminal_le_idealOrigin
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (signatures sources q : Nat)
    (hq : q ≤ 2 ^ 125) (hcache : QueryCache.enncard initialCache ≤ q) :
    Pr[fun result => ∃ distinct ∈ Finset.Icc 1 14,
        ∃ pattern : FewTimePattern signatures distinct,
        ∃ configuration : OriginConfiguration pattern sources,
        ∃ candidate : Fin q,
          FixedRawTargetViewedTerminal secretKey computation initialCache q
            configuration candidate.val result |
      (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
        computation).run ⟨initialCache, ⟨[], [], []⟩, [], none⟩] ≤
      q * rawTargetOriginUnionBound signatures sources := by
  apply probEvent_exists_originConfiguration_fixedRawOrdinal_viewedEvent_le_idealOrigin
    secretKey computation initialCache signatures sources q hq hcache q
      (fun _ _ configuration candidate =>
        FixedRawTargetViewedTerminal secretKey computation initialCache q
          configuration candidate.val)
  intro distinct pattern configuration candidate result hresult hevent
  obtain ⟨hcacheFinal, hterminal⟩ := hevent
  obtain ⟨hcomplete, hhit⟩ := hterminal result hresult rfl
  exact ⟨hcomplete, hhit, hcacheFinal⟩

theorem probEvent_gameRestWithViewTrace_nonfresh_honest_leak_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqMax : q ≤ 2 ^ 125)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets)
    (root : Digest) (rootCache : QueryCache HashSpec)
    (hroot : (root, rootCache) ∈ support
      ((simulateQ romImpl
        (liftM ((treeRoot parameter topLayer rootTree
          (otsSecret topLayer rootTree) : OracleComp HashSpec Digest)) :
            OracleComp OracleWorld Digest)).run ∅)) :
    Pr[fun rest =>
        let result : (Digest × Forgery × Bool) × ViewedFullTraceState :=
          ((root, rest.1.1, rest.1.2), rest.2)
        ViewedHonestProperFewTimeLeakWitness parameter otsSecret ftsSecret result
          ∧ ¬VerifierFreshTarget parameter result |
      gameRestWithViewTrace adversary ⟨root, parameter⟩
        ⟨parameter, root, otsSecret, ftsSecret⟩ rootCache] ≤
      q * rawTargetOriginUnionBound signatureLimit q := by
  classical
  let secretKey : SecretKey := ⟨parameter, root, otsSecret, ftsSecret⟩
  let publicKey : PublicKey := ⟨root, parameter⟩
  let initialState : ViewedFullTraceState :=
    ⟨rootCache, ⟨[], [], []⟩, [], none⟩
  let run := (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
    (adversary.main publicKey)).run initialState
  let finish : Forgery × ViewedFullTraceState →
      ProbComp ((Forgery × Bool) × ViewedFullTraceState) := fun prior => do
    let ((verified, targetView), finalCache) ←
      (simulateQ romImpl
        (liftM (verifyWithView publicKey prior.1.message prior.1.signature) :
          OracleComp OracleWorld (Bool × FewTimeView))).run prior.2.cache
    let log := prior.2.trace.signing.toSigningLog
    let verdict := decide (SigningTranscript.Valid log ∧
      ¬SigningTranscript.Contains log prior.1) && verified
    pure ((prior.1, verdict),
      ⟨finalCache, prior.2.trace, prior.2.views, some targetView⟩)
  let prefixEvent := fun prior : Forgery × ViewedFullTraceState =>
    ∃ distinct ∈ Finset.Icc 1 14,
      ∃ pattern : FewTimePattern signatureLimit distinct,
      ∃ configuration : OriginConfiguration pattern q,
      ∃ candidate : Fin q,
        FixedRawTargetViewedTerminal secretKey (adversary.main publicKey)
          rootCache q configuration candidate.val prior
  have hgame : gameRestWithViewTrace adversary publicKey secretKey rootCache =
      run >>= finish := by
    rfl
  rw [show ⟨root, parameter⟩ = publicKey from rfl,
    show ⟨parameter, root, otsSecret, ftsSecret⟩ = secretKey from rfl, hgame]
  calc
    _ ≤ Pr[prefixEvent | run] := by
      apply probEvent_bind_le_probEvent
      intro prior hprior hnotPrefix
      rcases prior with ⟨forgery, state⟩
      apply probEvent_eq_zero
      intro rest hrest hevent
      rw [mem_support_bind_iff] at hrest
      obtain ⟨⟨⟨verified, targetView⟩, finalCache⟩, hverify, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst rest
      let result : (Digest × Forgery × Bool) × ViewedFullTraceState :=
        ((root, forgery,
          decide (SigningTranscript.Valid state.trace.signing.toSigningLog ∧
            ¬SigningTranscript.Contains state.trace.signing.toSigningLog forgery) &&
              verified),
          ⟨finalCache, state.trace, state.views, some targetView⟩)
      have hrestSupport :
          ((forgery,
              decide (SigningTranscript.Valid state.trace.signing.toSigningLog ∧
                ¬SigningTranscript.Contains state.trace.signing.toSigningLog forgery) &&
                  verified),
            ⟨finalCache, state.trace, state.views, some targetView⟩) ∈
            support (gameRestWithViewTrace adversary publicKey secretKey rootCache) := by
        rw [hgame, mem_support_bind_iff]
        refine ⟨(forgery, state), hprior, ?_⟩
        rw [mem_support_bind_iff]
        exact ⟨((verified, targetView), finalCache), hverify,
          by simp only [support_pure, Set.mem_singleton_iff]⟩
      have hresult : result ∈ support
          (gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret) := by
        rw [gameAfterSecretsWithViewTrace, mem_support_bind_iff]
        refine ⟨(root, rootCache), hroot, ?_⟩
        rw [mem_support_bind_iff]
        exact ⟨_, hrestSupport, by simp [result]⟩
      obtain ⟨f, digest, hf, hvalid, _, hdigest, hadmissible, hproper, hfull⟩ := hevent.1
      have hcacheLe : state.cache ≤ finalCache :=
        simulateQ_romImpl_cache_le
          (liftM (verifyWithView publicKey forgery.message forgery.signature) :
            OracleComp OracleWorld (Bool × FewTimeView)) state.cache
              ((verified, targetView), finalCache) hverify
      rcases gameAfterSecretsWithViewTrace_honestLeak_target_classified_at_adversary_state
          adversary q hq parameter hparameter otsSecret hots ftsSecret hfts result hresult
          f hf digest hdigest hadmissible hproper hfull hvalid rootCache state rfl hcacheLe with
        hfresh | hclassified
      · exact hevent.2 hfresh
      · obtain ⟨distinct, hdistinct, pattern, configuration, candidate, hterminal⟩ :=
          hclassified
        apply hnotPrefix
        exact ⟨distinct, hdistinct, pattern, configuration, candidate, hterminal⟩
    _ ≤ _ := probEvent_exists_fixedRawTargetViewedTerminal_le_idealOrigin
      secretKey (adversary.main publicKey) rootCache signatureLimit q q hqMax
        (by
          have hroot' : QueryCache.enncard rootCache ≤ q := by
            have hprojected : (root, rootCache) ∈ support
                ((simulateQ romImpl
                  (liftM ((treeRoot parameter topLayer rootTree
                    (otsSecret topLayer rootTree) : OracleComp HashSpec Digest)) :
                      OracleComp OracleWorld Digest)).run ∅) := hroot
            have hgameBound := isQueryBoundP_gameAfterSecrets adversary q hq
              hparameter hots hfts
            rw [gameAfterSecrets] at hgameBound
            have hrootBound := OracleComp.IsQueryBoundP.of_bind_left
              (p := fun input : OracleWorld.Domain => input matches Sum.inr _) hgameBound
            have hbound := simulateQ_romImpl_enncard_le_queryBound
              (liftM ((treeRoot parameter topLayer rootTree
                (otsSecret topLayer rootTree) : OracleComp HashSpec Digest)) :
                  OracleComp OracleWorld Digest) q
              hrootBound
              (root, rootCache) hprojected
            exact hbound
          exact hroot')

theorem probEvent_gameAfterSecretsWithViewTrace_nonfresh_honest_leak_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqMax : q ≤ 2 ^ 125)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    Pr[fun result =>
        ViewedHonestProperFewTimeLeakWitness parameter otsSecret ftsSecret result
          ∧ ¬VerifierFreshTarget parameter result |
      gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] ≤
      q * rawTargetOriginUnionBound signatureLimit q := by
  rw [gameAfterSecretsWithViewTrace]
  apply probEvent_bind_le_of_forall_le
  rintro ⟨root, rootCache⟩ hroot
  let attach := fun rest : (Forgery × Bool) × ViewedFullTraceState =>
    ((root, rest.1.1, rest.1.2), rest.2)
  change Pr[fun result =>
      ViewedHonestProperFewTimeLeakWitness parameter otsSecret ftsSecret result ∧
        ¬VerifierFreshTarget parameter result |
    gameRestWithViewTrace adversary ⟨root, parameter⟩
      ⟨parameter, root, otsSecret, ftsSecret⟩ rootCache >>= pure ∘ attach] ≤ _
  rw [probEvent_bind_pure_comp]
  exact probEvent_gameRestWithViewTrace_nonfresh_honest_leak_le adversary q hq hqMax
    parameter hparameter otsSecret hots ftsSecret hfts root rootCache hroot

theorem probEvent_gameAfterSecretsWithViewTrace_nonfresh_honest_leak_le_mul_inv131
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqMax : q ≤ 2 ^ 125)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    Pr[fun result =>
        ViewedHonestProperFewTimeLeakWitness parameter otsSecret ftsSecret result
          ∧ ¬VerifierFreshTarget parameter result |
      gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] ≤
      q * ((2 ^ 131 : Nat) : ℝ≥0∞)⁻¹ := by
  exact (probEvent_gameAfterSecretsWithViewTrace_nonfresh_honest_leak_le adversary q hq hqMax
    parameter hparameter otsSecret hots ftsSecret hfts).trans
      (mul_le_mul' le_rfl (rawTargetOriginUnionBound_le_inv131 le_rfl hqMax))

end SphincsSecurity.Concrete

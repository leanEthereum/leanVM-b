import SphincsSecurity.Proof.FewTimeTarget125
import SphincsSecurity.Proof.FewTime125Count
import SphincsSecurity.Proof.MessageCollision

namespace SphincsSecurity.Concrete.Range125

open OracleComp OracleSpec ENNReal

theorem singletonOriginUnionBound_le_inv (q : Nat) (hq : q ≤ 2 ^ 125) :
    singletonOriginUnionBound signatureLimit q ≤
      ((2 ^ 141 : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  rw [singletonOriginUnionBound_eq]
  calc
    (∑ pattern : FewTimePattern signatureLimit 1,
        originChoiceMass pattern.selected q ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ *
          ((2 ^ 166 : Nat) : ℝ≥0∞)⁻¹) ≤
        ∑ _pattern : FewTimePattern signatureLimit 1,
          2 * ((2 ^ 166 : Nat) : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_le_sum
      intro pattern _
      have hmass := pattern.originChoiceMass_le_five_fourths_pow hq
      rw [pow_one] at hmass
      have hratio : (5 / 4 : ℝ≥0∞) ≤ 2 := ENNReal.div_le_of_le_mul (by norm_num)
      have hmass : originChoiceMass pattern.selected q ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ ≤ 2 :=
        hmass.trans hratio
      simpa only [mul_comm] using
        (mul_le_mul_left hmass ((2 ^ 166 : Nat) : ℝ≥0∞)⁻¹)
    _ = (Fintype.card (FewTimePattern signatureLimit 1) : ℝ≥0∞) *
        (2 * ((2 ^ 166 : Nat) : ℝ≥0∞)⁻¹) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ((2 ^ 141 : Nat) : ℝ≥0∞)⁻¹ := by
      have hcard : Fintype.card (FewTimePattern signatureLimit 1) = signatureLimit := by
        simp [fewTimePattern_card]
      rw [hcard, signatureLimit]
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
      norm_num

theorem probEvent_exists_singletonOriginConfiguration_fixedOrdinal_viewedEvent_le
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (signatures sources q : Nat)
    (hq : q ≤ 2 ^ 125) (hcache : QueryCache.enncard initialCache ≤ q)
    (candidates : Nat)
    (viewedEvent : ∀ pattern : FewTimePattern signatures 1,
      OriginConfiguration pattern sources → Fin candidates →
        α × ViewedFullTraceState → Prop)
    (himp : ∀ (pattern : FewTimePattern signatures 1)
      (configuration : OriginConfiguration pattern sources) (candidate : Fin candidates)
      (result : α × OriginTargetMonitorState configuration),
      result ∈ support
        ((simulateQ
          (originTargetMonitoredAdversaryImpl configuration secretKey candidate.val)
          computation).run (OriginTargetMonitorState.initial configuration initialCache)) →
      viewedEvent pattern configuration candidate
          (result.1, result.2.origin.viewed) →
        result.2.Complete ∧
          (∀ target, result.2.targetView = some target →
            FixedFewTimePatternHit pattern.assignment
              (result.2.origin.observation.views, target)) ∧
          QueryCache.enncard result.2.origin.viewed.cache ≤ q) :
    Pr[fun result => ∃ pattern : FewTimePattern signatures 1,
        ∃ configuration : OriginConfiguration pattern sources,
        ∃ candidate : Fin candidates,
          viewedEvent pattern configuration candidate result |
      (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
        computation).run ⟨initialCache, ⟨[], [], []⟩, [], none⟩] ≤
      candidates * singletonOriginUnionBound signatures sources := by
  classical
  let run := (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
    computation).run ⟨initialCache, ⟨[], [], []⟩, [], none⟩
  calc
    Pr[fun result => ∃ pattern : FewTimePattern signatures 1,
        ∃ configuration : OriginConfiguration pattern sources,
        ∃ candidate : Fin candidates,
          viewedEvent pattern configuration candidate result | run] =
        Pr[fun result => ∃ pattern ∈
            (Finset.univ : Finset (FewTimePattern signatures 1)),
          ∃ configuration : OriginConfiguration pattern sources,
          ∃ candidate : Fin candidates,
            viewedEvent pattern configuration candidate result | run] := by
      congr 1
      funext result
      simp
    _ ≤ ∑ pattern : FewTimePattern signatures 1,
        Pr[fun result =>
          ∃ configuration : OriginConfiguration pattern sources,
          ∃ candidate : Fin candidates,
            viewedEvent pattern configuration candidate result | run] :=
      probEvent_exists_finset_le_sum Finset.univ run fun pattern result =>
        ∃ configuration : OriginConfiguration pattern sources,
        ∃ candidate : Fin candidates,
          viewedEvent pattern configuration candidate result
    _ ≤ ∑ pattern : FewTimePattern signatures 1,
        ∑ configuration : OriginConfiguration pattern sources,
          Pr[fun result => ∃ candidate : Fin candidates,
            viewedEvent pattern configuration candidate result | run] := by
      apply Finset.sum_le_sum
      intro pattern _
      calc
        _ = Pr[fun result => ∃ configuration ∈
              (Finset.univ : Finset (OriginConfiguration pattern sources)),
            ∃ candidate : Fin candidates,
              viewedEvent pattern configuration candidate result | run] := by
            congr 1
            funext result
            simp
        _ ≤ _ := probEvent_exists_finset_le_sum Finset.univ run fun configuration result =>
          ∃ candidate : Fin candidates,
            viewedEvent pattern configuration candidate result
    _ ≤ ∑ pattern : FewTimePattern signatures 1,
        ∑ configuration : OriginConfiguration pattern sources,
          candidates * Pr[configuration.Hit |
            ($ᵗ configuration.Sample : ProbComp configuration.Sample)] := by
      apply Finset.sum_le_sum
      intro pattern _
      apply Finset.sum_le_sum
      intro configuration _
      exact probEvent_exists_fixedOrdinal_viewedEvent_le_ideal configuration secretKey
        computation initialCache q hq hcache candidates
          (viewedEvent pattern configuration) (himp pattern configuration)
    _ = candidates * singletonOriginUnionBound signatures sources := by
      rw [singletonOriginUnionBound]
      simp_rw [← Finset.mul_sum]

theorem probEvent_someFixedSingletonOriginTargetViewedTerminal_le
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (signatures sources q : Nat)
    (hq : q ≤ 2 ^ 125) (hcache : QueryCache.enncard initialCache ≤ q)
    (candidates : Nat) :
    Pr[SomeFixedSingletonOriginTargetViewedTerminal secretKey computation initialCache
        signatures sources q candidates |
      (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
        computation).run ⟨initialCache, ⟨[], [], []⟩, [], none⟩] ≤
      candidates * singletonOriginUnionBound signatures sources := by
  unfold SomeFixedSingletonOriginTargetViewedTerminal
  apply probEvent_exists_singletonOriginConfiguration_fixedOrdinal_viewedEvent_le
    secretKey computation initialCache signatures sources q hq hcache candidates
      (fun _ configuration candidate =>
        FixedOriginTargetViewedTerminal secretKey computation initialCache q
          configuration candidate.val)
  intro pattern configuration candidate result hresult hevent
  obtain ⟨hcacheFinal, hterminal⟩ := hevent
  obtain ⟨hcomplete, hhit⟩ := hterminal result hresult rfl
  exact ⟨hcomplete, hhit, hcacheFinal⟩

theorem probEvent_someFixedOneOriginTargetViewedTerminal_le
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (signatures sources q : Nat)
    (hq : q ≤ 2 ^ 125) (hcache : QueryCache.enncard initialCache ≤ q)
    (candidates : Nat) :
    Pr[SomeFixedOneOriginTargetViewedTerminal secretKey computation initialCache
        signatures sources q candidates |
      (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
        computation).run ⟨initialCache, ⟨[], [], []⟩, [], none⟩] ≤
      candidates * singletonOriginUnionBound signatures sources := by
  calc
    _ = Pr[SomeFixedSingletonOriginTargetViewedTerminal secretKey computation initialCache
          signatures sources q candidates |
        (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
          computation).run ⟨initialCache, ⟨[], [], []⟩, [], none⟩] := by
      congr 1
      funext result
      exact propext (someFixedOneOriginTargetViewedTerminal_iff secretKey computation
        initialCache signatures sources q candidates result)
    _ ≤ _ := probEvent_someFixedSingletonOriginTargetViewedTerminal_le
      secretKey computation initialCache signatures sources q hq hcache candidates

theorem probEvent_gameRestWithViewTrace_nonfresh_messageCollision_le
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
        ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result ∧
          ¬VerifierFreshTarget parameter result |
      gameRestWithViewTrace adversary ⟨root, parameter⟩
        ⟨parameter, root, otsSecret, ftsSecret⟩ rootCache] ≤
      q * singletonOriginUnionBound signatureLimit q := by
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
    SomeFixedSingletonOriginTargetViewedTerminal secretKey
      (adversary.main publicKey) rootCache signatureLimit q q q prior
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
      obtain ⟨f, digest, hf, hvalid, _, hdigest, hadmissible,
        hcollision, _⟩ := hevent.1
      obtain ⟨cover, hcard, hne⟩ :=
        hcollision.exists_singletonFewTimeCover digest hdigest
      have hcacheLe : state.cache ≤ finalCache :=
        simulateQ_romImpl_cache_le
          (liftM (verifyWithView publicKey forgery.message forgery.signature) :
            OracleComp OracleWorld (Bool × FewTimeView)) state.cache
              ((verified, targetView), finalCache) hverify
      rcases gameAfterSecretsWithViewTrace_singletonCover_target_classified_at_adversary_state
          adversary q hq parameter hparameter otsSecret hots ftsSecret hfts result hresult
          f hf digest hdigest hadmissible cover hcard hne hvalid rootCache state rfl rfl
          hcacheLe with hfresh | hclassified
      · exact hevent.2 hfresh
      · obtain ⟨distinct, hdistinct, pattern, configuration, candidate, hterminal⟩ :=
          hclassified
        subst distinct
        apply hnotPrefix
        unfold prefixEvent SomeFixedSingletonOriginTargetViewedTerminal
        exact ⟨pattern, configuration, candidate, hterminal⟩
    _ ≤ _ := probEvent_someFixedSingletonOriginTargetViewedTerminal_le
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
                  OracleComp OracleWorld Digest) q hrootBound
              (root, rootCache) hprojected
            exact hbound
          exact hroot') q

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in

theorem probEvent_gameRestWithViewTrace_fresh_messageCollision_le
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
        ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result ∧
          VerifierFreshTarget parameter result |
      gameRestWithViewTrace adversary ⟨root, parameter⟩
        ⟨parameter, root, otsSecret, ftsSecret⟩ rootCache] ≤
      ((q + 1 : Nat) : ℝ≥0∞) * singletonOriginUnionBound signatureLimit q := by
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
  let freshEvent := fun rest : (Forgery × Bool) × ViewedFullTraceState =>
    let result : (Digest × Forgery × Bool) × ViewedFullTraceState :=
      ((root, rest.1.1, rest.1.2), rest.2)
    ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result ∧
      VerifierFreshTarget parameter result
  have hrootNone : ∀ payload,
      rootCache (tweakableHashInput parameter .message payload) = none := by
    have hroot' : (root, rootCache) ∈ support
        ((simulateQ (randomOracle : QueryImpl HashSpec _)
          (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅) := by
      simpa only [simulateQ_romImpl_liftM] using hroot
    exact fun payload => treeRoot_cache_message_none parameter topLayer rootTree
      (otsSecret topLayer rootTree) root rootCache hroot' payload
  have hrootCache : QueryCache.enncard rootCache ≤ q := by
    have hgameBound := isQueryBoundP_gameAfterSecrets adversary q hq
      hparameter hots hfts
    rw [gameAfterSecrets] at hgameBound
    have hrootBound := OracleComp.IsQueryBoundP.of_bind_left
      (p := fun input : OracleWorld.Domain => input matches Sum.inr _) hgameBound
    exact simulateQ_romImpl_enncard_le_queryBound
      (liftM ((treeRoot parameter topLayer rootTree
        (otsSecret topLayer rootTree) : OracleComp HashSpec Digest)) :
          OracleComp OracleWorld Digest) q hrootBound (root, rootCache) hroot
  have hprefixBound :=
    probEvent_someFixedOneOriginTargetViewedTerminal_le
      (α := Forgery × HashOutput) (secretKey := secretKey)
      (computation := adversaryWithTargetQuery adversary publicKey)
      (initialCache := rootCache) (signatures := signatureLimit) (sources := q)
      (q := q) (hq := hqMax) (hcache := hrootCache) (candidates := q + 1)
  have hgame : gameRestWithViewTrace adversary publicKey secretKey rootCache =
      run >>= finish := rfl
  rw [show ⟨root, parameter⟩ = publicKey from rfl,
    show ⟨parameter, root, otsSecret, ftsSecret⟩ = secretKey from rfl, hgame]
  change Pr[freshEvent | run >>= finish] ≤ _
  have hfirst : Pr[freshEvent | run >>= finish] ≤
      Pr[SomeFixedOneOriginTargetViewedTerminal secretKey
        (adversaryWithTargetQuery adversary publicKey) rootCache signatureLimit q q (q + 1) |
          (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
            (adversaryWithTargetQuery adversary publicKey)).run
              ⟨rootCache, ⟨[], [], []⟩, [], none⟩] := by
    rw [adversaryWithTargetQuery_viewed_run]
    change Pr[_ | run >>= _] ≤
      Pr[SomeFixedOneOriginTargetViewedTerminal secretKey
        (adversaryWithTargetQuery adversary publicKey) rootCache signatureLimit q q (q + 1) |
          run >>= _]
    apply probEvent_bind_le_bind_of_forall_le
    rintro ⟨forgery, state⟩ hprior
    let input := tweakableHashInput parameter .message
      (messageDigestPayload root forgery.message forgery.signature.randomness)
    change Pr[_ |
      (simulateQ romImpl
        (liftM (verifyWithView publicKey forgery.message forgery.signature) :
          OracleComp OracleWorld (Bool × FewTimeView))).run state.cache >>= _] ≤ _
    rw [verifyWithView_split_run]
    simp only [bind_assoc]
    rw [show tweakableHashInput publicKey.parameter .message
      (messageDigestPayload publicKey.root forgery.message
        forgery.signature.randomness) = input from rfl]
    change _ ≤ Pr[SomeFixedOneOriginTargetViewedTerminal secretKey
      (adversaryWithTargetQuery adversary publicKey) rootCache signatureLimit q q (q + 1) |
      (randomOracle input).run state.cache >>= pure ∘ fun source =>
        ((forgery, source.1), appendDirectTargetViewedState input state.cache
          source.1 source.2 state)]
    rw [probEvent_bind_pure_comp]
    change Pr[_ | (randomOracle input).run state.cache >>= _] ≤
      Pr[fun source => SomeFixedOneOriginTargetViewedTerminal secretKey
        (adversaryWithTargetQuery adversary publicKey) rootCache signatureLimit q q (q + 1)
          ((forgery, source.1),
        appendDirectTargetViewedState input state.cache source.1 source.2 state) |
          (randomOracle input).run state.cache]
    apply probEvent_bind_le_probEvent
    rintro ⟨output, digestCache⟩ hquery hnotPrefix
    apply probEvent_eq_zero
    intro rest hrest hevent
    rw [mem_support_bind_iff] at hrest
    obtain ⟨⟨⟨verified, targetView⟩, finalCache⟩, hverifyRest, hpure⟩ := hrest
    simp only [support_pure, Set.mem_singleton_iff] at hpure
    subst rest
    let result : (Digest × Forgery × Bool) × ViewedFullTraceState :=
      ((root, forgery,
        decide (SigningTranscript.Valid state.trace.signing.toSigningLog ∧
          ¬SigningTranscript.Contains state.trace.signing.toSigningLog forgery) &&
            verified),
        ⟨finalCache, state.trace, state.views, some targetView⟩)
    change ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result ∧
      VerifierFreshTarget parameter result at hevent
    have hverify : ((verified, targetView), finalCache) ∈ support
        ((simulateQ romImpl
          (liftM (verifyWithView publicKey forgery.message forgery.signature) :
            OracleComp OracleWorld (Bool × FewTimeView))).run state.cache) := by
      rw [verifyWithView_split_run, mem_support_bind_iff]
      exact ⟨(output, digestCache), by simpa only [input, publicKey] using hquery,
        hverifyRest⟩
    have hrestSupport :
        ((forgery,
            decide (SigningTranscript.Valid state.trace.signing.toSigningLog ∧
              ¬SigningTranscript.Contains state.trace.signing.toSigningLog forgery) &&
                verified),
          ⟨finalCache, state.trace, state.views, some targetView⟩) ∈
          support (gameRestWithViewTrace adversary publicKey secretKey rootCache) := by
      rw [gameRestWithViewTrace, mem_support_bind_iff]
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
    obtain ⟨f, digest, hf, hvalid, _, hdigest, _, hcollision, _⟩ := hevent.1
    obtain ⟨cover, hcard, _⟩ :=
      hcollision.exists_singletonFewTimeCover digest hdigest
    obtain ⟨otherRootCache, adversaryCache, _, _, hotherRootNone,
      hotherChain, hadversaryMiss, _, _, _⟩ := hevent.2
    have hbase : (forgery, state.base) ∈ support
        ((simulateQ (fullTracedMappedAdversaryImpl secretKey)
          (adversary.main publicKey)).run initialState.base) := by
      rw [← viewedFullTracedMappedAdversaryImpl_projection secretKey
        (adversary.main publicKey) initialState, support_map]
      exact ⟨(forgery, state), hprior, rfl⟩
    have hchain : FullAdversaryTrace.CacheChain rootCache state.trace.intervals
        state.cache :=
      fullTracedMappedAdversaryImpl_cacheChain secretKey (adversary.main publicKey)
        rootCache rootCache ⟨[], [], []⟩ (forgery, state.base) (by rfl) hbase
    have hmiss : state.cache input = none := by
      have hrootInput : rootCache input = none := by
        simpa only [input] using hrootNone
          (messageDigestPayload root forgery.message forgery.signature.randomness)
      have hotherRootInput : otherRootCache input = none := by
        simpa only [input, result] using hotherRootNone
          (messageDigestPayload root forgery.message forgery.signature.randomness)
      have hlookup := FullAdversaryTrace.CacheChain.finish_lookup_eq input
        (hrootInput.trans hotherRootInput.symm) hchain
        (by simpa only [result] using hotherChain)
      exact hlookup.trans hadversaryMiss
    have hdigestLe : digestCache ≤ finalCache :=
      simulateQ_romImpl_cache_le
        (liftM (verifyWithViewAfterOutput publicKey forgery.signature output) :
          OracleComp OracleWorld (Bool × FewTimeView)) digestCache
            ((verified, targetView), finalCache) hverifyRest
    have hcachedDigest : digestCache input = some output :=
      randomOracle_output_cached input state.cache digestCache output (by
        have hquerySim : simulateQ (randomOracle : QueryImpl HashSpec _)
            (oracleHash input) = randomOracle input := by
          change simulateQ (randomOracle : QueryImpl HashSpec _)
            (liftM (HashSpec.query input)) = randomOracle input
          rw [simulateQ_spec_query]
        rw [hquerySim]
        exact hquery)
    have hcachedFinal : finalCache input = some output := hdigestLe hcachedDigest
    have hanswer : f input = output := hf (by simpa only [result] using hcachedFinal)
    have hdigestOutput : truncateMessageDigest output = digest := by
      have hdigest' : truncateMessageDigest (f input) = digest := by
        simpa only [messageDigest, oracleHash, evalWithAnswerFn_bind,
          evalWithAnswerFn_query, evalWithAnswerFn_pure, result, input] using hdigest
      rwa [hanswer] at hdigest'
    have htargetOutput : hashOutputFewTimeView output =
        fewTimeTargetView (digestIndex digest) (digestLeaves digest) := by
      simp [hashOutputFewTimeView, fewTimeTargetView, hdigestOutput]
    have hfullBase : (result.1, result.2.base) ∈ support
        (gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret) := by
      rw [← gameAfterSecretsWithViewTrace_projection adversary parameter otsSecret
        ftsSecret, support_map]
      exact ⟨result, hresult, rfl⟩
    obtain ⟨configuration, hrealized⟩ :=
      cover.exists_paddedRealized_originConfiguration_of_queryBudget
        adversary q hq parameter hparameter otsSecret hots ftsSecret hfts
          (result.1, result.2.base) hfullBase f hf (digestIndex digest)
            (digestLeaves digest) signatureLimit hvalid
    have hfinalCache : QueryCache.enncard finalCache ≤ q := by
      have hbound := gameAfterSecretsWithFullTrace_support_enncard_le adversary q hq
        parameter hparameter otsSecret hots ftsSecret hfts
          (result.1, result.2.base) hfullBase
      change QueryCache.enncard result.2.cache ≤ q at hbound
      simpa only [result] using hbound
    have hdigestCard : QueryCache.enncard digestCache ≤ q :=
      (QueryCache.enncard_mono hdigestLe).trans hfinalCache
    have hcountLe : freshTargetCandidateCount secretKey state.trace ≤ q := by
      rw [freshTargetCandidateCount_eq_card]
      have hbound := gameAfterSecretsWithViewTrace_freshTargetCandidatePositions_card_le
        adversary q hq parameter hparameter otsSecret hots ftsSecret hfts result hresult
      simp only [result] at hbound
      exact_mod_cast hbound
    let candidate : Fin (q + 1) :=
      ⟨freshTargetCandidateCount secretKey state.trace, by omega⟩
    unfold SomeFixedOneOriginTargetViewedTerminal at hnotPrefix
    apply hnotPrefix
    refine ⟨cover.entries.card, hcard, cover.pattern.pad hvalid,
      configuration, candidate, ?_⟩
    exact configuration.verifierTarget_fixedTerminal_for_cover adversary parameter otsSecret
      ftsSecret result hresult f hf digest cover hvalid hrealized
        rootCache state hprior rfl rfl input output digestCache rfl hmiss
          (by simpa only [input] using hquery) hdigestLe htargetOutput q hdigestCard
  calc
    Pr[freshEvent | run >>= finish] ≤
        Pr[SomeFixedOneOriginTargetViewedTerminal secretKey
          (adversaryWithTargetQuery adversary publicKey) rootCache signatureLimit q q (q + 1) |
            (simulateQ (viewedFullTracedMappedAdversaryImpl secretKey)
              (adversaryWithTargetQuery adversary publicKey)).run
                ⟨rootCache, ⟨[], [], []⟩, [], none⟩] := hfirst
    _ ≤ ((q + 1 : Nat) : ℝ≥0∞) * singletonOriginUnionBound signatureLimit q :=
      hprefixBound

theorem probEvent_gameAfterSecretsWithViewTrace_nonfresh_messageCollision_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqMax : q ≤ 2 ^ 125)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    Pr[fun result =>
        ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result ∧
          ¬VerifierFreshTarget parameter result |
      gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] ≤
      q * singletonOriginUnionBound signatureLimit q := by
  rw [gameAfterSecretsWithViewTrace]
  apply probEvent_bind_le_of_forall_le
  rintro ⟨root, rootCache⟩ hroot
  let attach := fun rest : (Forgery × Bool) × ViewedFullTraceState =>
    ((root, rest.1.1, rest.1.2), rest.2)
  change Pr[fun result =>
      ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result ∧
        ¬VerifierFreshTarget parameter result |
    gameRestWithViewTrace adversary ⟨root, parameter⟩
      ⟨parameter, root, otsSecret, ftsSecret⟩ rootCache >>= pure ∘ attach] ≤ _
  rw [probEvent_bind_pure_comp]
  exact probEvent_gameRestWithViewTrace_nonfresh_messageCollision_le adversary q hq hqMax
    parameter hparameter otsSecret hots ftsSecret hfts root rootCache hroot

theorem probEvent_gameAfterSecretsWithViewTrace_fresh_messageCollision_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqMax : q ≤ 2 ^ 125)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    Pr[fun result =>
        ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result ∧
          VerifierFreshTarget parameter result |
      gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] ≤
      ((q + 1 : Nat) : ℝ≥0∞) * singletonOriginUnionBound signatureLimit q := by
  rw [gameAfterSecretsWithViewTrace]
  apply probEvent_bind_le_of_forall_le
  rintro ⟨root, rootCache⟩ hroot
  let attach := fun rest : (Forgery × Bool) × ViewedFullTraceState =>
    ((root, rest.1.1, rest.1.2), rest.2)
  change Pr[fun result =>
      ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result ∧
        VerifierFreshTarget parameter result |
    gameRestWithViewTrace adversary ⟨root, parameter⟩
      ⟨parameter, root, otsSecret, ftsSecret⟩ rootCache >>= pure ∘ attach] ≤ _
  rw [probEvent_bind_pure_comp]
  exact probEvent_gameRestWithViewTrace_fresh_messageCollision_le adversary q hq hqMax
    parameter hparameter otsSecret hots ftsSecret hfts root rootCache hroot

theorem probEvent_gameAfterSecretsWithViewTrace_messageCollision_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqMax : q ≤ 2 ^ 125)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    Pr[ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret |
      gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] ≤
      q * singletonOriginUnionBound signatureLimit q +
        ((q + 1 : Nat) : ℝ≥0∞) * singletonOriginUnionBound signatureLimit q := by
  classical
  calc
    _ ≤ Pr[fun result =>
        (ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result ∧
          ¬VerifierFreshTarget parameter result) ∨
        (ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result ∧
          VerifierFreshTarget parameter result) |
      gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] := by
        apply probEvent_mono
        intro result _ hcollision
        by_cases hfresh : VerifierFreshTarget parameter result
        · exact Or.inr ⟨hcollision, hfresh⟩
        · exact Or.inl ⟨hcollision, hfresh⟩
    _ ≤ _ := (probEvent_or_le _ _ _).trans (add_le_add
      (probEvent_gameAfterSecretsWithViewTrace_nonfresh_messageCollision_le adversary q hq
        hqMax parameter hparameter otsSecret hots ftsSecret hfts)
      (probEvent_gameAfterSecretsWithViewTrace_fresh_messageCollision_le adversary q hq
        hqMax parameter hparameter otsSecret hots ftsSecret hfts))

theorem probEvent_gameAfterSecretsWithViewTrace_messageCollision_le_inv
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 125)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    Pr[ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret |
      gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] ≤
      (q : ℝ≥0∞) * ((2 ^ 139 : Nat) : ℝ≥0∞)⁻¹ := by
  calc
    _ ≤ q * singletonOriginUnionBound signatureLimit q +
          ((q + 1 : Nat) : ℝ≥0∞) * singletonOriginUnionBound signatureLimit q :=
      probEvent_gameAfterSecretsWithViewTrace_messageCollision_le adversary q hq hqMax
        parameter hparameter otsSecret hots ftsSecret hfts
    _ = ((2 * q + 1 : Nat) : ℝ≥0∞) *
        singletonOriginUnionBound signatureLimit q := by
      push_cast
      ring
    _ ≤ ((2 * q + 1 : Nat) : ℝ≥0∞) *
        ((2 ^ 141 : Nat) : ℝ≥0∞)⁻¹ := by
      have hmass := singletonOriginUnionBound_le_inv q hqMax
      calc
        ((2 * q + 1 : Nat) : ℝ≥0∞) * singletonOriginUnionBound signatureLimit q =
            singletonOriginUnionBound signatureLimit q * (2 * q + 1 : Nat) := mul_comm _ _
        _ ≤ ((2 ^ 141 : Nat) : ℝ≥0∞)⁻¹ * (2 * q + 1 : Nat) :=
          mul_le_mul_left hmass _
        _ = ((2 * q + 1 : Nat) : ℝ≥0∞) *
            ((2 ^ 141 : Nat) : ℝ≥0∞)⁻¹ := mul_comm _ _
    _ ≤ ((4 * q : Nat) : ℝ≥0∞) *
        ((2 ^ 141 : Nat) : ℝ≥0∞)⁻¹ := by
      have hcoeff : ((2 * q + 1 : Nat) : ℝ≥0∞) ≤ (4 * q : Nat) := by
        exact_mod_cast (show 2 * q + 1 ≤ 4 * q by omega)
      exact mul_le_mul_left hcoeff ((2 ^ 141 : Nat) : ℝ≥0∞)⁻¹
    _ = (q : ℝ≥0∞) * ((2 ^ 139 : Nat) : ℝ≥0∞)⁻¹ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
      norm_num
      ring

theorem probEvent_sampled_cleanMessage_le
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 125) :
    Pr[SampledViewedEvent cleanMessageEvent | sampledViewedGame adversary] ≤
      (q : ℝ≥0∞) * ((2 ^ 139 : Nat) : ℝ≥0∞)⁻¹ := by
  rw [probEvent_sampledViewedGame_eq_weighted]
  calc
    (∑' secrets : SampledSecrets, Pr[= secrets | sampleSecrets] *
        Pr[cleanMessageEvent secrets.parameter secrets.otsSecret secrets.ftsSecret |
          gameAfterSecretsWithViewTrace adversary secrets.parameter secrets.otsSecret
            secrets.ftsSecret]) ≤
        ∑' secrets : SampledSecrets, Pr[= secrets | sampleSecrets] *
          ((q : ℝ≥0∞) * ((2 ^ 139 : Nat) : ℝ≥0∞)⁻¹) := by
      apply ENNReal.tsum_le_tsum
      intro secrets
      by_cases hsecrets : secrets ∈ support sampleSecrets
      · obtain ⟨hparameter, hots, hfts⟩ := secrets.support_components hsecrets
        have hrisk :
            Pr[cleanMessageEvent secrets.parameter secrets.otsSecret secrets.ftsSecret |
                gameAfterSecretsWithViewTrace adversary secrets.parameter secrets.otsSecret
                  secrets.ftsSecret] ≤
              (q : ℝ≥0∞) * ((2 ^ 139 : Nat) : ℝ≥0∞)⁻¹ := by
          apply le_trans (probEvent_mono fun _ _ event => event.2)
          exact probEvent_gameAfterSecretsWithViewTrace_messageCollision_le_inv adversary q
            hqPos hq hqMax secrets.parameter hparameter secrets.otsSecret hots
              secrets.ftsSecret hfts
        calc
          Pr[= secrets | sampleSecrets] *
              Pr[cleanMessageEvent secrets.parameter secrets.otsSecret secrets.ftsSecret |
                gameAfterSecretsWithViewTrace adversary secrets.parameter secrets.otsSecret
                  secrets.ftsSecret] =
              Pr[cleanMessageEvent secrets.parameter secrets.otsSecret secrets.ftsSecret |
                gameAfterSecretsWithViewTrace adversary secrets.parameter secrets.otsSecret
                  secrets.ftsSecret] * Pr[= secrets | sampleSecrets] := mul_comm _ _
          _ ≤ ((q : ℝ≥0∞) * ((2 ^ 139 : Nat) : ℝ≥0∞)⁻¹) *
              Pr[= secrets | sampleSecrets] :=
            mul_le_mul_left hrisk _
          _ = Pr[= secrets | sampleSecrets] *
              ((q : ℝ≥0∞) * ((2 ^ 139 : Nat) : ℝ≥0∞)⁻¹) := mul_comm _ _
      · rw [probOutput_eq_zero_of_not_mem_support hsecrets, zero_mul, zero_mul]
    _ = (∑' secrets : SampledSecrets, Pr[= secrets | sampleSecrets]) *
        ((q : ℝ≥0∞) * ((2 ^ 139 : Nat) : ℝ≥0∞)⁻¹) := by
      rw [ENNReal.tsum_mul_right]
    _ ≤ 1 * ((q : ℝ≥0∞) * ((2 ^ 139 : Nat) : ℝ≥0∞)⁻¹) :=
      mul_le_mul_left tsum_probOutput_le_one _
    _ = (q : ℝ≥0∞) * ((2 ^ 139 : Nat) : ℝ≥0∞)⁻¹ := one_mul _

end SphincsSecurity.Concrete.Range125

import SphincsSecurity.Proof.FewTimeTargetView

/-! A valid counter for every honest layer rules out failure after the signer has selected its message digest. The bounded search covers the entire counter type. -/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

theorem otsSignFrom_ne_none_of_valid_counter (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (secret : ChainIndex → Digest) (message : Digest) (attempts start : Nat)
    (counter : Counter)
    (hlower : start ≤ counter.toNat) (hupper : counter.toNat < start + attempts)
    (hvalid : evalWithAnswerFn f (encode parameter lay tree leaf message counter) ≠ none) :
    evalWithAnswerFn f (otsSignFrom parameter lay tree leaf secret message attempts start) ≠ none := by
  induction attempts generalizing start with
  | zero => omega
  | succ attempts ih =>
      rw [otsSignFrom, evalWithAnswerFn_bind]
      cases hencode : evalWithAnswerFn f
          (encode parameter lay tree leaf message (BitVec.ofNat counterBits start)) with
      | some codeword =>
          simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, ne_eq, reduceCtorEq, not_false_eq_true]
      | none =>
          have hne : start ≠ counter.toNat := by
            intro heq
            apply hvalid
            simpa only [heq, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hencode
          exact ih (start + 1) (by omega) (by omega)

theorem otsSign_ne_none_of_valid_counter (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (secret : ChainIndex → Digest) (message : Digest) (counter : Counter)
    (hvalid : evalWithAnswerFn f (encode parameter lay tree leaf message counter) ≠ none) :
    evalWithAnswerFn f (otsSign parameter lay tree leaf secret message) ≠ none := by
  apply otsSignFrom_ne_none_of_valid_counter f parameter lay tree leaf secret message
    encodingAttemptLimit 0 counter (Nat.zero_le _) _ hvalid
  exact counter.isLt

theorem signLayer_ne_none_of_valid_counter (f : QueryImpl HashSpec Id)
    (secretKey : SecretKey) (index : Index) (lay : Layer) (counter : Counter)
    (hvalid : evalWithAnswerFn f
      (encode secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
        (evalWithAnswerFn f (layerMessage secretKey index lay)) counter) ≠ none) :
    evalWithAnswerFn f (signLayer secretKey index lay) ≠ none := by
  have hots := otsSign_ne_none_of_valid_counter f secretKey.parameter lay (treeIndexAt index lay)
    (leafIndexAt index lay) (secretKey.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay))
    (evalWithAnswerFn f (layerMessage secretKey index lay)) counter hvalid
  unfold signLayer
  simp only [evalWithAnswerFn_bind]
  cases hresult : evalWithAnswerFn f
      (otsSign secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
        (secretKey.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay))
        (evalWithAnswerFn f (layerMessage secretKey index lay))) with
  | none => exact (hots hresult).elim
  | some values => simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, ne_eq,
      reduceCtorEq, not_false_eq_true]

theorem signAfterDigest_ne_none_of_valid_counters (f : QueryImpl HashSpec Id)
    (secretKey : SecretKey) (randomness : Randomness) (index : Index)
    (leaves : DigestTree → FtsLeaf) (counters : Layer → Counter)
    (hvalid : ∀ lay, evalWithAnswerFn f
      (encode secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
        (evalWithAnswerFn f (layerMessage secretKey index lay)) (counters lay)) ≠ none) :
    evalWithAnswerFn f (signAfterDigest secretKey randomness index leaves) ≠ none := by
  classical
  have hlayers : ∀ lay, ∃ parts, evalWithAnswerFn f (signLayer secretKey index lay) = some parts := by
    intro lay
    exact Option.ne_none_iff_exists'.mp
      (signLayer_ne_none_of_valid_counter f secretKey index lay (counters lay) (hvalid lay))
  choose parts hparts using hlayers
  have heq : (fun lay => evalWithAnswerFn f (signLayer secretKey index lay)) =
      (fun lay => some (parts lay)) := funext hparts
  simp only [signAfterDigest, evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin, heq,
    traverseOption_some, evalWithAnswerFn_pure, ne_eq, reduceCtorEq, not_false_eq_true]

theorem FullyHonestOpening.signAfterDigest_ne_none
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {index : Index} {leaves : DigestTree → FtsLeaf} {signature : Signature}
    (hfull : FullyHonestOpening f cache secretKey index leaves signature)
    (randomness : Randomness) :
    evalWithAnswerFn f (signAfterDigest secretKey randomness index leaves) ≠ none := by
  apply signAfterDigest_ne_none_of_valid_counters f secretKey randomness index leaves signature.counter
  intro lay
  obtain ⟨codeword, hencode, _⟩ := (hfull.1 lay).1
  rw [hencode]
  simp

theorem signWithView_fresh_admissible_transition_finish
    (f : QueryImpl HashSpec Id) (secretKey : SecretKey) (message : Message)
    (initialCache finalCache : QueryCache HashSpec)
    (signature : Option Signature) (view : Option FewTimeView)
    (hmem : ((signature, view), finalCache) ∈ support
      ((simulateQ romImpl (signWithView secretKey message)).run initialCache))
    (hf : finalCache.AgreesWithFn f)
    (targetPayload : HashInput) (output : HashOutput) (index : Index)
    (leaves : DigestTree → FtsLeaf)
    (hbefore : initialCache
      (tweakableHashInput secretKey.parameter .message targetPayload) = none)
    (hafter : finalCache
      (tweakableHashInput secretKey.parameter .message targetPayload) = some output)
    (houtput : signAttemptResultOfOutput output = some (index, leaves)) :
    ∃ randomness, targetPayload = messageDigestPayload secretKey.root message randomness ∧
      evalWithAnswerFn f (signAfterDigest secretKey randomness index leaves) = signature := by
  rw [signWithView, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨loopResult, loopCache⟩, hloop, hfinish⟩ := hmem
  have hloopLe : loopCache ≤ finalCache := by
    cases loopResult with
    | none =>
        have heq : ((signature, view), finalCache) = ((none, none), loopCache) := by
          simpa only [simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff] using hfinish
        rw [show loopCache = finalCache from (congrArg Prod.snd heq).symm]
    | some selected =>
        rcases selected with ⟨randomness, selectedIndex, selectedLeaves⟩
        exact simulateQ_romImpl_cache_le
          (do
            let signature ← liftM
              (signAfterDigest secretKey randomness selectedIndex selectedLeaves)
            pure (signature, some (selectedFewTimeView selectedIndex selectedLeaves)))
          loopCache ((signature, view), finalCache) hfinish
  have hloopHit : loopCache
      (tweakableHashInput secretKey.parameter .message targetPayload) ≠ none := by
    intro hnone
    cases hloopResult : loopResult with
    | none =>
        have heq : ((signature, view), finalCache) = ((none, none), loopCache) := by
          simpa only [hloopResult, simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff] using hfinish
        have hcache : finalCache = loopCache := congrArg Prod.snd heq
        rw [hcache, hnone] at hafter
        simp at hafter
    | some selected =>
        rcases selected with ⟨randomness, selectedIndex, selectedLeaves⟩
        rw [hloopResult, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hfinish
        obtain ⟨⟨signatureResult, signatureCache⟩, hsignature, hpure⟩ := hfinish
        have hpureEq : ((signature, view), finalCache) =
            ((signatureResult, some (selectedFewTimeView selectedIndex selectedLeaves)),
              signatureCache) := by
          simpa only [simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff] using hpure
        have hsignature' : (signatureResult, signatureCache) ∈ support
            ((simulateQ (randomOracle : QueryImpl HashSpec _)
              (signAfterDigest secretKey randomness selectedIndex selectedLeaves)).run
                loopCache) := by
          simpa only [simulateQ_romImpl_liftM] using hsignature
        have hnone' := signAfterDigest_cache_message_none secretKey randomness
          selectedIndex selectedLeaves loopCache signatureCache signatureResult hsignature'
          targetPayload hnone
        have hcache : finalCache = signatureCache := congrArg Prod.snd hpureEq
        rw [hcache, hnone'] at hafter
        simp at hafter
  obtain ⟨loopOutput, hloopOutput⟩ := Option.ne_none_iff_exists'.mp hloopHit
  have hloopOutputEq : loopOutput = output := by
    have := hloopLe hloopOutput
    rw [hafter] at this
    exact Option.some.inj this.symm
  have hloopOutput' : loopCache
      (tweakableHashInput secretKey.parameter .message targetPayload) = some output := by
    rw [← hloopOutputEq]
    exact hloopOutput
  obtain ⟨_, randomness, _, hpayload, hloopResult⟩ :=
    signDigestLoop_successful_source_is_selected digestAttemptLimit secretKey message
      initialCache loopCache loopResult hloop targetPayload output index leaves
      hbefore hloopOutput' houtput
  rw [hloopResult, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hfinish
  obtain ⟨⟨signatureResult, signatureCache⟩, hsignature, hpure⟩ := hfinish
  have hpureEq : ((signature, view), finalCache) =
      ((signatureResult, some (selectedFewTimeView index leaves)), signatureCache) := by
    simpa only [simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] using hpure
  have hsignature' : (signatureResult, signatureCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (signAfterDigest secretKey randomness index leaves)).run loopCache) := by
    simpa only [simulateQ_romImpl_liftM] using hsignature
  have hcacheEq : finalCache = signatureCache := congrArg Prod.snd hpureEq
  have hresultEq : signature = signatureResult := congrArg (fun result => result.1.1) hpureEq
  have heval := (replay_of_mem_support
    (signAfterDigest secretKey randomness index leaves) loopCache signatureResult signatureCache
      hsignature' f (by rwa [← hcacheEq])).2.1
  exact ⟨randomness, hpayload, heval.trans hresultEq.symm⟩

theorem ProperFewTimeLeak.no_signer_target_of_fullyHonest
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec}
    {secretKey : SecretKey} {signingLog : QueryLog SigningSpec}
    {index : Index} {leaves : DigestTree → FtsLeaf} {forged : Signature}
    (hproper : ProperFewTimeLeak f cache secretKey signingLog index leaves)
    (hfull : FullyHonestOpening f cache secretKey index leaves forged)
    (state : ViewedFullTraceState)
    (hlog : state.trace.signing.toSigningLog = signingLog)
    (hvalidViews : state.ValidViews secretKey)
    (hconsistent : state.trace.Consistent)
    (hvalidRuns : state.trace.signing.ValidRuns secretKey)
    (hcaches : state.trace.signing.CachesLe cache) (hf : cache.AgreesWithFn f)
    (position : Fin state.trace.intervals.length)
    (request : SignRequest) (signature : Option Signature)
    (initialCache finalCache : QueryCache HashSpec)
    (hinterval : state.trace.intervals.get position =
      ⟨.inr request, signature, initialCache, finalCache⟩)
    (targetPayload : HashInput) (output : HashOutput)
    (hbefore : initialCache
      (tweakableHashInput secretKey.parameter .message targetPayload) = none)
    (hafter : finalCache
      (tweakableHashInput secretKey.parameter .message targetPayload) = some output)
    (houtput : signAttemptResultOfOutput output = some (index, leaves)) : False := by
  have hnone := hproper.signer_target_signature_eq_none state hlog hvalidViews hconsistent
    hvalidRuns hcaches hf position request signature initialCache finalCache hinterval
      targetPayload output hbefore hafter houtput
  obtain ⟨signingPosition, viewPosition, _, _, hentry, hviewRun⟩ :=
    ViewedFullTraceState.ValidViews.signer_interval hvalidViews hconsistent position
      request signature initialCache finalCache hinterval
  have hmem : state.trace.signing.get signingPosition ∈ state.trace.signing :=
    List.get_mem state.trace.signing signingPosition
  have hfinalLe : finalCache ≤ cache := by
    have h := (hcaches _ hmem).2
    simpa only [hentry] using h
  obtain ⟨randomness, _, heval⟩ := signWithView_fresh_admissible_transition_finish f secretKey
    request initialCache finalCache signature (state.views.get viewPosition) hviewRun
    (fun _ _ hcached => hf (hfinalLe hcached)) targetPayload output index leaves hbefore hafter houtput
  exact hfull.signAfterDigest_ne_none randomness (heval.trans hnone)

end SphincsSecurity.Concrete

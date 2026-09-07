import SphincsSecurity.Proof.SignerAdmissibleMessage

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

theorem signDigestLoop_selected_cached_output (attempts : Nat) (key : SecretKey) (message : Message)
    (before after : QueryCache HashSpec) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (hloop : (some (randomness, index, leaves), after) ∈ support ((simulateQ romImpl (signDigestLoop attempts key message)).run before)) :
    ∃ output, after (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) = some output ∧
      Admissible (truncateMessageDigest output) ∧ hashOutputFewTimeView output = selectedFewTimeView index leaves := by
  have hreplay := replayRom_of_mem_support (signDigestLoop attempts key message) before
    (some (randomness, index, leaves)) after hloop (fromCache after) (agreesWithFn_fromCache after)
  have hgood := successfulDigestLoop_of_mem_support (fromCache after) key message attempts randomness index leaves
    before after after hreplay le_rfl (agreesWithFn_fromCache after)
  obtain ⟨_, digest, heval, hadmissible, hindex, hleaves, hcached⟩ := hgood.extract
  obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp (CachedRun.messageDigest_cached hcached)
  have hdigest : digest = truncateMessageDigest output := by
    rw [← heval]
    change truncateMessageDigest (fromCache after (tweakableHashInput key.parameter .message
      (messageDigestPayload key.root message randomness))) = truncateMessageDigest output
    rw [agreesWithFn_fromCache after houtput]
  refine ⟨output, houtput, hdigest ▸ hadmissible, ?_⟩
  simp only [hashOutputFewTimeView, selectedFewTimeView, ← hdigest, hindex, hleaves]

theorem signAfterDigest_message_cache_eq (key : SecretKey) (randomness : Randomness) (index : Index)
    (leaves : DigestTree → FtsLeaf) (before after : QueryCache HashSpec) (signature : Option Signature)
    (hfinish : (signature, after) ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _)
      (signAfterDigest key randomness index leaves)).run before)) (payload : HashInput) :
    after (tweakableHashInput key.parameter .message payload) = before (tweakableHashInput key.parameter .message payload) := by
  cases hbefore : before (tweakableHashInput key.parameter .message payload) with
  | none => exact signAfterDigest_cache_message_none key randomness index leaves before after signature hfinish payload hbefore
  | some output =>
      have hcache : before ≤ after :=
        (replay_of_mem_support (signAfterDigest key randomness index leaves) before signature after hfinish
          (fromCache after) (agreesWithFn_fromCache after)).1
      exact hcache hbefore

theorem signWithView_support_decomposition (key : SecretKey) (message : Message) (before after : QueryCache HashSpec)
    (signature : Option Signature) (view : Option FewTimeView)
    (hresult : ((signature, view), after) ∈ support ((simulateQ romImpl (signWithView key message)).run before)) :
    (signature = none ∧ view = none ∧ (none, after) ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before)) ∨
      ∃ randomness index leaves loopCache,
        (some (randomness, index, leaves), loopCache) ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before) ∧
        (signature, after) ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _) (signAfterDigest key randomness index leaves)).run loopCache) ∧
        view = some (selectedFewTimeView index leaves) := by
  rw [signWithView, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hresult
  obtain ⟨⟨loopResult, loopCache⟩, hloop, hfinish⟩ := hresult
  cases loopResult with
  | none =>
      have heq : ((signature, view), after) = ((none, none), loopCache) := by
        simpa only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] using hfinish
      refine Or.inl ⟨congrArg (fun result => result.1.1) heq, congrArg (fun result => result.1.2) heq, ?_⟩
      have hcache : after = loopCache := congrArg Prod.snd heq
      rwa [hcache]
  | some selected =>
      obtain ⟨randomness, index, leaves⟩ := selected
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hfinish
      obtain ⟨⟨signatureResult, signatureCache⟩, hsignature, hpure⟩ := hfinish
      have heq : ((signature, view), after) = ((signatureResult, some (selectedFewTimeView index leaves)), signatureCache) := by
        simpa only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] using hpure
      refine Or.inr ⟨randomness, index, leaves, loopCache, hloop, ?_, congrArg (fun result => result.1.2) heq⟩
      have hresponse : signature = signatureResult := congrArg (fun result => result.1.1) heq
      have hcache : after = signatureCache := congrArg Prod.snd heq
      rw [hresponse, hcache]
      simpa only [simulateQ_romImpl_liftM] using hsignature

theorem signWithView_new_admissible_selected (key : SecretKey) (message : Message)
    (before after : QueryCache HashSpec) (signature : Option Signature) (view : Option FewTimeView)
    (hresult : ((signature, view), after) ∈ support ((simulateQ romImpl (signWithView key message)).run before))
    (payload : HashInput) (output : HashOutput)
    (hbefore : before (tweakableHashInput key.parameter .message payload) = none)
    (hafter : after (tweakableHashInput key.parameter .message payload) = some output)
    (hadmissible : Admissible (truncateMessageDigest output)) :
    ∃ randomness index leaves loopCache,
      (some (randomness, index, leaves), loopCache) ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before) ∧
      payload = messageDigestPayload key.root message randomness ∧
      view = some (hashOutputFewTimeView output) ∧ hashOutputFewTimeView output = selectedFewTimeView index leaves := by
  rcases signWithView_support_decomposition key message before after signature view hresult with hnone | hsome
  · obtain ⟨randomness, index, leaves, hselected, _⟩ := signDigestLoop_new_admissible_selected digestAttemptLimit key message
      before after none hnone.2.2 payload output hbefore hafter hadmissible
    contradiction
  · obtain ⟨randomness, index, leaves, loopCache, hloop, hfinish, hview⟩ := hsome
    rw [signAfterDigest_message_cache_eq key randomness index leaves loopCache after signature hfinish payload] at hafter
    obtain ⟨selected, selectedIndex, selectedLeaves, hselected, hpayload⟩ := signDigestLoop_new_admissible_selected digestAttemptLimit key message
      before loopCache (some (randomness, index, leaves)) hloop payload output hbefore hafter hadmissible
    have hrandomness : randomness = selected := congrArg Prod.fst (Option.some.inj hselected)
    have hpayload' : payload = messageDigestPayload key.root message randomness := hpayload.trans (congrArg _ hrandomness.symm)
    obtain ⟨selectedOutput, houtput, _, houtputView⟩ := signDigestLoop_selected_cached_output digestAttemptLimit key message before loopCache randomness index leaves hloop
    have hout : output = selectedOutput := Option.some.inj ((hpayload' ▸ hafter).symm.trans houtput)
    refine ⟨randomness, index, leaves, loopCache, hloop, hpayload', ?_, hout ▸ houtputView⟩
    rw [hout, houtputView]
    exact hview

end SphincsSecurity.Concrete

import SphincsSecurity.Proof.FewTimeTargetSource
import SphincsSecurity.Proof.FewTimePrehit

/-!
# Counting fresh target-view candidates

A direct hash interval contributes its queried input. A signer interval may contribute any
message-digest input it inserted, including the selected digest of a signing invocation whose later
signature construction failed. If that input was fresh, distinct candidate intervals embed into
distinct entries of the final random-oracle cache.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

def TargetCandidateInput (secretKey : SecretKey)
    (entry : AdversaryCacheEntry) (input : HashInput) : Prop :=
  (entry.input = .inl (.inr input)) ∨
    ∃ request randomness,
      entry.input = .inr request ∧
        input = tweakableHashInput secretKey.parameter .message
          (messageDigestPayload secretKey.root request randomness)

def FreshTargetCandidate (secretKey : SecretKey)
    (entry : AdversaryCacheEntry) : Prop :=
  ∃ input output,
    TargetCandidateInput secretKey entry input
      ∧ entry.initialCache input = none
      ∧ entry.finalCache input = some output

noncomputable instance (secretKey : SecretKey) :
    DecidablePred (FreshTargetCandidate secretKey) :=
  fun entry => Classical.propDecidable (FreshTargetCandidate secretKey entry)

theorem freshTargetCandidate_of_message_transition
    (secretKey : SecretKey) (entry : AdversaryCacheEntry) (targetPayload : HashInput)
    (hvalid : (entry.output, entry.finalCache) ∈ support
      ((unloggedMappedAdversaryImpl secretKey entry.input).run entry.initialCache))
    (hbefore : entry.initialCache
      (tweakableHashInput secretKey.parameter .message targetPayload) = none)
    (hafter : entry.finalCache
      (tweakableHashInput secretKey.parameter .message targetPayload) ≠ none)
    (hkind : entry.input = .inl (.inr
        (tweakableHashInput secretKey.parameter .message targetPayload)) ∨
      ∃ request, entry.input = .inr request) :
    FreshTargetCandidate secretKey entry := by
  rcases entry with ⟨input, result, initialCache, finalCache⟩
  rcases input with worldInput | request
  · rcases worldInput with uniformInput | hashInput
    · rcases hkind with hfalse | ⟨_, hfalse⟩ <;> simp at hfalse
    · obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hafter
      refine ⟨tweakableHashInput secretKey.parameter .message targetPayload, output, ?_,
        hbefore, houtput⟩
      rcases hkind with hdirect | ⟨_, hfalse⟩
      · exact Or.inl hdirect
      · simp at hfalse
  · obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hafter
    change Option Signature at result
    change (result, finalCache) ∈ support
      ((simulateQ romImpl (scheme.sign secretKey request)).run initialCache) at hvalid
    refine ⟨tweakableHashInput secretKey.parameter .message targetPayload, output, ?_,
      hbefore, houtput⟩
    rcases hkind with hfalse | ⟨sourceRequest, hrequest⟩
    · simp at hfalse
    · have hrequestEq : request = sourceRequest := by injection hrequest
      subst sourceRequest
      have hsign : (result, finalCache) ∈ support
          ((simulateQ romImpl (scheme.sign secretKey request)).run initialCache) := by
        exact hvalid
      rw [show scheme.sign secretKey request = sign secretKey request from rfl] at hsign
      obtain ⟨_, randomness, _, _, hpayload⟩ :=
        sign_message_source secretKey request initialCache finalCache result hsign
          targetPayload hbefore hafter
      exact Or.inr ⟨request, randomness, rfl, by rw [hpayload]⟩

set_option linter.constructorNameAsVariable false in
theorem signWithView_fresh_admissible_transition_view
    (secretKey : SecretKey) (message : Message)
    (initialCache finalCache : QueryCache HashSpec)
    (signature : Option Signature) (view : Option FewTimeView)
    (hmem : ((signature, view), finalCache) ∈ support
      ((simulateQ romImpl (signWithView secretKey message)).run initialCache))
    (targetPayload : HashInput) (output : HashOutput) (index : Index)
    (leaves : DigestTree → FtsLeaf)
    (hbefore : initialCache
      (tweakableHashInput secretKey.parameter .message targetPayload) = none)
    (hafter : finalCache
      (tweakableHashInput secretKey.parameter .message targetPayload) = some output)
    (houtput : signAttemptResultOfOutput output = some (index, leaves)) :
    ∃ randomness,
      targetPayload = messageDigestPayload secretKey.root message randomness
        ∧ view = some (hashOutputFewTimeView output)
        ∧ ∀ signed, signature = some signed → randomness = signed.randomness := by
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
  have hview : view = some (selectedFewTimeView index leaves) :=
    congrArg (fun result => result.1.2) hpureEq
  have houtputView := signAttemptResultOfOutput_view output index leaves houtput
  refine ⟨randomness, hpayload, hview.trans (by
    simpa only [selectedFewTimeView] using congrArg some houtputView), ?_⟩
  intro signed hsigned
  have hresult : signatureResult = some signed := by
    have := congrArg (fun result => result.1.1) hpureEq
    rw [hsigned] at this
    exact this.symm
  have hsignature' : (some signed, signatureCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (signAfterDigest secretKey randomness index leaves)).run loopCache) := by
    rw [hresult] at hsignature
    simpa only [simulateQ_romImpl_liftM] using hsignature
  exact (signAfterDigest_support_some_randomness secretKey randomness index leaves
    loopCache signatureCache signed hsignature').symm

theorem signingCacheEntry_validView_fresh_admissible_transition_view
    {secretKey : SecretKey} {entry : SigningCacheEntry} {view : Option FewTimeView}
    (hvalid : SigningCacheEntry.ValidView secretKey entry view)
    (targetPayload : HashInput) (output : HashOutput) (index : Index)
    (leaves : DigestTree → FtsLeaf)
    (hbefore : entry.initialCache
      (tweakableHashInput secretKey.parameter .message targetPayload) = none)
    (hafter : entry.finalCache
      (tweakableHashInput secretKey.parameter .message targetPayload) = some output)
    (houtput : signAttemptResultOfOutput output = some (index, leaves)) :
    ∃ randomness,
      targetPayload = messageDigestPayload secretKey.root entry.request randomness
        ∧ view = some (hashOutputFewTimeView output)
        ∧ ∀ signed, entry.signature = some signed → randomness = signed.randomness :=
  signWithView_fresh_admissible_transition_view secretKey entry.request
    entry.initialCache entry.finalCache entry.signature view hvalid targetPayload output
    index leaves hbefore hafter houtput

noncomputable def freshTargetCandidatePositions
    (secretKey : SecretKey) (trace : FullAdversaryTrace) :
    Finset (Fin trace.intervals.length) :=
  Finset.univ.filter fun position =>
    FreshTargetCandidate secretKey (trace.intervals.get position)

theorem freshTargetCandidatePositions_card_le_enncard
    (secretKey : SecretKey) (trace : FullAdversaryTrace)
    (finalCache : QueryCache HashSpec)
    (hintervals : trace.IntervalsLe finalCache)
    (hchronological : FullAdversaryTrace.Chronological trace.intervals) :
    ((freshTargetCandidatePositions secretKey trace).card : ℝ≥0∞) ≤
      QueryCache.enncard finalCache := by
  classical
  let candidates := freshTargetCandidatePositions secretKey trace
  let candidateInput : ↑candidates → HashInput := fun candidate =>
    Classical.choose ((Finset.mem_filter.mp candidate.2).2)
  let candidateOutput : ∀ candidate : ↑candidates, HashOutput := fun candidate =>
    Classical.choose (Classical.choose_spec ((Finset.mem_filter.mp candidate.2).2))
  have candidateSpec : ∀ candidate : ↑candidates,
      TargetCandidateInput secretKey (trace.intervals.get candidate.1)
          (candidateInput candidate)
        ∧ (trace.intervals.get candidate.1).initialCache (candidateInput candidate) = none
        ∧ (trace.intervals.get candidate.1).finalCache (candidateInput candidate) =
          some (candidateOutput candidate) := by
    intro candidate
    exact Classical.choose_spec
      (Classical.choose_spec ((Finset.mem_filter.mp candidate.2).2))
  let cacheEmbedding : ↑candidates ↪ finalCache.toSet :=
    ⟨fun candidate => ⟨⟨candidateInput candidate, candidateOutput candidate⟩,
        (hintervals (trace.intervals.get candidate.1)
          (List.get_mem trace.intervals candidate.1)).2 (candidateSpec candidate).2.2⟩,
      by
        intro left right heq
        have hinput : candidateInput left = candidateInput right :=
          congrArg (fun entry : finalCache.toSet => entry.1.1) heq
        apply Subtype.ext
        by_contra hposition
        rcases lt_or_gt_of_ne hposition with hlt | hlt
        · have hle := hchronological.get_finalCache_le_initialCache left.1 right.1 hlt
          have hcached := hle (candidateSpec left).2.2
          rw [hinput, (candidateSpec right).2.1] at hcached
          simp at hcached
        · have hle := hchronological.get_finalCache_le_initialCache right.1 left.1 hlt
          have hcached := hle (candidateSpec right).2.2
          rw [← hinput, (candidateSpec left).2.1] at hcached
          simp at hcached⟩
  have hencard := cacheEmbedding.encard_le
  simpa only [candidates, QueryCache.enncard, Set.encard_coe_eq_coe_finsetCard,
    ENat.toENNReal_coe] using ENat.toENNReal_mono hencard

theorem gameAfterSecretsWithViewTrace_freshTargetCandidatePositions_card_le
    (adversary : Adversary) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState)
    (hresult : result ∈ support
      (gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret)) :
    ((freshTargetCandidatePositions
      ⟨parameter, result.1.1, otsSecret, ftsSecret⟩ result.2.trace).card : ℝ≥0∞) ≤ q := by
  have hbase : (result.1, result.2.base) ∈ support
      (gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret) := by
    rw [← gameAfterSecretsWithViewTrace_projection adversary parameter otsSecret ftsSecret,
      support_map]
    exact ⟨result, hresult, rfl⟩
  have hinvariants := gameAfterSecretsWithFullTrace_support_interval_invariants adversary
    parameter otsSecret ftsSecret (result.1, result.2.base) hbase
  calc
    _ ≤ QueryCache.enncard result.2.cache :=
      freshTargetCandidatePositions_card_le_enncard
        ⟨parameter, result.1.1, otsSecret, ftsSecret⟩ result.2.trace result.2.cache
        hinvariants.2.1 hinvariants.2.2
    _ ≤ q := gameAfterSecretsWithFullTrace_support_enncard_le adversary q hq
      parameter hparameter otsSecret hots ftsSecret hfts (result.1, result.2.base) hbase

end SphincsSecurity.Concrete

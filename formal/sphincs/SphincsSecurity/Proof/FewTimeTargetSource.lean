import SphincsSecurity.Proof.FewTimeViewTrace
import Batteries.Data.Fin.Coding

/-!
# Cache origin of the verifier target view

The message-digest answer used by final verification is either fresh at verification or was first
inserted by one of the retained outer adversary intervals.  In the latter case the interval is a
direct hash query at that input or a signer invocation.
-/

namespace SphincsSecurity

open OracleComp OracleSpec

namespace Concrete

def isTargetCandidateInterval (entry : AdversaryCacheEntry) : Prop :=
  match entry.input with
  | .inl (.inr _) => True
  | .inr _ => True
  | .inl (.inl _) => False

instance : DecidablePred isTargetCandidateInterval := fun entry => by
  rcases entry with ⟨input, output, initialCache, finalCache⟩
  rcases input with worldInput | request
  · rcases worldInput with uniformInput | hashInput
    · exact isFalse id
    · exact isTrue trivial
  · exact isTrue trivial

abbrev TargetCandidateIntervals (trace : FullAdversaryTrace) :=
  {position : Fin trace.intervals.length //
    isTargetCandidateInterval (trace.intervals.get position)}

def targetCandidateIntervalCount (trace : FullAdversaryTrace) : Nat :=
  Fin.countP fun position : Fin trace.intervals.length =>
    decide (isTargetCandidateInterval (trace.intervals.get position))

noncomputable def targetCandidateIntervalOrdinal (trace : FullAdversaryTrace)
    (position : Fin trace.intervals.length)
    (hcandidate : isTargetCandidateInterval (trace.intervals.get position)) :
    Fin (targetCandidateIntervalCount trace) :=
  Fin.encodeSubtype (fun candidate =>
    isTargetCandidateInterval (trace.intervals.get candidate)) ⟨position, hcandidate⟩

def TargetCandidateAt (trace : FullAdversaryTrace) (input : HashInput)
    (adversaryCache : QueryCache HashSpec)
    (candidate : Fin (targetCandidateIntervalCount trace + 1)) : Prop :=
  (∃ (source : Fin trace.intervals.length)
      (hcandidate : isTargetCandidateInterval (trace.intervals.get source)),
      candidate.val = (targetCandidateIntervalOrdinal trace source hcandidate).val
        ∧ (trace.intervals.get source).initialCache input = none
        ∧ (trace.intervals.get source).finalCache input ≠ none)
    ∨ (candidate.val = targetCandidateIntervalCount trace ∧
      adversaryCache input = none)

theorem exists_targetCandidateAt_of_source_kind
    (trace : FullAdversaryTrace) (input : HashInput)
    (adversaryCache : QueryCache HashSpec)
    (horigin : adversaryCache input = none ∨
      ∃ source : Fin trace.intervals.length,
        (trace.intervals.get source).initialCache input = none
          ∧ (trace.intervals.get source).finalCache input ≠ none
          ∧ ((trace.intervals.get source).input = .inl (.inr input)
            ∨ ∃ request, (trace.intervals.get source).input = .inr request)) :
    ∃ candidate : Fin (targetCandidateIntervalCount trace + 1),
      TargetCandidateAt trace input adversaryCache candidate := by
  rcases horigin with hverifier | ⟨source, hinitial, hfinal, hkind⟩
  · exact ⟨⟨targetCandidateIntervalCount trace, Nat.lt_succ_self _⟩,
      Or.inr ⟨rfl, hverifier⟩⟩
  · have hcandidate : isTargetCandidateInterval (trace.intervals.get source) := by
      rcases hkind with hdirect | ⟨request, hsigner⟩
      · rw [isTargetCandidateInterval, hdirect]
        trivial
      · rw [isTargetCandidateInterval, hsigner]
        trivial
    let ordinal := targetCandidateIntervalOrdinal trace source hcandidate
    exact ⟨⟨ordinal.val, Nat.lt_succ_of_lt ordinal.isLt⟩,
      Or.inl ⟨source, hcandidate, rfl, hinitial, hfinal⟩⟩

theorem gameAfterSecretsWithViewTrace_target_source_kind
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState)
    (hmem : result ∈ support
      (gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret)) :
    let input := tweakableHashInput parameter .message
      (messageDigestPayload result.1.1 result.1.2.1.message
        result.1.2.1.signature.randomness)
    ∃ (rootCache adversaryCache digestCache : QueryCache HashSpec) (output : HashOutput),
      (∀ payload, rootCache (tweakableHashInput parameter .message payload) = none)
        ∧ FullAdversaryTrace.CacheChain rootCache result.2.trace.intervals adversaryCache
        ∧ (output, digestCache) ∈ support
          ((simulateQ (randomOracle : QueryImpl HashSpec _) (oracleHash input)).run adversaryCache)
        ∧ digestCache ≤ result.2.cache
        ∧ result.2.targetView = some (hashOutputFewTimeView output)
        ∧ (adversaryCache input = none ∨
          ∃ source : Fin result.2.trace.intervals.length,
            (result.2.trace.intervals.get source).initialCache input = none
              ∧ (result.2.trace.intervals.get source).finalCache input ≠ none
              ∧ ((result.2.trace.intervals.get source).input = .inl (.inr input)
                ∨ ∃ request, (result.2.trace.intervals.get source).input = .inr request))
        ∧ ∃ candidate : Fin (targetCandidateIntervalCount result.2.trace + 1),
          TargetCandidateAt result.2.trace input adversaryCache candidate := by
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
  let input := tweakableHashInput parameter .message
    (messageDigestPayload root forgery.message forgery.signature.randomness)
  have hrootRun : (root, rootCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅) := by
    simpa only [simulateQ_romImpl_liftM] using hroot
  have hrootNone : ∀ payload,
      rootCache (tweakableHashInput parameter .message payload) = none :=
    fun payload => treeRoot_cache_message_none parameter topLayer rootTree
      (otsSecret topLayer rootTree) root rootCache hrootRun payload
  let initialState : ViewedFullTraceState :=
    ⟨rootCache, ⟨[], [], []⟩, [], none⟩
  have hbase : (forgery, state.base) ∈ support
      ((simulateQ (fullTracedMappedAdversaryImpl secretKey)
        (adversary.main publicKey)).run initialState.base) := by
    rw [← viewedFullTracedMappedAdversaryImpl_projection secretKey
      (adversary.main publicKey) initialState, support_map]
    exact ⟨(forgery, state), hadversary, rfl⟩
  have hchain : FullAdversaryTrace.CacheChain rootCache state.trace.intervals state.cache :=
    fullTracedMappedAdversaryImpl_cacheChain secretKey (adversary.main publicKey)
      rootCache rootCache ⟨[], [], []⟩ (forgery, state.base) (by rfl) hbase
  have hvalid : state.trace.ValidIntervals secretKey :=
    fullTracedMappedAdversaryImpl_validIntervals secretKey (adversary.main publicKey)
      rootCache ⟨[], [], []⟩ (forgery, state.base)
      (by simp [FullAdversaryTrace.ValidIntervals]) hbase
  have hverify' : ((verified, targetView), finalCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (verifyWithView publicKey forgery.message forgery.signature)).run state.cache) := by
    simpa only [simulateQ_romImpl_liftM] using hverify
  obtain ⟨output, digestCache, houtput, hdigestLe, htarget⟩ :=
    verifyWithView_support_view publicKey forgery.message forgery.signature
      state.cache finalCache verified targetView hverify'
  refine ⟨rootCache, state.cache, digestCache, output, hrootNone, hchain,
    ?_, hdigestLe, congrArg some htarget, ?_⟩
  · simpa only [input, publicKey] using houtput
  · have horigin : state.cache input = none ∨
        ∃ source : Fin state.trace.intervals.length,
          (state.trace.intervals.get source).initialCache input = none
            ∧ (state.trace.intervals.get source).finalCache input ≠ none
            ∧ ((state.trace.intervals.get source).input = .inl (.inr input)
              ∨ ∃ request, (state.trace.intervals.get source).input = .inr request) := by
      by_cases hcached : state.cache input = none
      · exact Or.inl hcached
      · right
        obtain ⟨source, hsourceInitial, hsourceFinal⟩ :=
          hchain.transition_to_finish input (hrootNone _) hcached
        exact ⟨source, hsourceInitial, hsourceFinal,
          FullAdversaryTrace.transition_source_kind hvalid
            (state.trace.intervals.get source) (List.get_mem _ source) input
            hsourceInitial hsourceFinal⟩
    exact ⟨horigin,
      exists_targetCandidateAt_of_source_kind state.trace input state.cache horigin⟩

end Concrete

end SphincsSecurity

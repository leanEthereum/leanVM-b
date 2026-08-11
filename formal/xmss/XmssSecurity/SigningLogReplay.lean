import XmssSecurity.ConcreteExecution

open OracleComp OracleSpec ENNReal
open scoped BigOperators

namespace XmssSecurity

noncomputable def mappedAdversaryImpl (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (WriterT (QueryLog SigningSpec) (StateT (QueryCache HashSpec) ProbComp)) :=
  let forward : QueryImpl OracleWorld
      (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
    (HasQuery.toQueryImpl (spec := OracleWorld) (m := OracleComp OracleWorld)).liftTarget _
  xmssRomImpl.writerTMapBase (forward + signingOracle Concrete.scheme publicKey secretKey)

theorem mappedAdversary_cache_le (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec)
    (result : (α × QueryLog SigningSpec) × QueryCache HashSpec)
    (hmem : result ∈ support
      (((simulateQ (mappedAdversaryImpl publicKey secretKey) computation).run).run initialCache)) :
    initialCache ≤ result.2 := by
  let forward : QueryImpl OracleWorld
      (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
    (HasQuery.toQueryImpl (spec := OracleWorld) (m := OracleComp OracleWorld)).liftTarget _
  apply xmssRom_cache_le
    ((simulateQ (forward + signingOracle Concrete.scheme publicKey secretKey) computation).run)
    initialCache result
  rw [QueryImpl.simulateQ_writerTMapBase_run]
  exact hmem

def SigningLogConsistent (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) : Prop :=
  ∀ request signature, SigningTranscript.Returned log request signature →
    ∃ encoding,
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash cache secretKey.parameter request.epoch
          (request.message, signature.randomness)) = some encoding ∧
      signature = Concrete.CacheReplay.signWithEncoding cache secretKey
        request.epoch signature.randomness encoding

theorem mappedAdversary_signingLog_consistent (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec)
    (result : (α × QueryLog SigningSpec) × QueryCache HashSpec)
    (hmem : result ∈ support
      (((simulateQ (mappedAdversaryImpl publicKey secretKey) computation).run).run initialCache))
    (largerCache : QueryCache HashSpec) (hle : result.2 ≤ largerCache) :
    SigningLogConsistent largerCache secretKey result.1.2 := by
  induction computation using OracleComp.inductionOn generalizing
      initialCache result with
  | pure value =>
      simp only [simulateQ_pure, WriterT.run_pure', StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at hmem
      subst result
      intro request signature hreturned
      obtain ⟨entry, hentry, _⟩ := hreturned
      simp at hentry
  | query_bind input next ih =>
      rw [simulateQ_bind] at hmem
      rw [WriterT.run_bind', StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨⟨output, queryLog⟩, middleCache⟩, hquery, hrestMapped⟩ := hmem
      rw [StateT.run_map, support_map] at hrestMapped
      obtain ⟨⟨⟨value, restLog⟩, finalCache⟩, hrest, heq⟩ := hrestMapped
      cases heq
      intro request signature hreturned
      obtain ⟨entry, hentry, hrequest, hsignature⟩ := hreturned
      change entry ∈ queryLog ++ restLog at hentry
      change finalCache ≤ largerCache at hle
      rw [List.mem_append] at hentry
      rcases hentry with hcurrent | hlater
      · cases input with
        | inl worldInput =>
            simp only [simulateQ_spec_query, mappedAdversaryImpl,
              QueryImpl.writerTMapBase, QueryImpl.add_apply_inl,
              QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply,
              WriterT.run_mk] at hquery
            erw [WriterT.run_liftM] at hquery
            rw [simulateQ_map, StateT.run_map, support_map] at hquery
            obtain ⟨⟨worldOutput, worldCache⟩, _hworld, heq⟩ := hquery
            cases heq
            simp at hcurrent
        | inr signingRequest =>
            simp only [simulateQ_spec_query, mappedAdversaryImpl,
              QueryImpl.writerTMapBase, QueryImpl.add_apply_inr,
              signingOracle] at hquery
            rw [WriterT.run_mk] at hquery
            erw [QueryImpl.run_withLogging_apply] at hquery
            erw [simulateQ_bind] at hquery
            rw [StateT.run_bind, mem_support_bind_iff] at hquery
            obtain ⟨⟨signOutput, signCache⟩, hsign, hpure⟩ := hquery
            cases hpure
            simp only [List.mem_singleton] at hcurrent
            cases hcurrent
            simp only at hrequest hsignature
            have hmiddleFinal : signCache ≤ finalCache :=
              mappedAdversary_cache_le publicKey secretKey (next signOutput)
                signCache ((value, restLog), finalCache) hrest
            rw [hrequest] at hsign
            rw [hsignature] at hsign
            change (some signature, signCache) ∈ support
              ((simulateQ xmssRomImpl
                (Concrete.sign publicKey secretKey request.epoch request.message)).run
                initialCache) at hsign
            apply concrete_sign_support_replay publicKey secretKey request
              initialCache signCache largerCache signature
            · exact hsign
            · exact hmiddleFinal.trans hle
      · apply ih output middleCache ((value, restLog), finalCache) hrest hle
        exact ⟨entry, hlater, hrequest, hsignature⟩

theorem detailed_execution_signingLog_consistent
    (adversary : Adversary Concrete.scheme)
    (execution : GameOutcome × QueryCache HashSpec)
    (hmem : execution ∈ support (detailedGameWithCache Concrete.scheme adversary)) :
    SigningLogConsistent execution.2 execution.1.secretKey execution.1.signingLog := by
  have hgame := hmem
  unfold detailedGameWithCache detailedGameCore at hgame
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hgame
  obtain ⟨⟨⟨publicKey, secretKey⟩, keyCache⟩, _hkeygen, hrest⟩ := hgame
  simp only at hrest
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨⟨⟨forgery, signingLog⟩, adversaryCache⟩, hadversary, hverifyRest⟩ := hrest
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hverifyRest
  obtain ⟨⟨verified, finalCache⟩, hverify, hfinal⟩ := hverifyRest
  simp only [simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hfinal
  subst execution
  simp only
  have hadversary' : ((forgery, signingLog), adversaryCache) ∈ support
      (((simulateQ (mappedAdversaryImpl publicKey secretKey)
        (adversary.main publicKey)).run).run keyCache) := by
    let forward : QueryImpl OracleWorld
        (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
      (HasQuery.toQueryImpl (spec := OracleWorld) (m := OracleComp OracleWorld)).liftTarget _
    rw [mappedAdversaryImpl]
    rw [← QueryImpl.simulateQ_writerTMapBase_run]
    exact hadversary
  have hcacheLe : adversaryCache ≤ finalCache :=
    xmssRom_cache_le _ adversaryCache (verified, finalCache) hverify
  exact mappedAdversary_signingLog_consistent publicKey secretKey
    (adversary.main publicKey) keyCache ((forgery, signingLog), adversaryCache)
    hadversary' finalCache hcacheLe

theorem detailed_execution_consistent
    (adversary : Adversary Concrete.scheme)
    (execution : GameOutcome × QueryCache HashSpec)
    (hmem : execution ∈ support (detailedGameWithCache Concrete.scheme adversary)) :
    ConcreteOutcomeConsistent execution.2 execution.1 :=
  detailed_execution_consistent_of_signing adversary execution hmem
    (detailed_execution_signingLog_consistent adversary execution hmem)

/-- Concrete winning executions are bounded by the sum of their 175 cache-level bad-event probabilities. -/
theorem forgeAdvantage_le_outcomeBadEvent_sum
    (adversary : Adversary Concrete.scheme) :
    forgeAdvantage Concrete.scheme adversary ≤
      ∑ event, Pr[fun execution : GameOutcome × QueryCache HashSpec =>
        OutcomeBadEventOccurs execution.2 execution.1 event |
        detailedGameWithCache Concrete.scheme adversary] := by
  rw [forgeAdvantage_eq_detailedGameWithCache]
  calc
    Pr[fun execution : GameOutcome × QueryCache HashSpec => execution.1.won = true |
        detailedGameWithCache Concrete.scheme adversary] ≤
      Pr[fun execution : GameOutcome × QueryCache HashSpec => ∃ event : BadEvent,
        OutcomeBadEventOccurs execution.2 execution.1 event |
        detailedGameWithCache Concrete.scheme adversary] := by
      apply probEvent_mono
      intro execution hmem hwin
      exact winning_outcome_has_badEvent execution.2 execution.1
        (detailed_execution_consistent adversary execution hmem) hwin
    _ ≤ ∑ event : BadEvent,
        Pr[fun execution : GameOutcome × QueryCache HashSpec =>
          OutcomeBadEventOccurs execution.2 execution.1 event |
          detailedGameWithCache Concrete.scheme adversary] := by
      simpa only [Finset.mem_univ, true_and] using
        probEvent_exists_finset_le_sum (Finset.univ : Finset BadEvent)
          (detailedGameWithCache Concrete.scheme adversary)
          (fun event execution => OutcomeBadEventOccurs execution.2 execution.1 event)

end XmssSecurity

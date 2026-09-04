import SphincsSecurity.Proof.ReplayWorld

/-!
# Replaying signing-log entries

Every entry in the adversary's signing log comes with the cache interval in which that invocation
of the signer ran. Replaying fixes hash answers but leaves the signer's uniform choices sampled.
-/

namespace SphincsSecurity

open OracleComp OracleSpec

noncomputable def replayMappedAdversaryImpl (f : QueryImpl HashSpec Id)
    (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (WriterT (QueryLog SigningSpec) (StateT (QueryCache HashSpec) ProbComp)) :=
  (replayRomImpl f).writerTMapBase
    (forwardOracles + signingOracle Concrete.scheme secretKey)

theorem replayMappedAdversary_cache_le (f : QueryImpl HashSpec Id)
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) alpha)
    (initialCache : QueryCache HashSpec)
    (result : (alpha × QueryLog SigningSpec) × QueryCache HashSpec)
    (hmem : result ∈ support
      (((simulateQ (replayMappedAdversaryImpl f secretKey) computation).run).run
        initialCache)) :
    initialCache ≤ result.2 := by
  apply simulateQ_replayRom_cache_le f
    ((simulateQ (forwardOracles + signingOracle Concrete.scheme secretKey) computation).run)
    initialCache result
  rw [QueryImpl.simulateQ_writerTMapBase_run]
  exact hmem

theorem replayMappedAdversary_signing_entry
    (f : QueryImpl HashSpec Id) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) alpha)
    (initialCache : QueryCache HashSpec)
    (result : (alpha × QueryLog SigningSpec) × QueryCache HashSpec)
    (hmem : result ∈ support
      (((simulateQ (replayMappedAdversaryImpl f secretKey) computation).run).run
        initialCache)) :
    ∀ entry ∈ result.1.2, ∃ beforeCache afterCache,
      (entry.2, afterCache) ∈ support
        ((simulateQ (replayRomImpl f) (Concrete.scheme.sign secretKey entry.1)).run beforeCache)
        ∧ afterCache ≤ result.2 := by
  induction computation using OracleComp.inductionOn generalizing initialCache result with
  | pure value =>
      simp only [simulateQ_pure, WriterT.run_pure', StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at hmem
      subst result
      intro entry hentry
      simp at hentry
  | query_bind input next ih =>
      rw [simulateQ_bind, WriterT.run_bind', StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨⟨output, queryLog⟩, middleCache⟩, hquery, hrestMapped⟩ := hmem
      rw [StateT.run_map, support_map] at hrestMapped
      obtain ⟨⟨⟨value, restLog⟩, finalCache⟩, hrest, heq⟩ := hrestMapped
      cases heq
      intro entry hentry
      change entry ∈ queryLog ++ restLog at hentry
      rw [List.mem_append] at hentry
      rcases hentry with hcurrent | hlater
      · cases input with
        | inl worldInput =>
            simp only [simulateQ_spec_query, replayMappedAdversaryImpl,
              QueryImpl.writerTMapBase, QueryImpl.add_apply_inl, forwardOracles,
              WriterT.run_mk] at hquery
            erw [WriterT.run_liftM] at hquery
            rw [simulateQ_map, StateT.run_map, support_map] at hquery
            obtain ⟨⟨worldOutput, worldCache⟩, _, heq⟩ := hquery
            cases heq
            simp at hcurrent
        | inr signingRequest =>
            simp only [simulateQ_spec_query, replayMappedAdversaryImpl,
              QueryImpl.writerTMapBase, QueryImpl.add_apply_inr, signingOracle] at hquery
            rw [WriterT.run_mk] at hquery
            erw [QueryImpl.run_withLogging_apply] at hquery
            erw [simulateQ_bind] at hquery
            rw [StateT.run_bind, mem_support_bind_iff] at hquery
            obtain ⟨⟨signOutput, signCache⟩, hsign, hpure⟩ := hquery
            cases hpure
            simp only [List.mem_singleton] at hcurrent
            subst entry
            have hsignFinal : signCache ≤ finalCache :=
              replayMappedAdversary_cache_le f secretKey (next signOutput) signCache
                ((value, restLog), finalCache) hrest
            exact ⟨initialCache, signCache, by simpa only [Concrete.scheme] using hsign, hsignFinal⟩
      · exact ih output middleCache ((value, restLog), finalCache) hrest entry hlater

theorem signing_entry_of_mem_support (f : QueryImpl HashSpec Id)
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) alpha)
    (initialCache : QueryCache HashSpec) (value : alpha) (signingLog : QueryLog SigningSpec)
    (adversaryCache finalCache : QueryCache HashSpec)
    (hmem : ((value, signingLog), adversaryCache) ∈ support
      ((simulateQ romImpl
        ((simulateQ (forwardOracles + signingOracle Concrete.scheme secretKey)
          computation).run)).run initialCache))
    (hle : adversaryCache ≤ finalCache) (hf : finalCache.AgreesWithFn f)
    (entry : (request : SignRequest) × SigningSpec.Range request)
    (hentry : entry ∈ signingLog) :
    ∃ beforeCache afterCache,
      (entry.2, afterCache) ∈ support
        ((simulateQ (replayRomImpl f) (Concrete.scheme.sign secretKey entry.1)).run beforeCache)
        ∧ afterCache ≤ finalCache := by
  have hfAdversary : adversaryCache.AgreesWithFn f := fun _ _ hcached => hf (hle hcached)
  have hreplay := replayRom_of_mem_support
    ((simulateQ (forwardOracles + signingOracle Concrete.scheme secretKey) computation).run)
    initialCache (value, signingLog) adversaryCache hmem f hfAdversary
  have hmapped : ((value, signingLog), adversaryCache) ∈ support
      (((simulateQ (replayMappedAdversaryImpl f secretKey) computation).run).run
        initialCache) := by
    rw [replayMappedAdversaryImpl, ← QueryImpl.simulateQ_writerTMapBase_run]
    exact hreplay
  obtain ⟨beforeCache, afterCache, hsign, hafter⟩ :=
    replayMappedAdversary_signing_entry f secretKey computation initialCache
      ((value, signingLog), adversaryCache) hmapped entry hentry
  exact ⟨beforeCache, afterCache, hsign, hafter.trans hle⟩

end SphincsSecurity

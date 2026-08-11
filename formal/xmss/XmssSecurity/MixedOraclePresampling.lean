import XmssSecurity.Execution
import XmssSecurity.RandomOraclePresampling

open OracleComp OracleSpec

namespace XmssSecurity

/-- Sampling one absent hash entry before a computation over the full XMSS oracle preserves its output distribution. -/
theorem evalDist_xmssRom_run'_eq_presample
    {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (target : HashInput)
    (habsent : cache target = none) :
    𝒟[(simulateQ xmssRomImpl computation).run' cache] =
      𝒟[do
        let value ← $ᵗ HashOutput
        (simulateQ xmssRomImpl computation).run'
          (cache.cacheQuery target value)] := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value =>
      change 𝒟[(pure value : ProbComp α)] =
        𝒟[do let _sampled ← $ᵗ HashOutput; pure value]
      symm
      exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        ($ᵗ HashOutput) (probFailure_uniformSample HashOutput) (pure value)
  | query_bind input next ih =>
      cases input with
      | inl uniformIndex =>
          change Fin (uniformIndex + 1) → OracleComp OracleWorld α at next
          have hrun (initialCache : QueryCache HashSpec) :
              (simulateQ xmssRomImpl
                (liftM (OracleWorld.query (.inl uniformIndex)) >>= next)).run'
                  initialCache =
              ((unifSpec.query uniformIndex : ProbComp _) >>= fun sampled =>
                (simulateQ xmssRomImpl (next sampled)).run' initialCache) := by
            simp [StateT.run'_eq, StateT.run_bind, xmssRomImpl, unifFwdImpl,
              QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply,
              map_eq_bind_pure_comp]
          rw [hrun]
          calc
            𝒟[(unifSpec.query uniformIndex : ProbComp _) >>= fun sampled =>
                (simulateQ xmssRomImpl (next sampled)).run' cache] =
                𝒟[(unifSpec.query uniformIndex : ProbComp _) >>= fun sampled =>
                  ($ᵗ HashOutput) >>= fun value =>
                    (simulateQ xmssRomImpl (next sampled)).run'
                      (cache.cacheQuery target value)] := by
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro sampled
              exact ih sampled cache habsent
            _ = 𝒟[($ᵗ HashOutput) >>= fun value =>
                  (unifSpec.query uniformIndex : ProbComp _) >>= fun sampled =>
                    (simulateQ xmssRomImpl (next sampled)).run'
                      (cache.cacheQuery target value)] :=
              OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
            _ = 𝒟[($ᵗ HashOutput) >>= fun value =>
                  (simulateQ xmssRomImpl
                    (liftM (OracleWorld.query (.inl uniformIndex)) >>= next)).run'
                      (cache.cacheQuery target value)] := by
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro value
              rw [hrun]
      | inr hashInput =>
          have hrun (initialCache : QueryCache HashSpec) :
              (simulateQ xmssRomImpl
                (liftM (OracleWorld.query (.inr hashInput)) >>= next)).run'
                  initialCache =
              ((randomOracle (spec := HashSpec) hashInput).run initialCache) >>=
                fun result =>
                  (simulateQ xmssRomImpl (next result.1)).run' result.2 := by
            rw [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq,
              StateT.run_bind, map_bind]
            rfl
          by_cases htarget : hashInput = target
          · subst hashInput
            rw [hrun, QueryImpl.withCaching_run_none _ habsent,
              map_eq_bind_pure_comp]
            simp only [Function.comp_apply, bind_assoc, pure_bind]
            apply OracleComp.DeferredSampling.evalDist_bind_congr_left
            intro sampled
            rw [hrun, QueryImpl.withCaching_run_some _
              (QueryCache.cacheQuery_self cache target sampled), pure_bind]
          · cases hinput : cache hashInput with
            | some answer =>
                rw [hrun, QueryImpl.withCaching_run_some _ hinput, pure_bind]
                change 𝒟[(simulateQ xmssRomImpl (next answer)).run' cache] =
                  𝒟[$ᵗ HashOutput >>= fun sampled =>
                    (simulateQ xmssRomImpl
                      (liftM (OracleWorld.query (.inr hashInput)) >>= next)).run'
                        (cache.cacheQuery target sampled)]
                calc
                  𝒟[(simulateQ xmssRomImpl (next answer)).run' cache] =
                      𝒟[do
                        let sampled ← $ᵗ HashOutput
                        (simulateQ xmssRomImpl (next answer)).run'
                          (cache.cacheQuery target sampled)] :=
                    ih answer cache habsent
                  _ = 𝒟[do
                        let sampled ← $ᵗ HashOutput
                        (simulateQ xmssRomImpl
                          (liftM (OracleWorld.query (.inr hashInput)) >>= next)).run'
                            (cache.cacheQuery target sampled)] := by
                    apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                    intro sampled
                    have hcached :
                        (cache.cacheQuery target sampled) hashInput = some answer := by
                      rw [QueryCache.cacheQuery_of_ne cache sampled htarget]
                      exact hinput
                    rw [hrun, QueryImpl.withCaching_run_some _ hcached, pure_bind]
                rfl
            | none =>
                have htargetAfterInput : ∀ answer : HashOutput,
                    (cache.cacheQuery hashInput answer) target = none := by
                  intro answer
                  simpa [QueryCache.cacheQuery_of_ne, Ne.symm htarget] using habsent
                rw [hrun, QueryImpl.withCaching_run_none _ hinput,
                  map_eq_bind_pure_comp]
                simp only [Function.comp_apply, bind_assoc, pure_bind]
                change 𝒟[$ᵗ HashOutput >>= fun answer =>
                    (simulateQ xmssRomImpl (next answer)).run'
                      (cache.cacheQuery hashInput answer)] =
                  𝒟[$ᵗ HashOutput >>= fun sampled =>
                    (simulateQ xmssRomImpl
                      (liftM (OracleWorld.query (.inr hashInput)) >>= next)).run'
                        (cache.cacheQuery target sampled)]
                calc
                  𝒟[$ᵗ HashOutput >>= fun answer =>
                        (simulateQ xmssRomImpl (next answer)).run'
                          (cache.cacheQuery hashInput answer)] =
                      𝒟[$ᵗ HashOutput >>= fun answer =>
                        $ᵗ HashOutput >>= fun sampled =>
                          (simulateQ xmssRomImpl (next answer)).run'
                            ((cache.cacheQuery hashInput answer).cacheQuery target sampled)] := by
                    apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                    intro answer
                    exact ih answer (cache.cacheQuery hashInput answer)
                      (htargetAfterInput answer)
                  _ = 𝒟[$ᵗ HashOutput >>= fun sampled =>
                        $ᵗ HashOutput >>= fun answer =>
                          (simulateQ xmssRomImpl (next answer)).run'
                            ((cache.cacheQuery hashInput answer).cacheQuery target sampled)] :=
                    OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
                  _ = 𝒟[$ᵗ HashOutput >>= fun sampled =>
                        $ᵗ HashOutput >>= fun answer =>
                          (simulateQ xmssRomImpl (next answer)).run'
                            ((cache.cacheQuery target sampled).cacheQuery hashInput answer)] := by
                    apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                    intro sampled
                    apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                    intro answer
                    rw [QueryCache.cacheQuery_comm_of_ne cache htarget]
                  _ = 𝒟[do
                        let sampled ← $ᵗ HashOutput
                        (simulateQ xmssRomImpl
                          (liftM (OracleWorld.query (.inr hashInput)) >>= next)).run'
                            (cache.cacheQuery target sampled)] := by
                    apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                    intro sampled
                    have hnone :
                        (cache.cacheQuery target sampled) hashInput = none := by
                      rw [QueryCache.cacheQuery_of_ne cache sampled htarget]
                      exact hinput
                    rw [hrun, QueryImpl.withCaching_run_none _ hnone,
                      map_eq_bind_pure_comp]
                    simp only [Function.comp_apply, bind_assoc, pure_bind]
                    change 𝒟[$ᵗ HashOutput >>= fun answer =>
                        (simulateQ xmssRomImpl (next answer)).run'
                          ((cache.cacheQuery target sampled).cacheQuery hashInput answer)] = _
                    rfl
                rfl

/-- Any finite pairwise-distinct list of absent hash entries may be sampled before a computation over the full XMSS oracle. -/
theorem evalDist_xmssRom_run'_eq_presampleList
    {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ (inputs : List HashInput) (cache : QueryCache HashSpec),
      inputs.Nodup →
      (∀ input ∈ inputs, cache input = none) →
      𝒟[(simulateQ xmssRomImpl computation).run' cache] =
        𝒟[do
          let sampledCache ← OracleComp.presampleCacheEntries cache inputs
          (simulateQ xmssRomImpl computation).run' sampledCache] := by
  intro inputs
  induction inputs with
  | nil =>
      intro cache _hnodup _habsent
      simp
  | cons input inputs ih =>
      intro cache hnodup habsent
      obtain ⟨hnotMem, htailNodup⟩ := List.nodup_cons.mp hnodup
      rw [evalDist_xmssRom_run'_eq_presample computation cache input
        (habsent input (by simp))]
      rw [OracleComp.presampleCacheEntries_cons]
      simp only [bind_assoc]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro value
      apply ih (cache.cacheQuery input value) htailNodup
      intro target htarget
      rw [QueryCache.cacheQuery_of_ne]
      · exact habsent target (by simp [htarget])
      · intro heq
        subst target
        exact hnotMem htarget

/-- The finite presampling equivalence can retain the sampled values alongside the threaded cache. -/
theorem evalDist_xmssRom_run'_eq_presampleTrace
    {α : Type} (computation : OracleComp OracleWorld α)
    (inputs : List HashInput) (cache : QueryCache HashSpec)
    (hnodup : inputs.Nodup)
    (habsent : ∀ input ∈ inputs, cache input = none) :
    𝒟[(simulateQ xmssRomImpl computation).run' cache] =
      𝒟[do
        let trace ← OracleComp.presampleCacheEntriesTrace cache inputs
        (simulateQ xmssRomImpl computation).run' trace.2] := by
  calc
    𝒟[(simulateQ xmssRomImpl computation).run' cache] =
        𝒟[do
          let sampledCache ← OracleComp.presampleCacheEntries cache inputs
          (simulateQ xmssRomImpl computation).run' sampledCache] :=
      evalDist_xmssRom_run'_eq_presampleList computation inputs cache hnodup habsent
    _ = 𝒟[do
          let trace ← OracleComp.presampleCacheEntriesTrace cache inputs
          (simulateQ xmssRomImpl computation).run' trace.2] := by
      symm
      calc
        𝒟[OracleComp.presampleCacheEntriesTrace cache inputs >>= fun trace =>
            (simulateQ xmssRomImpl computation).run' trace.2] =
            𝒟[(Prod.snd <$>
                OracleComp.presampleCacheEntriesTrace cache inputs) >>= fun sampledCache =>
              (simulateQ xmssRomImpl computation).run' sampledCache] := by
          simp [map_eq_bind_pure_comp, bind_assoc]
        _ = 𝒟[OracleComp.presampleCacheEntries cache inputs >>= fun sampledCache =>
              (simulateQ xmssRomImpl computation).run' sampledCache] := by
          conv_lhs => rw [evalDist_bind]
          conv_rhs => rw [evalDist_bind]
          rw [OracleComp.evalDist_presampleCacheEntriesTrace_snd]
  rfl

end XmssSecurity

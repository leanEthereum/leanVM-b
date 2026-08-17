import XmssSecurity.AdaptiveFreshTarget
import XmssSecurity.ExpectedQueryCount

open OracleComp ENNReal

namespace XmssSecurity.Rom

open OracleSpec

noncomputable local instance : IsUniformSpec HashSpec :=
  IsUniformSpec.ofFintypeInhabited _

/-- The fresh-target collision loss is proportional to the expected number of hash queries. -/
theorem mixed_adaptive_truncated_output_fresh_hit_from_cache_le_expected
    {α : Type} (computation : OracleComp OracleWorld α)
    (target : HashInput → Digest) (cache : QueryCache HashSpec) :
    Pr[fun result => ∃ input output,
        result.2 input = some output ∧ cache input = none ∧
          truncateHash output = target input |
      (simulateQ xmssRomImpl computation).run cache] ≤
      expectedSimulatedQueryCount xmssRomImpl (· matches .inr _)
        computation cache / ((2 ^ digestBits : Nat) : ENNReal) := by
  let digestCard : ENNReal := ((2 ^ digestBits : Nat) : ENNReal)
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value =>
      refine le_of_eq_of_le (b := 0) ?_ zero_le
      rw [simulateQ_pure]
      refine probEvent_eq_zero fun result hresult hhit => ?_
      change result ∈ support (pure (value, cache) : ProbComp _) at hresult
      rw [support_pure, Set.mem_singleton_iff] at hresult
      subst result
      obtain ⟨input, output, hcache, hnone, _⟩ := hhit
      simp [hnone] at hcache
  | query_bind query next ih =>
      rcases query with uniformIndex | hashInput
      · change Fin (uniformIndex + 1) → OracleComp OracleWorld α at next
        have hrun :
            (simulateQ xmssRomImpl
              (liftM (OracleWorld.query (.inl uniformIndex)) >>= next)).run cache =
            ((unifSpec.query uniformIndex : ProbComp _) >>= fun sampled =>
              (simulateQ xmssRomImpl (next sampled)).run cache) := by
          simp [StateT.run_bind, xmssRomImpl, unifFwdImpl,
            QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply]
        have hcount :
            expectedSimulatedQueryCount xmssRomImpl (· matches .inr _)
                (liftM (OracleWorld.query (.inl uniformIndex)) >>= next) cache =
              ∑' sampled, Pr[= sampled | (unifSpec.query uniformIndex : ProbComp _)] *
                expectedSimulatedQueryCount xmssRomImpl (· matches .inr _)
                  (next sampled) cache := by
          rw [expectedSimulatedQueryCount_query_bind]
          simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
          change (∑' result, Pr[= result |
              (fun sampled => (sampled, cache)) <$>
                (unifSpec.query uniformIndex : ProbComp _)] *
                expectedSimulatedQueryCount xmssRomImpl (· matches .inr _)
                  (next result.1) result.2) = _
          rw [tsum_probOutput_map_mul]
        rw [hrun, probEvent_bind_eq_tsum, hcount, div_eq_mul_inv,
          ← ENNReal.tsum_mul_right]
        apply ENNReal.tsum_le_tsum
        intro sampled
        rw [mul_assoc]
        gcongr
        exact ih sampled cache
      · change HashOutput → OracleComp OracleWorld α at next
        by_cases hcached : ∃ output, cache hashInput = some output
        · obtain ⟨output, houtput⟩ := hcached
          have hquery :
              (simulateQ xmssRomImpl
                (liftM (OracleWorld.query (.inr hashInput)))).run cache =
              pure ((show OracleWorld.Range (.inr hashInput) from output), cache) := by
            rw [simulateQ_spec_query]
            change (randomOracle (spec := HashSpec) hashInput).run cache = pure (output, cache)
            rw [QueryImpl.withCaching_run_some _ houtput]
          have hrun :
              (simulateQ xmssRomImpl
                (liftM (OracleWorld.query (.inr hashInput)) >>= next)).run cache =
              (simulateQ xmssRomImpl (next output)).run cache := by
            rw [simulateQ_bind, StateT.run_bind]
            rw [hquery, pure_bind]
          have hcount :
              expectedSimulatedQueryCount xmssRomImpl (· matches .inr _)
                  (liftM (OracleWorld.query (.inr hashInput)) >>= next) cache =
                1 + expectedSimulatedQueryCount xmssRomImpl (· matches .inr _)
                  (next output) cache := by
            rw [expectedSimulatedQueryCount_query_bind]
            simp only [↓reduceIte]
            have hhandler :
                (xmssRomImpl (.inr hashInput)).run cache =
                  pure ((show OracleWorld.Range (.inr hashInput) from output), cache) := by
              change (randomOracle (spec := HashSpec) hashInput).run cache = _
              rw [QueryImpl.withCaching_run_some _ houtput]
              simp
            rw [hhandler, tsum_probOutput_pure_mul]
            simp
          rw [hrun, hcount]
          exact (ih output cache).trans (by gcongr; exact le_add_left le_rfl)
        · push Not at hcached
          have hnone : cache hashInput = none := Option.eq_none_iff_forall_ne_some.mpr hcached
          have hquery :
              (simulateQ xmssRomImpl
                (liftM (OracleWorld.query (.inr hashInput)))).run cache =
              (($ᵗ HashOutput) >>= fun output =>
                pure (output, cache.cacheQuery hashInput output) : ProbComp _) := by
            rw [simulateQ_spec_query]
            change (randomOracle (spec := HashSpec) hashInput).run cache = _
            rw [QueryImpl.withCaching_run_none _ hnone]
            simp [uniformSampleImpl, map_eq_bind_pure_comp]
          have hrun :
              (simulateQ xmssRomImpl
                (liftM (OracleWorld.query (.inr hashInput)) >>= next)).run cache =
              (($ᵗ HashOutput) >>= fun output =>
                (simulateQ xmssRomImpl (next output)).run
                  (cache.cacheQuery hashInput output)) := by
            rw [simulateQ_bind, StateT.run_bind]
            rw [hquery]
            simp [monad_norm]
          have hcount :
              expectedSimulatedQueryCount xmssRomImpl (· matches .inr _)
                  (liftM (OracleWorld.query (.inr hashInput)) >>= next) cache =
                1 + ∑' output, Pr[= output | $ᵗ HashOutput] *
                  expectedSimulatedQueryCount xmssRomImpl (· matches .inr _)
                    (next output) (cache.cacheQuery hashInput output) := by
            rw [expectedSimulatedQueryCount_query_bind]
            simp only [↓reduceIte]
            have hhandler : (xmssRomImpl (.inr hashInput)).run cache =
                (fun output : HashOutput =>
                  ((show OracleWorld.Range (.inr hashInput) from output),
                    cache.cacheQuery hashInput output)) <$>
                  ($ᵗ HashOutput) := by
              change (randomOracle (spec := HashSpec) hashInput).run cache = _
              rw [QueryImpl.withCaching_run_none _ hnone]
              simp [uniformSampleImpl]
            rw [hhandler, tsum_probOutput_map_mul]
            simp
          rw [hrun, probEvent_bind_eq_tsum]
          have hrest : ∀ output : HashOutput,
              truncateHash output ≠ target hashInput →
              Pr[fun result => ∃ input candidateOutput,
                    result.2 input = some candidateOutput ∧ cache input = none ∧
                      truncateHash candidateOutput = target input |
                (simulateQ xmssRomImpl (next output)).run
                  (cache.cacheQuery hashInput output)] ≤
                expectedSimulatedQueryCount xmssRomImpl (· matches .inr _)
                    (next output) (cache.cacheQuery hashInput output) /
                  digestCard := by
            intro output hmiss
            calc
              Pr[fun result => ∃ input candidateOutput,
                    result.2 input = some candidateOutput ∧ cache input = none ∧
                      truncateHash candidateOutput = target input |
                  (simulateQ xmssRomImpl (next output)).run
                    (cache.cacheQuery hashInput output)] ≤
                Pr[fun result => ∃ input candidateOutput,
                    result.2 input = some candidateOutput ∧
                      (cache.cacheQuery hashInput output) input = none ∧
                      truncateHash candidateOutput = target input |
                  (simulateQ xmssRomImpl (next output)).run
                    (cache.cacheQuery hashInput output)] := by
                  apply probEvent_mono
                  intro result hresult
                  rintro ⟨input, candidateOutput, hfinal, hinitial, htarget⟩
                  by_cases heq : input = hashInput
                  · subst input
                    have hle := xmssRom_cache_le (next output)
                      (cache.cacheQuery hashInput output) result hresult
                    have hcurrent := hle (QueryCache.cacheQuery_self cache hashInput output)
                    rw [hcurrent] at hfinal
                    cases hfinal
                    exact (hmiss htarget).elim
                  · exact ⟨input, candidateOutput, hfinal, by
                      rw [QueryCache.cacheQuery_of_ne _ _ heq]
                      exact hinitial, htarget⟩
              _ ≤ _ := ih output (cache.cacheQuery hashInput output)
          calc
            ∑' output, Pr[= output | ($ᵗ HashOutput)] *
                Pr[fun result => ∃ input candidateOutput,
                    result.2 input = some candidateOutput ∧ cache input = none ∧
                      truncateHash candidateOutput = target input |
                  (simulateQ xmssRomImpl (next output)).run
                    (cache.cacheQuery hashInput output)] ≤
              ∑' output, ((if truncateHash output = target hashInput then
                  Pr[= output | ($ᵗ HashOutput)] else 0) +
                Pr[= output | ($ᵗ HashOutput)] *
                  (expectedSimulatedQueryCount xmssRomImpl (· matches .inr _)
                    (next output) (cache.cacheQuery hashInput output) /
                      digestCard)) := by
                apply ENNReal.tsum_le_tsum
                intro output
                by_cases heq : truncateHash output = target hashInput
                · simp only [heq, ite_true]
                  calc
                    Pr[= output | ($ᵗ HashOutput)] * _ ≤
                        Pr[= output | ($ᵗ HashOutput)] * 1 :=
                      mul_le_mul' le_rfl probEvent_le_one
                    _ = Pr[= output | ($ᵗ HashOutput)] := mul_one _
                    _ ≤ Pr[= output | ($ᵗ HashOutput)] + _ := le_add_right le_rfl
                · simp only [heq, ite_false, zero_add]
                  exact mul_le_mul' le_rfl (hrest output heq)
            _ = (∑' output : HashOutput,
                  if truncateHash output = target hashInput then
                    Pr[= output | ($ᵗ HashOutput)] else 0) +
                (∑' output, Pr[= output | ($ᵗ HashOutput)] *
                  expectedSimulatedQueryCount xmssRomImpl (· matches .inr _)
                    (next output) (cache.cacheQuery hashInput output)) /
                  digestCard := by
              rw [ENNReal.tsum_add]
              congr 1
              rw [div_eq_mul_inv, ← ENNReal.tsum_mul_right]
              apply tsum_congr
              intro output
              rw [div_eq_mul_inv, mul_assoc]
            _ ≤ digestCard⁻¹ +
                (∑' output, Pr[= output | ($ᵗ HashOutput)] *
                  expectedSimulatedQueryCount xmssRomImpl (· matches .inr _)
                    (next output) (cache.cacheQuery hashInput output)) /
                  digestCard := by
              gcongr
              rw [← probEvent_eq_tsum_ite]
              exact (uniform_truncate_probability (target hashInput)).le
            _ = (1 + ∑' output, Pr[= output | ($ᵗ HashOutput)] *
                  expectedSimulatedQueryCount xmssRomImpl (· matches .inr _)
                    (next output) (cache.cacheQuery hashInput output)) /
                digestCard := by
              simp [div_eq_mul_inv, add_mul]
            _ = expectedSimulatedQueryCount xmssRomImpl (· matches .inr _)
                  (liftM (OracleWorld.query (.inr hashInput)) >>= next) cache /
                ((2 ^ digestBits : Nat) : ENNReal) := by
              rw [hcount]

/-- An adaptive fresh-target collision is charged to the expected number of hash queries. -/
theorem mixed_adaptiveFreshDigestCollisionWith_le_expected
    {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (targetInput : HashInput → HashInput)
    (win : α × QueryCache HashSpec → Prop)
    (hwin : ∀ result ∈ support ((simulateQ xmssRomImpl computation).run cache),
      win result → AdaptiveFreshDigestCollisionWith cache result.2 targetInput) :
    Pr[win | (simulateQ xmssRomImpl computation).run cache] ≤
      expectedSimulatedQueryCount xmssRomImpl (· matches .inr _)
        computation cache / ((2 ^ digestBits : Nat) : ENNReal) := by
  let experiment := (simulateQ xmssRomImpl computation).run cache
  let target : HashInput → Digest := fun input =>
    Concrete.CacheView.digestAt cache (targetInput input)
  calc
    Pr[win | experiment] ≤
        Pr[fun result => ∃ input output,
          result.2 input = some output ∧ cache input = none ∧
            truncateHash output = target input | experiment] := by
      apply probEvent_mono
      intro result hresult hresultWin
      obtain ⟨input, output, targetOutput, houtput, hfresh, htarget, hcollision⟩ :=
        hwin result hresult hresultWin
      have hcacheLe := xmssRom_cache_le computation cache result hresult
      have htargetFinal := hcacheLe htarget
      refine ⟨input, output, houtput, hfresh, ?_⟩
      calc
        truncateHash output = Concrete.CacheView.digestAt result.2 input :=
          (Concrete.CacheView.digestAt_eq_of_cache_eq_some houtput).symm
        _ = Concrete.CacheView.digestAt result.2 (targetInput input) := hcollision
        _ = truncateHash targetOutput :=
          Concrete.CacheView.digestAt_eq_of_cache_eq_some htargetFinal
        _ = Concrete.CacheView.digestAt cache (targetInput input) :=
          (Concrete.CacheView.digestAt_eq_of_cache_eq_some htarget).symm
    _ ≤ _ := mixed_adaptive_truncated_output_fresh_hit_from_cache_le_expected
      computation target cache

end XmssSecurity.Rom

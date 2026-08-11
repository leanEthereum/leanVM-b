import XmssSecurity.FreshTarget

open OracleComp ENNReal

namespace XmssSecurity.Rom

/-- A uniform 256-bit oracle output has any fixed 128-bit truncation with probability exactly `2^-128`. -/
theorem uniform_truncate_probability (target : Digest) :
    Pr[fun output : HashOutput => truncateHash output = target | $ᵗ HashOutput] =
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  rw [probEvent_uniformSample]
  change ((matchingOutputs target).card : ℝ≥0∞) /
      (Fintype.card HashOutput : ℝ≥0∞) = _
  rw [card_matchingOutputs, card_hashOutput, hashOutputBits_eq, Nat.pow_add,
    Nat.cast_mul, div_eq_mul_inv]
  have hzero : ((2 ^ digestBits : Nat) : ℝ≥0∞) ≠ 0 := by positivity
  have htop : ((2 ^ digestBits : Nat) : ℝ≥0∞) ≠ ∞ := by simp
  rw [ENNReal.mul_inv (Or.inl hzero) (Or.inl htop)]
  calc
    ((2 ^ digestBits : Nat) : ℝ≥0∞) *
        (((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) =
      (((2 ^ digestBits : Nat) : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by ac_rfl
    _ = ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
      rw [ENNReal.mul_inv_cancel hzero htop, one_mul]

open OracleSpec

noncomputable local instance : IsUniformSpec HashSpec :=
  IsUniformSpec.ofFintypeInhabited _

/-- Each fresh query may select its own target digest without adding an index-set loss. -/
theorem mixed_adaptive_truncated_output_fresh_hit_from_cache_le {α : Type}
    (computation : OracleComp OracleWorld α) (q : Nat)
    (hbound : computation.IsQueryBoundP (· matches .inr _) q)
    (target : HashInput → Digest) (cache : QueryCache HashSpec) :
    Pr[fun result => ∃ input output,
        result.2 input = some output ∧ cache input = none ∧
          truncateHash output = target input |
      (simulateQ xmssRomImpl computation).run cache] ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  let digestCard : ℝ≥0∞ := ((2 ^ digestBits : Nat) : ℝ≥0∞)
  have hdigestCard : digestCard = ((2 ^ digestBits : Nat) : ℝ≥0∞) := rfl
  induction computation using OracleComp.inductionOn generalizing q cache with
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
      rw [isQueryBoundP_query_bind_iff] at hbound
      rcases query with uniformIndex | hashInput
      · change Fin (uniformIndex + 1) → OracleComp OracleWorld α at next
        have hrun :
            (simulateQ xmssRomImpl
              (liftM (OracleWorld.query (.inl uniformIndex)) >>= next)).run cache =
            ((unifSpec.query uniformIndex : ProbComp _) >>= fun sampled =>
              (simulateQ xmssRomImpl (next sampled)).run cache) := by
          simp [StateT.run_bind, xmssRomImpl, unifFwdImpl,
            QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply]
        rw [hrun]
        refine probEvent_bind_le_of_forall_le fun sampled _ => ?_
        exact ih sampled q (by simpa using hbound.2 sampled) cache
      · by_cases hcached : ∃ output, cache hashInput = some output
        · obtain ⟨output, houtput⟩ := hcached
          have hrun :
              (simulateQ xmssRomImpl
                (liftM (OracleWorld.query (.inr hashInput)) >>= next)).run cache =
              (simulateQ xmssRomImpl (next output)).run cache := by
            have hquery :
                (simulateQ xmssRomImpl
                  (liftM (OracleWorld.query (.inr hashInput)))).run cache =
                pure ((show OracleWorld.Range (.inr hashInput) from output), cache) := by
              rw [simulateQ_spec_query]
              change (randomOracle (spec := HashSpec) hashInput).run cache = pure (output, cache)
              rw [QueryImpl.withCaching_run_some _ houtput]
            rw [simulateQ_bind, StateT.run_bind]
            change ((simulateQ xmssRomImpl
              (liftM (OracleWorld.query (.inr hashInput)))).run cache >>= fun p =>
                (simulateQ xmssRomImpl (next p.1)).run p.2) = _
            rw [hquery, pure_bind]
          rw [hrun]
          exact ih output (q - 1) (by simpa using hbound.2 output) cache |>.trans (by
            gcongr
            exact_mod_cast Nat.sub_le q 1)
        · push Not at hcached
          have hnone : cache hashInput = none := Option.eq_none_iff_forall_ne_some.mpr hcached
          have hrun :
              (simulateQ xmssRomImpl
                (liftM (OracleWorld.query (.inr hashInput)) >>= next)).run cache =
              (($ᵗ HashOutput) >>= fun output =>
                (simulateQ xmssRomImpl (next output)).run
                  (cache.cacheQuery hashInput output)) := by
            have hquery :
                (simulateQ xmssRomImpl
                  (liftM (OracleWorld.query (.inr hashInput)))).run cache =
                (($ᵗ HashOutput) >>= fun output =>
                  pure (output, cache.cacheQuery hashInput output) : ProbComp _) := by
              rw [simulateQ_spec_query]
              change (randomOracle (spec := HashSpec) hashInput).run cache = _
              rw [QueryImpl.withCaching_run_none _ hnone]
              simp [uniformSampleImpl, map_eq_bind_pure_comp]
            rw [simulateQ_bind, StateT.run_bind]
            change ((simulateQ xmssRomImpl
              (liftM (OracleWorld.query (.inr hashInput)))).run cache >>= fun p =>
                (simulateQ xmssRomImpl (next p.1)).run p.2) = _
            rw [hquery]
            simp [monad_norm]
          rw [hrun, probEvent_bind_eq_tsum]
          have hrest : ∀ output : HashOutput,
              truncateHash output ≠ target hashInput →
              Pr[fun result => ∃ input candidateOutput,
                    result.2 input = some candidateOutput ∧ cache input = none ∧
                      truncateHash candidateOutput = target input |
                (simulateQ xmssRomImpl (next output)).run
                  (cache.cacheQuery hashInput output)] ≤
                ((q - 1 : Nat) : ℝ≥0∞) * digestCard⁻¹ := by
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
              _ ≤ ((q - 1 : Nat) : ℝ≥0∞) /
                    ((2 ^ digestBits : Nat) : ℝ≥0∞) :=
                ih output (q - 1) (by simpa using hbound.2 output)
                  (cache.cacheQuery hashInput output)
              _ = ((q - 1 : Nat) : ℝ≥0∞) * digestCard⁻¹ := by
                simp [digestCard, div_eq_mul_inv]
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
                  (((q - 1 : Nat) : ℝ≥0∞) * digestCard⁻¹)) := by
                refine ENNReal.tsum_le_tsum fun output => ?_
                by_cases heq : truncateHash output = target hashInput
                · simp only [heq, ite_true]
                  calc
                    Pr[= output | ($ᵗ HashOutput)] *
                        Pr[fun result => ∃ input candidateOutput,
                            result.2 input = some candidateOutput ∧ cache input = none ∧
                              truncateHash candidateOutput = target input |
                          (simulateQ xmssRomImpl (next output)).run
                            (cache.cacheQuery hashInput output)] ≤
                      Pr[= output | ($ᵗ HashOutput)] * 1 :=
                        mul_le_mul' le_rfl probEvent_le_one
                    _ = Pr[= output | ($ᵗ HashOutput)] := mul_one _
                    _ ≤ Pr[= output | ($ᵗ HashOutput)] + _ := le_add_right le_rfl
                · simp only [heq, ite_false, zero_add]
                  exact mul_le_mul' le_rfl (hrest output heq)
            _ = (∑' output : HashOutput,
                  if truncateHash output = target hashInput then
                    Pr[= output | ($ᵗ HashOutput)] else 0) +
                (∑' output : HashOutput,
                  Pr[= output | ($ᵗ HashOutput)]) *
                  (((q - 1 : Nat) : ℝ≥0∞) * digestCard⁻¹) := by
              rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
            _ ≤ digestCard⁻¹ + 1 * (((q - 1 : Nat) : ℝ≥0∞) * digestCard⁻¹) := by
              apply add_le_add
              · rw [← probEvent_eq_tsum_ite]
                rw [hdigestCard]
                exact (uniform_truncate_probability (target hashInput)).le
              · exact mul_le_mul' tsum_probOutput_le_one le_rfl
            _ = (q : ℝ≥0∞) * digestCard⁻¹ := by
              have hqpos : 0 < q := by simpa using hbound.1
              have hqone : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hqpos)
              rw [one_mul, ← one_add_mul, ← Nat.cast_one, ← Nat.cast_add,
                Nat.add_sub_cancel' hqone]
            _ = (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
              simp [digestCard, div_eq_mul_inv]

def AdaptiveFreshDigestCollisionWith (initialCache finalCache : QueryCache HashSpec)
    (targetInput : HashInput → HashInput) : Prop :=
  ∃ input output targetOutput,
    finalCache input = some output ∧ initialCache input = none ∧
      initialCache (targetInput input) = some targetOutput ∧
      Concrete.CacheView.digestAt finalCache input =
        Concrete.CacheView.digestAt finalCache (targetInput input)

/-- Adaptively choosing one cached target input for each fresh query still costs at most `q / 2^128`. -/
theorem mixed_adaptiveFreshDigestCollisionWith_le {α : Type}
    (computation : OracleComp OracleWorld α) (q : Nat)
    (hbound : computation.IsQueryBoundP (· matches .inr _) q)
    (cache : QueryCache HashSpec) (targetInput : HashInput → HashInput)
    (win : α × QueryCache HashSpec → Prop)
    (hwin : ∀ result ∈ support ((simulateQ xmssRomImpl computation).run cache),
      win result → AdaptiveFreshDigestCollisionWith cache result.2 targetInput) :
    Pr[win | (simulateQ xmssRomImpl computation).run cache] ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
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
    _ ≤ (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) :=
      mixed_adaptive_truncated_output_fresh_hit_from_cache_le computation q hbound target cache

end XmssSecurity.Rom

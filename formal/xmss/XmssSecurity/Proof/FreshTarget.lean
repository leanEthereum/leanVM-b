import XmssSecurity.Statement
import XmssSecurity.Proof.MixedOracle
import XmssSecurity.Proof.HashInputLemmas

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Rom

noncomputable local instance : IsUniformSpec HashSpec :=
  IsUniformSpec.ofFintypeInhabited _

/-- A later computation creates a cache entry with one fixed full output, even if older entries already have that output. -/
theorem mixed_exact_output_fresh_hit_from_cache_le {α : Type}
    (computation : OracleComp OracleWorld α) (q : Nat)
    (hbound : computation.IsQueryBoundP (· matches .inr _) q)
    (target : HashOutput) (cache : QueryCache HashSpec) :
    Pr[fun result => ∃ input,
        result.2 input = some target ∧ cache input = none |
      (simulateQ xmssRomImpl computation).run cache] ≤
      (q : ℝ≥0∞) / ((2 ^ hashOutputBits : Nat) : ℝ≥0∞) := by
  let outputCard : ℝ≥0∞ := Fintype.card HashOutput
  have hcard : outputCard = ((2 ^ hashOutputBits : Nat) : ℝ≥0∞) := by
    change ((Fintype.card HashOutput : Nat) : ℝ≥0∞) =
      ((2 ^ hashOutputBits : Nat) : ℝ≥0∞)
    exact_mod_cast card_hashOutput
  induction computation using OracleComp.inductionOn generalizing q cache with
  | pure value =>
      refine le_of_eq_of_le (b := 0) ?_ zero_le
      rw [simulateQ_pure]
      refine probEvent_eq_zero fun result hresult hhit => ?_
      change result ∈ support (pure (value, cache) : ProbComp _) at hresult
      rw [support_pure, Set.mem_singleton_iff] at hresult
      subst result
      obtain ⟨input, hcache, hnone⟩ := hhit
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
          have hrest : ∀ output : HashOutput, output ≠ target →
              Pr[fun result => ∃ input,
                    result.2 input = some target ∧ cache input = none |
                (simulateQ xmssRomImpl (next output)).run
                  (cache.cacheQuery hashInput output)] ≤
                ((q - 1 : Nat) : ℝ≥0∞) * outputCard⁻¹ := by
            intro output hne
            calc
              Pr[fun result => ∃ input,
                    result.2 input = some target ∧ cache input = none |
                  (simulateQ xmssRomImpl (next output)).run
                    (cache.cacheQuery hashInput output)] ≤
                Pr[fun result => ∃ input,
                    result.2 input = some target ∧
                      (cache.cacheQuery hashInput output) input = none |
                  (simulateQ xmssRomImpl (next output)).run
                    (cache.cacheQuery hashInput output)] := by
                  apply probEvent_mono
                  intro result hresult
                  rintro ⟨input, hfinal, hinitial⟩
                  by_cases heq : input = hashInput
                  · subst input
                    have hle := xmssRom_cache_le (next output)
                      (cache.cacheQuery hashInput output) result hresult
                    have hcurrent := hle (QueryCache.cacheQuery_self cache hashInput output)
                    rw [hcurrent] at hfinal
                    cases hfinal
                    exact (hne rfl).elim
                  · exact ⟨input, hfinal, by
                      rw [QueryCache.cacheQuery_of_ne _ _ heq]
                      exact hinitial⟩
              _ ≤ ((q - 1 : Nat) : ℝ≥0∞) /
                    ((2 ^ hashOutputBits : Nat) : ℝ≥0∞) :=
                ih output (q - 1) (by simpa using hbound.2 output)
                  (cache.cacheQuery hashInput output)
              _ = ((q - 1 : Nat) : ℝ≥0∞) * outputCard⁻¹ := by
                rw [hcard, div_eq_mul_inv]
          calc
            ∑' output, Pr[= output | ($ᵗ HashOutput)] *
                Pr[fun result => ∃ input,
                    result.2 input = some target ∧ cache input = none |
                  (simulateQ xmssRomImpl (next output)).run
                    (cache.cacheQuery hashInput output)] ≤
              ∑' output, ((if output = target then outputCard⁻¹ else 0) +
                Pr[= output | ($ᵗ HashOutput)] *
                  (((q - 1 : Nat) : ℝ≥0∞) * outputCard⁻¹)) := by
                refine ENNReal.tsum_le_tsum fun output => ?_
                by_cases heq : output = target
                · subst output
                  simp only [ite_true]
                  calc
                    Pr[= target | ($ᵗ HashOutput)] *
                        Pr[fun result => ∃ input,
                            result.2 input = some target ∧ cache input = none |
                          (simulateQ xmssRomImpl (next target)).run
                            (cache.cacheQuery hashInput target)] ≤
                      Pr[= target | ($ᵗ HashOutput)] * 1 :=
                        mul_le_mul' le_rfl probEvent_le_one
                    _ = Pr[= target | ($ᵗ HashOutput)] := mul_one _
                    _ ≤ outputCard⁻¹ := by rw [probOutput_uniformSample]
                    _ ≤ outputCard⁻¹ + _ := le_add_right le_rfl
                · simp only [heq, ite_false, zero_add]
                  exact mul_le_mul' le_rfl (hrest output heq)
            _ = (∑' output : HashOutput,
                  if output = target then outputCard⁻¹ else 0) +
                (∑' output : HashOutput,
                  Pr[= output | ($ᵗ HashOutput)]) *
                  (((q - 1 : Nat) : ℝ≥0∞) * outputCard⁻¹) := by
              rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
            _ ≤ outputCard⁻¹ + 1 * (((q - 1 : Nat) : ℝ≥0∞) * outputCard⁻¹) := by
              apply add_le_add
              · rw [tsum_eq_single target (by intro output hne; rw [if_neg hne])]
                rw [if_pos rfl]
              · exact mul_le_mul' tsum_probOutput_le_one le_rfl
            _ = (q : ℝ≥0∞) * outputCard⁻¹ := by
              have hqpos : 0 < q := by simpa using hbound.1
              have hqone : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hqpos)
              rw [one_mul, ← one_add_mul, ← Nat.cast_one, ← Nat.cast_add,
                Nat.add_sub_cancel' hqone]
            _ = (q : ℝ≥0∞) / ((2 ^ hashOutputBits : Nat) : ℝ≥0∞) := by
              rw [hcard, div_eq_mul_inv]

/-- A later computation creates a cache entry with one fixed 128-bit truncation, even if that digest already occurs in the initial cache. -/
theorem mixed_truncated_output_fresh_hit_from_cache_le {α : Type}
    (computation : OracleComp OracleWorld α) (q : Nat)
    (hbound : computation.IsQueryBoundP (· matches .inr _) q)
    (target : Digest) (cache : QueryCache HashSpec) :
    Pr[fun result => ∃ input output,
        result.2 input = some output ∧ cache input = none ∧ truncateHash output = target |
      (simulateQ xmssRomImpl computation).run cache] ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  let experiment := (simulateQ xmssRomImpl computation).run cache
  have hevent :
      (fun result : α × QueryCache HashSpec => ∃ input output,
        result.2 input = some output ∧ cache input = none ∧ truncateHash output = target) =
      (fun result : α × QueryCache HashSpec => ∃ output ∈ matchingOutputs target, ∃ input,
        result.2 input = some output ∧ cache input = none) := by
    funext result
    apply propext
    constructor
    · rintro ⟨input, output, hfinal, hinitial, htruncate⟩
      exact ⟨output, by simp [matchingOutputs, htruncate], input, hfinal, hinitial⟩
    · rintro ⟨output, houtput, input, hfinal, hinitial⟩
      exact ⟨input, output, hfinal, hinitial, (Finset.mem_filter.mp houtput).2⟩
  rw [hevent]
  calc
    Pr[fun result => ∃ output ∈ matchingOutputs target, ∃ input,
          result.2 input = some output ∧ cache input = none | experiment] ≤
        ∑ output ∈ matchingOutputs target,
          Pr[fun result => ∃ input,
            result.2 input = some output ∧ cache input = none | experiment] :=
      probEvent_exists_finset_le_sum (matchingOutputs target) experiment
        (fun output result => ∃ input, result.2 input = some output ∧ cache input = none)
    _ ≤ ∑ _output ∈ matchingOutputs target,
          (q : ℝ≥0∞) / ((2 ^ hashOutputBits : Nat) : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro output _
      exact mixed_exact_output_fresh_hit_from_cache_le computation q hbound output cache
    _ = ((2 ^ digestBits : Nat) : ℝ≥0∞) *
          ((q : ℝ≥0∞) / ((2 ^ hashOutputBits : Nat) : ℝ≥0∞)) := by
      rw [Finset.sum_const, nsmul_eq_mul, card_matchingOutputs]
    _ = (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
      have hzero : ((2 ^ digestBits : Nat) : ℝ≥0∞) ≠ 0 := by positivity
      have htop : ((2 ^ digestBits : Nat) : ℝ≥0∞) ≠ ∞ := by simp
      rw [hashOutputBits_eq, Nat.pow_add, Nat.cast_mul, div_eq_mul_inv,
        ENNReal.mul_inv (Or.inl hzero) (Or.inl htop)]
      calc
        ((2 ^ digestBits : Nat) : ℝ≥0∞) *
            ((q : ℝ≥0∞) *
              (((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ *
                ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹)) =
            (((2 ^ digestBits : Nat) : ℝ≥0∞) *
              ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) *
              ((q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) := by ac_rfl
        _ = (q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
          rw [ENNReal.mul_inv_cancel hzero htop, one_mul]

def FreshDigestCollisionWith (initialCache finalCache : QueryCache HashSpec)
    (targetInput : HashInput) : Prop :=
  ∃ input output,
    finalCache input = some output ∧ initialCache input = none ∧
      Concrete.CacheView.digestAt finalCache input =
        Concrete.CacheView.digestAt finalCache targetInput

/-- Once one side of a targeted collision is cached, producing a fresh colliding side costs at most `q / 2^128`. -/
theorem mixed_freshDigestCollisionWith_le {α : Type}
    (computation : OracleComp OracleWorld α) (q : Nat)
    (hbound : computation.IsQueryBoundP (· matches .inr _) q)
    (cache : QueryCache HashSpec) (targetInput : HashInput) (targetOutput : HashOutput)
    (htarget : cache targetInput = some targetOutput) (win : α × QueryCache HashSpec → Prop)
    (hwin : ∀ result ∈ support ((simulateQ xmssRomImpl computation).run cache),
      win result → FreshDigestCollisionWith cache result.2 targetInput) :
    Pr[win | (simulateQ xmssRomImpl computation).run cache] ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  let experiment := (simulateQ xmssRomImpl computation).run cache
  calc
    Pr[win | experiment] ≤
        Pr[fun result => FreshDigestCollisionWith cache result.2 targetInput |
          experiment] := probEvent_mono hwin
    _ ≤ Pr[fun result => ∃ input output,
          result.2 input = some output ∧ cache input = none ∧
            truncateHash output = truncateHash targetOutput | experiment] := by
      apply probEvent_mono
      intro result hresult
      rintro ⟨input, output, houtput, hfresh, hcollision⟩
      have htargetFinal := xmssRom_cache_le computation cache result hresult htarget
      refine ⟨input, output, houtput, hfresh, ?_⟩
      calc
        truncateHash output = Concrete.CacheView.digestAt result.2 input :=
          (Concrete.CacheView.digestAt_eq_of_cache_eq_some houtput).symm
        _ = Concrete.CacheView.digestAt result.2 targetInput := hcollision
        _ = truncateHash targetOutput :=
          Concrete.CacheView.digestAt_eq_of_cache_eq_some htargetFinal
    _ ≤ (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) :=
      mixed_truncated_output_fresh_hit_from_cache_le computation q hbound
        (truncateHash targetOutput) cache

end XmssSecurity.Rom

import XmssSecurity.Execution
import XmssSecurity.RandomOracle
import XmssSecurity.SecurityBudget
import VCVio.OracleComp.QueryTracking.Unpredictability

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Rom

noncomputable local instance : IsUniformSpec HashSpec :=
  IsUniformSpec.ofFintypeInhabited _

/-- A fixed 256-bit target remains hard to hit when arbitrary public sampling is interleaved with the bounded hash queries. -/
theorem mixed_exact_output_hit_from_cache_le {α : Type}
    (computation : OracleComp OracleWorld α) (q : Nat)
    (hbound : computation.IsQueryBoundP (· matches .inr _) q)
    (target : HashOutput) (cache : QueryCache HashSpec)
    (habsent : ∀ input, cache input ≠ some target) :
    Pr[fun result => ∃ input, result.2 input = some target |
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
      obtain ⟨input, hcache⟩ := hhit
      exact habsent input hcache
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
        exact ih sampled q (by simpa using hbound.2 sampled) cache habsent
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
          exact ih output (q - 1) (by simpa using hbound.2 output) cache habsent |>.trans (by
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
                    result.2 input = some target |
                (simulateQ xmssRomImpl (next output)).run
                  (cache.cacheQuery hashInput output)] ≤
                ((q - 1 : Nat) : ℝ≥0∞) * outputCard⁻¹ := by
            intro output hne
            refine (ih output (q - 1) (by simpa using hbound.2 output)
              (cache.cacheQuery hashInput output) ?_).trans_eq ?_
            · intro input
              by_cases heq : input = hashInput
              · subst input
                rw [QueryCache.cacheQuery_self]
                simpa using hne
              · rw [QueryCache.cacheQuery_of_ne _ _ heq]
                exact habsent input
            · rw [hcard, div_eq_mul_inv]
          calc
            ∑' output, Pr[= output | ($ᵗ HashOutput)] *
                Pr[fun result => ∃ input,
                    result.2 input = some target |
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
                            result.2 input = some target |
                          (simulateQ xmssRomImpl (next target)).run
                            (cache.cacheQuery hashInput target)] ≤
                      Pr[= target | ($ᵗ HashOutput)] * 1 :=
                        mul_le_mul' le_rfl probEvent_le_one
                    _ = Pr[= target | ($ᵗ HashOutput)] :=
                      mul_one _
                    _ ≤ outputCard⁻¹ := by
                      rw [probOutput_uniformSample]
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

/-- The mixed public-randomness game hits a previously absent 128-bit truncation with probability at most `q / 2^128`. -/
theorem mixed_truncated_output_hit_from_cache_le {α : Type}
    (computation : OracleComp OracleWorld α) (q : Nat)
    (hbound : computation.IsQueryBoundP (· matches .inr _) q)
    (target : Digest) (cache : QueryCache HashSpec)
    (habsent : ∀ input output, cache input = some output → truncateHash output ≠ target) :
    Pr[fun result => ∃ input output,
        result.2 input = some output ∧ truncateHash output = target |
      (simulateQ xmssRomImpl computation).run cache] ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  let experiment := (simulateQ xmssRomImpl computation).run cache
  have hevent :
      (fun result : α × QueryCache HashSpec => ∃ input output,
        result.2 input = some output ∧ truncateHash output = target) =
      (fun result : α × QueryCache HashSpec => ∃ output ∈ matchingOutputs target, ∃ input,
        result.2 input = some output) := by
    funext result
    apply propext
    constructor
    · rintro ⟨input, output, hfinal, htruncate⟩
      exact ⟨output, by simp [matchingOutputs, htruncate], input, hfinal⟩
    · rintro ⟨output, houtput, input, hfinal⟩
      exact ⟨input, output, hfinal, (Finset.mem_filter.mp houtput).2⟩
  rw [hevent]
  calc
    Pr[fun result => ∃ output ∈ matchingOutputs target, ∃ input,
          result.2 input = some output | experiment] ≤
        ∑ output ∈ matchingOutputs target,
          Pr[fun result => ∃ input, result.2 input = some output | experiment] :=
      probEvent_exists_finset_le_sum (matchingOutputs target) experiment
        (fun output result => ∃ input, result.2 input = some output)
    _ ≤ ∑ _output ∈ matchingOutputs target,
          (q : ℝ≥0∞) / ((2 ^ hashOutputBits : Nat) : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro output houtput
      apply mixed_exact_output_hit_from_cache_le computation q hbound output cache
      intro input hcache
      exact habsent input output hcache (Finset.mem_filter.mp houtput).2
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

/-- Direct specialization of the mixed truncation bound to the full signature game. -/
theorem game_truncated_output_hit_le (scheme : Scheme) (adversary : Adversary scheme)
    (q : Nat) (hbound : HasHashQueryBound scheme adversary q) (target : Digest) :
    Pr[fun result => ∃ input output,
        result.2 input = some output ∧ truncateHash output = target |
      gameWithCache scheme adversary] ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  simpa [gameWithCache] using mixed_truncated_output_hit_from_cache_le
    (gameCore scheme adversary) q hbound target ∅ (by simp)

/-- If every winning trace hits one fixed truncated target, its forging advantage has the 128-bit bound. -/
theorem forgeAdvantage_le_of_implies_truncated_hit
    (scheme : Scheme) (adversary : Adversary scheme) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (target : Digest)
    (hwin : ∀ result ∈ support (gameWithCache scheme adversary), result.1 = true →
      ∃ input output, result.2 input = some output ∧ truncateHash output = target) :
    forgeAdvantage scheme adversary ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  rw [forgeAdvantage_eq_gameWithCache]
  exact (probEvent_mono hwin).trans
    (game_truncated_output_hit_le scheme adversary q hbound target)

/-- A static set of at most 175 truncated targets in the full game fits within the 120-bit budget. -/
theorem game_truncated_targets_hit_le
    (scheme : Scheme) (adversary : Adversary scheme) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (targets : Finset Digest)
    (hcard : targets.card ≤ totalBadEventSlots) :
    Pr[fun result => ∃ input output,
        result.2 input = some output ∧ truncateHash output ∈ targets |
      gameWithCache scheme adversary] ≤
      (q : ℝ≥0∞) / ((2 ^ targetSecurityBits : Nat) : ℝ≥0∞) := by
  let experiment := gameWithCache scheme adversary
  have hevent :
      (fun result : Bool × QueryCache HashSpec => ∃ input output,
        result.2 input = some output ∧ truncateHash output ∈ targets) =
      (fun result : Bool × QueryCache HashSpec => ∃ target ∈ targets, ∃ input output,
        result.2 input = some output ∧ truncateHash output = target) := by
    funext result
    apply propext
    constructor
    · rintro ⟨input, output, houtput, htarget⟩
      exact ⟨truncateHash output, htarget, input, output, houtput, rfl⟩
    · rintro ⟨target, htarget, input, output, houtput, heq⟩
      exact ⟨input, output, houtput, heq ▸ htarget⟩
  rw [hevent]
  calc
    Pr[fun result => ∃ target ∈ targets, ∃ input output,
          result.2 input = some output ∧ truncateHash output = target | experiment] ≤
        ∑ target ∈ targets,
          Pr[fun result => ∃ input output,
            result.2 input = some output ∧ truncateHash output = target | experiment] :=
      probEvent_exists_finset_le_sum targets experiment
        (fun target result => ∃ input output,
          result.2 input = some output ∧ truncateHash output = target)
    _ ≤ ∑ _target ∈ targets,
          (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro target _
      exact game_truncated_output_hit_le scheme adversary q hbound target
    _ = (targets.card : ℝ≥0∞) *
          ((q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (totalBadEventSlots : ℝ≥0∞) *
          ((q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)) := by
      gcongr
    _ ≤ (q : ℝ≥0∞) / ((2 ^ targetSecurityBits : Nat) : ℝ≥0∞) :=
      totalBadEventSlots_budget_le_120 q

/-- A fixed-target classification of every winning trace closes the full 120-bit game bound. -/
theorem forgeAdvantage_le_of_implies_truncated_targets_hit
    (scheme : Scheme) (adversary : Adversary scheme) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (targets : Finset Digest)
    (hcard : targets.card ≤ totalBadEventSlots)
    (hwin : ∀ result ∈ support (gameWithCache scheme adversary), result.1 = true →
      ∃ input output, result.2 input = some output ∧ truncateHash output ∈ targets) :
    forgeAdvantage scheme adversary ≤
      (q : ℝ≥0∞) / ((2 ^ targetSecurityBits : Nat) : ℝ≥0∞) := by
  rw [forgeAdvantage_eq_gameWithCache]
  exact (probEvent_mono hwin).trans
    (game_truncated_targets_hit_le scheme adversary q hbound targets hcard)

end XmssSecurity.Rom

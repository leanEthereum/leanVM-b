import SphincsSecurity.Proof.DigestSelectionMass

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
noncomputable local instance : SampleableType Randomness := SampleableType.ofFintype Randomness
attribute [local irreducible] signAttempt signDigestAttemptPrefix

theorem cachedDigestAttemptRate_eq_count (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (P : FewTimeView → Prop) :
    cachedDigestAttemptRate key message cache P =
      cachedMessageEntryCountWhere cache key.parameter key.root message P * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ := by
  let hit : Randomness → Prop := fun randomness => ∃ output,
    cache (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) = some output ∧
      signAttemptResultOfOutput output ≠ none ∧ P (hashOutputFewTimeView output)
  let targets : Finset Randomness := Finset.univ.filter hit
  let fiber := cachedMessageInputSetWhere cache key.parameter key.root message P
  let embedding : (targets : Set Randomness) ↪ fiber :=
    ⟨fun randomness =>
      ⟨⟨tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness.1),
          Classical.choose (Finset.mem_filter.mp randomness.2).2⟩,
        ⟨⟨(Classical.choose_spec (Finset.mem_filter.mp randomness.2).2).1, ⟨randomness.1, rfl⟩⟩,
          (Classical.choose_spec (Finset.mem_filter.mp randomness.2).2).2⟩⟩,
      fun left right heq => Subtype.ext <|
        (messageDigestPayload_injective key.root <|
          (tweakableHashInput_injective key.parameter (by trivial) (by trivial) <|
            congrArg (fun entry : fiber => entry.1.1) heq).2).2⟩
  have hsurjective : Function.Surjective embedding := by
    rintro ⟨⟨input, output⟩, ⟨hcached, randomness, hinput⟩, hadmissible, hP⟩
    change input = tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness) at hinput
    subst input
    have hh : hit randomness := ⟨output, hcached, hadmissible, hP⟩
    let target : (targets : Set Randomness) := ⟨randomness, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩⟩
    refine ⟨target, Subtype.ext ?_⟩
    have hout := Option.some.inj ((Classical.choose_spec (Finset.mem_filter.mp target.2).2).1.symm.trans hcached)
    exact Sigma.ext (by rfl) (heq_of_eq hout)
  have hcard : (targets.card : ENNReal) = cachedMessageEntryCountWhere cache key.parameter key.root message P := by
    have h := Set.encard_congr (Equiv.ofBijective embedding ⟨embedding.injective, hsurjective⟩)
    simpa only [cachedMessageEntryCountWhere, fiber, Set.encard_coe_eq_coe_finsetCard, ENat.toENNReal_coe] using
      congrArg ENat.toENNReal h
  rw [cachedDigestAttemptRate, probEvent_uniformSample, card_randomness, div_eq_mul_inv]
  change (targets.card : ENNReal) * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ = _
  rw [hcard]

noncomputable def exactDigestReuseWeight (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) : ENNReal :=
  digestAttemptExpectation digestAttemptLimit key message cache * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹

theorem exactDigestReuseWeight_ne_top (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    exactDigestReuseWeight key message cache ≠ ⊤ :=
  ENNReal.mul_ne_top (digestAttemptExpectation_ne_top digestAttemptLimit key message cache) (by finiteness)

theorem digestAttemptExpectation_mul_inv_le_of_budget
    (attempts : Nat) (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (budget : Nat) (rate weight : ENNReal)
    (hrate : rate ≤ (1 - (budget : ENNReal) * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹) *
      ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹)
    (hweight : ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ + (1 - rate) * weight ≤ weight)
    (hbudget : QueryCache.enncard cache + (attempts : ENNReal) ≤ budget) :
    digestAttemptExpectation attempts key message cache * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ ≤ weight := by
  induction attempts generalizing cache with
  | zero => simp only [digestAttemptExpectation, zero_mul]; exact zero_le
  | succ attempts ih =>
      rw [digestAttemptExpectation, add_mul, one_mul, ← ENNReal.tsum_mul_right]
      have hcontinuation :
          (∑' result, (Pr[= result | signDigestAttemptPrefix key message cache] *
            if result.2.1 = none then digestAttemptExpectation attempts key message result.2.2 else 0) *
              ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹) ≤
          Pr[fun result => result.2.1 = none | signDigestAttemptPrefix key message cache] * weight := by
        rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
        apply ENNReal.tsum_le_tsum
        intro result
        by_cases hr : result ∈ support (signDigestAttemptPrefix key message cache)
        · by_cases hnone : result.2.1 = none
          · rw [if_pos hnone, if_pos hnone, mul_assoc]
            apply mul_le_mul' le_rfl
            apply ih
            have hgrowth := signAttempt_enncard_le key message result.1 cache result.2
              (signDigestAttemptPrefix_support_attempt key message cache result hr)
            calc
              QueryCache.enncard result.2.2 + (attempts : ENNReal) ≤
                  (QueryCache.enncard cache + 1) + (attempts : ENNReal) := add_le_add hgrowth le_rfl
              _ = QueryCache.enncard cache + ((attempts + 1 : Nat) : ENNReal) := by push_cast; ring
              _ ≤ _ := hbudget
          · simp only [if_neg hnone, mul_zero, zero_mul, le_refl]
        · simp only [probOutput_eq_zero_of_not_mem_support hr, zero_mul, ite_self, le_refl]
      apply (add_le_add le_rfl hcontinuation).trans
      apply le_trans _ hweight
      exact add_le_add le_rfl (mul_le_mul'
        (probEvent_signDigestAttemptPrefix_retry_le_of_budget key message cache budget
          ((le_add_right le_rfl).trans hbudget) rate hrate) le_rfl)

theorem exactDigestReuseWeight_le_digestReuseWeight
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    exactDigestReuseWeight key message cache ≤ digestReuseWeight q := by
  let rate : ENNReal := (1 - ((q + digestAttemptLimit : Nat) : ENNReal) *
    ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹) * ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹
  have hbudget : QueryCache.enncard cache + (digestAttemptLimit : ENNReal) ≤ (q + digestAttemptLimit : Nat) := by
    simpa only [Nat.cast_add] using add_le_add hcache (le_refl (digestAttemptLimit : ENNReal))
  have hpositive : rate ≠ 0 := by
    apply digestRaceSuccessRate_ne_zero_of_budget_lt
    norm_num [digestAttemptLimit, randomnessBits] at *
    omega
  have hrateOne : rate ≤ 1 :=
    (probEvent_signDigestAttemptPrefix_success_ge_of_budget key message cache (q + digestAttemptLimit)
      ((le_add_right le_rfl).trans hbudget)).trans probEvent_le_one
  exact digestAttemptExpectation_mul_inv_le_of_budget digestAttemptLimit key message cache
    (q + digestAttemptLimit) rate _ le_rfl
    (prehit_race_weight_div_success rate hpositive (ne_top_of_le_ne_top (by simp) hrateOne) hrateOne).le hbudget

theorem probEvent_signDigestLoop_prehit_eq_count_mul_exactWeight
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) (P : FewTimeView → Prop) :
    Pr[PrehitSelectedView cache key message P |
      (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache] =
      cachedMessageEntryCountWhere cache key.parameter key.root message P * exactDigestReuseWeight key message cache := by
  rw [probEvent_signDigestLoop_prehit_eq_rate_mul_attempts digestAttemptLimit key message cache cache le_rfl,
    cachedDigestAttemptRate_eq_count, exactDigestReuseWeight]
  ring

theorem freshSelection_add_count_exactWeight_add_exhaustion (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    freshDigestSelectionProbability key message cache +
      cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) * exactDigestReuseWeight key message cache +
      digestExhaustionProbability key message cache = 1 := by
  have h := freshSelection_add_cachedAttempts_add_exhaustion key message cache
  rw [cachedDigestAttemptRate_eq_count] at h
  unfold exactDigestReuseWeight
  convert h using 1; ring

end SphincsSecurity.Concrete

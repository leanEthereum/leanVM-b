import XmssSecurity.ChainValueUniformity

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

noncomputable local instance chainTrajectorySampleableDigest : SampleableType Digest :=
  SampleableType.ofFintype Digest

@[simp]
theorem Vector.back_push {n : Nat} (values : Vector α n) (value : α) :
    (values.push value).back = value := by
  symm
  exact Vector.back_eq_of_push_eq (Vector.push_pop_back (values.push value)).symm

def Concrete.chainTrajectory
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (position : Nat) : (steps : Nat) → Digest →
      OracleComp HashSpec (Vector Digest (steps + 1))
  | 0, value => pure (Vector.ofFn fun _ => value)
  | steps + 1, value => do
      let values ← chainTrajectory parameter epoch chain position steps value
      if hvalid : position + steps < chainLength - 1 then
        let next ← Concrete.chainHash parameter epoch chain
          ⟨position + steps, hvalid⟩ values.back
        return values.push next
      else
        return values.push 0

@[simp]
theorem Concrete.chainTrajectory_zero
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (position : Nat) (value : Digest) :
    Concrete.chainTrajectory parameter epoch chain position 0 value =
      pure (Vector.ofFn fun _ => value) := rfl

theorem Concrete.chainTrajectory_succ
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (position steps : Nat) (value : Digest) :
    Concrete.chainTrajectory parameter epoch chain position (steps + 1) value = (do
      let values ← Concrete.chainTrajectory parameter epoch chain position steps value
      if hvalid : position + steps < chainLength - 1 then
        let next ← Concrete.chainHash parameter epoch chain
          ⟨position + steps, hvalid⟩ values.back
        return values.push next
      else
        return values.push 0) := rfl

@[simp]
theorem Concrete.chainTrajectory_back
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (epoch : Epoch) (chain : ChainIndex) (position steps : Nat)
    (value : Digest) :
    (evalWithAnswerFn (Concrete.CacheReplay.answerFn cache)
      (Concrete.chainTrajectory parameter epoch chain position steps value)).back =
      Wots.walk (Concrete.CacheView.chainStep cache parameter epoch chain)
        position steps value := by
  induction steps with
  | zero =>
      change value = value
      rfl
  | succ steps ih =>
      rw [Concrete.chainTrajectory_succ]
      simp only [evalWithAnswerFn_bind, ih, Wots.walk]
      split <;> simp_all [Concrete.chainHash, Concrete.CacheView.chainStep,
        Concrete.CacheView.chainInput, Concrete.CacheView.tweakableHash]

theorem Concrete.chainTrajectory_getElem
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (epoch : Epoch) (chain : ChainIndex) (position steps offset : Nat)
    (value : Digest) (hoffset : offset < steps + 1) :
    (evalWithAnswerFn (Concrete.CacheReplay.answerFn cache)
      (Concrete.chainTrajectory parameter epoch chain position steps value))[offset] =
      Wots.walk (Concrete.CacheView.chainStep cache parameter epoch chain)
        position offset value := by
  induction steps generalizing offset with
  | zero =>
      have : offset = 0 := by omega
      subst offset
      rfl
  | succ steps ih =>
      rw [Concrete.chainTrajectory_succ]
      simp only [evalWithAnswerFn_bind]
      split <;> rename_i hvalid
      · simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
        by_cases hlower : offset < steps + 1
        · rw [Vector.getElem_push_lt]
          exact ih offset hlower
        · have hlast : offset = steps + 1 := by omega
          subst offset
          rw [Vector.getElem_push_eq, Concrete.chainTrajectory_back]
          simp [Wots.walk, hvalid, Concrete.chainHash,
            Concrete.CacheView.chainStep, Concrete.CacheView.chainInput,
            Concrete.CacheView.tweakableHash]
      · simp only [evalWithAnswerFn_pure]
        by_cases hlower : offset < steps + 1
        · rw [Vector.getElem_push_lt]
          exact ih offset hlower
        · have hlast : offset = steps + 1 := by omega
          subst offset
          rw [Vector.getElem_push_eq]
          simp [Wots.walk, Concrete.CacheView.chainStep, hvalid]

theorem Concrete.chainTrajectory_queryBound_zero_of_avoids
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (position steps : Nat) (value : Digest) (targetDomain : HashDomain)
    (havoid : ∀ offset, offset < steps →
      ∀ hvalid : position + offset < chainLength - 1,
        HashDomain.chain epoch chain ⟨position + offset, hvalid⟩ ≠ targetDomain) :
    (Concrete.chainTrajectory parameter epoch chain position steps value).IsQueryBoundP
      (AtHashAddress parameter targetDomain) 0 := by
  induction steps with
  | zero => simp [Concrete.chainTrajectory]
  | succ steps ih =>
      rw [Concrete.chainTrajectory_succ]
      refine OracleComp.isQueryBoundP_bind (m := 0)
        (ih fun offset hoffset => havoid offset (by omega)) ?_
      intro values _
      split
      · exact OracleComp.isQueryBoundP_bind (m := 0)
          (Concrete.tweakableHash_queryBound_atOtherAddress parameter targetDomain
            (.chain epoch chain ⟨position + steps, by assumption⟩)
            (Concrete.digestBytes values.back) (havoid steps (by omega) _))
          (fun next _ => OracleComp.isQueryBoundP_pure
            (p := AtHashAddress parameter targetDomain) (values.push next) 0)
      · exact OracleComp.isQueryBoundP_pure
          (p := AtHashAddress parameter targetDomain) (values.push 0) 0

theorem Concrete.chainTrajectory_succ_probability
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (epoch : Epoch) (chain : ChainIndex) (position steps : Nat)
    (value : Digest) (targetValues : Vector Digest (steps + 1))
    (targetNext : Digest)
    (hvalid : position + steps < chainLength - 1)
    (habsent : ∀ input,
      AtHashAddress parameter (.chain epoch chain ⟨position + steps, hvalid⟩) input →
        cache input = none) :
    Pr[fun result : Vector Digest (steps + 2) × QueryCache HashSpec =>
        result.1 = targetValues.push targetNext |
      (simulateQ randomOracle
        (Concrete.chainTrajectory parameter epoch chain position (steps + 1) value)).run cache] =
      Pr[fun result : Vector Digest (steps + 1) × QueryCache HashSpec =>
          result.1 = targetValues |
        (simulateQ randomOracle
          (Concrete.chainTrajectory parameter epoch chain position steps value)).run cache] *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  rw [Concrete.chainTrajectory_succ]
  simp only [hvalid, ↓reduceDIte]
  rw [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum]
  rw [probEvent_eq_tsum_ite
    ((simulateQ randomOracle
      (Concrete.chainTrajectory parameter epoch chain position steps value)).run cache)
    (fun result => result.1 = targetValues)]
  rw [← ENNReal.tsum_mul_right]
  apply tsum_congr
  rintro ⟨values, resultCache⟩
  by_cases hvalues : values = targetValues
  · subst values
    by_cases hmem : (targetValues, resultCache) ∈ support
        ((simulateQ randomOracle
          (Concrete.chainTrajectory parameter epoch chain position steps value)).run cache)
    · have hfresh : resultCache
          (Concrete.CacheView.chainInput parameter epoch chain
            ⟨position + steps, hvalid⟩ targetValues.back) = none := by
        apply Concrete.CacheReplay.cache_none_of_zero_query_bound
          (Concrete.chainTrajectory parameter epoch chain position steps value)
          (Concrete.CacheView.chainInput parameter epoch chain
            ⟨position + steps, hvalid⟩ targetValues.back)
          cache resultCache targetValues
        · apply OracleComp.IsQueryBoundP.of_imp
            (p' := AtHashAddress parameter
              (.chain epoch chain ⟨position + steps, hvalid⟩))
          · intro input heq
            subst input
            exact (atHashAddress_tweakableHashInput_iff parameter _ _ _).2 rfl
          · apply Concrete.chainTrajectory_queryBound_zero_of_avoids
            intro offset hoffset hoffsetValid heq
            simp only [HashDomain.chain.injEq, Fin.mk.injEq] at heq
            omega
        · exact habsent _
            ((atHashAddress_tweakableHashInput_iff parameter _ _ _).2 rfl)
        · exact hmem
      have hnext := Concrete.chainHash_fresh_probability resultCache parameter epoch chain
        ⟨position + steps, hvalid⟩ targetValues.back targetNext hfresh
      simp only
      congr 1
      rw [show (simulateQ randomOracle
            (Concrete.chainHash parameter epoch chain ⟨position + steps, hvalid⟩
              targetValues.back >>= fun next => pure (targetValues.push next))).run resultCache =
          (fun result : Digest × QueryCache HashSpec =>
            (targetValues.push result.1, result.2)) <$>
            (simulateQ randomOracle
              (Concrete.chainHash parameter epoch chain ⟨position + steps, hvalid⟩
                targetValues.back)).run resultCache by
        simp [simulateQ_bind, StateT.run_bind, map_eq_bind_pure_comp]]
      rw [probEvent_map]
      calc
        Pr[(fun result => result.1 = targetValues.push targetNext) ∘
              (fun result : Digest × QueryCache HashSpec =>
                (targetValues.push result.1, result.2)) |
            (simulateQ randomOracle
              (Concrete.chainHash parameter epoch chain
                ⟨position + steps, hvalid⟩ targetValues.back)).run resultCache] =
            Pr[fun result : Digest × QueryCache HashSpec => result.1 = targetNext |
              (simulateQ randomOracle
                (Concrete.chainHash parameter epoch chain
                  ⟨position + steps, hvalid⟩ targetValues.back)).run resultCache] := by
              apply probEvent_congr' (fun result _ => ?_) rfl
              simp only [Function.comp_apply, Vector.push_inj_right]
        _ = ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := hnext
    · rw [probOutput_eq_zero_of_not_mem_support hmem]
      simp
  · have hzero : Pr[fun result : Vector Digest (steps + 2) × QueryCache HashSpec =>
        result.1 = targetValues.push targetNext |
      (simulateQ randomOracle
        (Concrete.chainHash parameter epoch chain ⟨position + steps, hvalid⟩ values.back >>=
          fun next => pure (values.push next))).run resultCache] = 0 := by
      apply probEvent_eq_zero
      intro result hresult heq
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hresult
      obtain ⟨⟨next, middleCache⟩, _hnext, hpure⟩ := hresult
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hpure
      subst result
      exact hvalues (Vector.pop_eq_of_push_eq heq)
    rw [hzero]
    simp [hvalues]

theorem Concrete.chainTrajectory_succ_probOutput_empty
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (position steps : Nat) (value : Digest)
    (targetValues : Vector Digest (steps + 1)) (targetNext : Digest)
    (hvalid : position + steps < chainLength - 1) :
    Pr[= targetValues.push targetNext |
      (simulateQ randomOracle
        (Concrete.chainTrajectory parameter epoch chain position (steps + 1) value)).run' ∅] =
      Pr[= targetValues |
        (simulateQ randomOracle
          (Concrete.chainTrajectory parameter epoch chain position steps value)).run' ∅] *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  calc
    Pr[= targetValues.push targetNext |
        (simulateQ randomOracle
          (Concrete.chainTrajectory parameter epoch chain position (steps + 1) value)).run' ∅] =
        Pr[fun result : Vector Digest (steps + 2) × QueryCache HashSpec =>
            result.1 = targetValues.push targetNext |
          (simulateQ randomOracle
            (Concrete.chainTrajectory parameter epoch chain position (steps + 1) value)).run ∅] := by
              rw [← probEvent_eq_eq_probOutput, StateT.run'_eq, probEvent_map]
              rfl
    _ = Pr[fun result : Vector Digest (steps + 1) × QueryCache HashSpec =>
          result.1 = targetValues |
        (simulateQ randomOracle
          (Concrete.chainTrajectory parameter epoch chain position steps value)).run ∅] *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ :=
      Concrete.chainTrajectory_succ_probability ∅ parameter epoch chain position steps
        value targetValues targetNext hvalid (by simp)
    _ = Pr[= targetValues |
        (simulateQ randomOracle
          (Concrete.chainTrajectory parameter epoch chain position steps value)).run' ∅] *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
      congr 1
      rw [← probEvent_eq_eq_probOutput, StateT.run'_eq, probEvent_map]
      rfl

noncomputable def Concrete.isolatedChainTrajectoryExperiment
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (position steps : Nat) : ProbComp (Vector Digest (steps + 1)) := do
  let value ← $ᵗ Digest
  (simulateQ randomOracle
    (Concrete.chainTrajectory parameter epoch chain position steps value)).run' ∅

theorem Concrete.isolatedChainTrajectoryExperiment_succ_probability
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (position steps : Nat) (targetValues : Vector Digest (steps + 1))
    (targetNext : Digest) (hvalid : position + steps < chainLength - 1) :
    Pr[= targetValues.push targetNext |
      Concrete.isolatedChainTrajectoryExperiment parameter epoch chain position (steps + 1)] =
      Pr[= targetValues |
        Concrete.isolatedChainTrajectoryExperiment parameter epoch chain position steps] *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  unfold Concrete.isolatedChainTrajectoryExperiment
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  simp_rw [Concrete.chainTrajectory_succ_probOutput_empty parameter epoch chain position steps
    _ targetValues targetNext hvalid]
  calc
    (∑' value : Digest, Pr[= value | $ᵗ Digest] *
        (Pr[= targetValues |
          (simulateQ randomOracle
            (Concrete.chainTrajectory parameter epoch chain position steps value)).run' ∅] *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹)) =
        ∑' value : Digest, (Pr[= value | $ᵗ Digest] *
          Pr[= targetValues |
            (simulateQ randomOracle
              (Concrete.chainTrajectory parameter epoch chain position steps value)).run' ∅]) *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
            apply tsum_congr
            intro value
            ring
    _ = (∑' value : Digest, Pr[= value | $ᵗ Digest] *
          Pr[= targetValues |
            (simulateQ randomOracle
              (Concrete.chainTrajectory parameter epoch chain position steps value)).run' ∅]) *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := ENNReal.tsum_mul_right

theorem Concrete.isolatedChainTrajectoryExperiment_zero_probability
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (position : Nat) (target : Vector Digest 1) :
    Pr[= target |
      Concrete.isolatedChainTrajectoryExperiment parameter epoch chain position 0] =
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  unfold Concrete.isolatedChainTrajectoryExperiment
  simp only [Concrete.chainTrajectory_zero, simulateQ_pure, StateT.run'_eq,
    StateT.run_pure, map_pure]
  rw [show target = Vector.ofFn (fun _ => target[0]) by
    ext index
    have : index = 0 := by omega
    subst index
    rfl]
  let singleton : Digest → Vector Digest 1 := fun value => Vector.ofFn fun _ => value
  change Pr[= singleton target[0] | singleton <$> ($ᵗ Digest)] = _
  rw [probOutput_map_injective]
  · exact HiddenValue.uniform_digest_point_probability target[0]
  · intro left right heq
    have hvalue := congrArg (fun values : Vector Digest 1 => values[0]) heq
    exact hvalue

theorem Concrete.isolatedChainTrajectoryExperiment_probability
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (position steps : Nat) (target : Vector Digest (steps + 1))
    (hvalid : position + steps ≤ chainLength - 1) :
    Pr[= target |
      Concrete.isolatedChainTrajectoryExperiment parameter epoch chain position steps] =
      (((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ^ (steps + 1) := by
  induction steps with
  | zero =>
      rw [Concrete.isolatedChainTrajectoryExperiment_zero_probability]
      simp
  | succ steps ih =>
      let targetValues : Vector Digest (steps + 1) := target.pop.cast (by omega)
      have htarget : targetValues.push target.back = target := by
        simpa [targetValues] using Vector.push_pop_back target
      rw [← htarget]
      rw [Concrete.isolatedChainTrajectoryExperiment_succ_probability]
      · rw [ih targetValues (by omega)]
        exact (pow_succ _ (steps + 1)).symm
      · omega

theorem Concrete.evalDist_isolatedChainTrajectoryExperiment_eq_uniform
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (position steps : Nat) (hvalid : position + steps ≤ chainLength - 1) :
    𝒟[Concrete.isolatedChainTrajectoryExperiment parameter epoch chain position steps] =
      𝒟[$ᵗ (Vector Digest (steps + 1))] := by
  apply SPMF.ext
  intro target
  change Pr[= target |
    Concrete.isolatedChainTrajectoryExperiment parameter epoch chain position steps] =
      Pr[= target | $ᵗ (Vector Digest (steps + 1))]
  rw [Concrete.isolatedChainTrajectoryExperiment_probability parameter epoch chain
    position steps target hvalid]
  have hcard : Fintype.card (Vector Digest (steps + 1)) =
      (2 ^ digestBits) ^ (steps + 1) := by
    let vectorEquiv : Vector Digest (steps + 1) ≃ (Fin (steps + 1) → Digest) :=
      { toFun := fun values index => values.get index
        invFun := Vector.ofFn
        left_inv := fun values => Vector.ext fun index hindex => by
          simp [Vector.get, Vector.ofFn]
        right_inv := fun values => funext fun index => by
          simp [Vector.get, Vector.ofFn] }
    rw [Fintype.card_congr vectorEquiv, Fintype.card_pi_const,
      HiddenValue.card_digest]
  rw [probOutput_uniformSample, hcard]
  simp only [Nat.cast_pow, Nat.cast_ofNat, ENNReal.inv_pow]

noncomputable def Concrete.sampledChainTrajectoryFromCache
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (epoch : Epoch) (chain : ChainIndex) (position steps : Nat) :
    ProbComp (Vector Digest (steps + 1) × QueryCache HashSpec) := do
  let value ← $ᵗ Digest
  (simulateQ randomOracle
    (Concrete.chainTrajectory parameter epoch chain position steps value)).run cache

theorem Concrete.sampledChainTrajectoryFromCache_succ_probability
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (epoch : Epoch) (chain : ChainIndex) (position steps : Nat)
    (targetValues : Vector Digest (steps + 1)) (targetNext : Digest)
    (hvalid : position + steps < chainLength - 1)
    (habsent : ∀ input,
      AtHashAddress parameter (.chain epoch chain ⟨position + steps, hvalid⟩) input →
        cache input = none) :
    Pr[fun result : Vector Digest (steps + 2) × QueryCache HashSpec =>
        result.1 = targetValues.push targetNext |
      Concrete.sampledChainTrajectoryFromCache cache parameter epoch chain position
        (steps + 1)] =
      Pr[fun result : Vector Digest (steps + 1) × QueryCache HashSpec =>
          result.1 = targetValues |
        Concrete.sampledChainTrajectoryFromCache cache parameter epoch chain position steps] *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  unfold Concrete.sampledChainTrajectoryFromCache
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  simp_rw [Concrete.chainTrajectory_succ_probability cache parameter epoch chain position steps
    _ targetValues targetNext hvalid habsent]
  calc
    (∑' value : Digest, Pr[= value | $ᵗ Digest] *
        (Pr[fun result : Vector Digest (steps + 1) × QueryCache HashSpec =>
            result.1 = targetValues |
          (simulateQ randomOracle
            (Concrete.chainTrajectory parameter epoch chain position steps value)).run cache] *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹)) =
        ∑' value : Digest, (Pr[= value | $ᵗ Digest] *
          Pr[fun result : Vector Digest (steps + 1) × QueryCache HashSpec =>
              result.1 = targetValues |
            (simulateQ randomOracle
              (Concrete.chainTrajectory parameter epoch chain position steps value)).run cache]) *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
            apply tsum_congr
            intro value
            ring
    _ = (∑' value : Digest, Pr[= value | $ᵗ Digest] *
          Pr[fun result : Vector Digest (steps + 1) × QueryCache HashSpec =>
              result.1 = targetValues |
            (simulateQ randomOracle
              (Concrete.chainTrajectory parameter epoch chain position steps value)).run cache]) *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := ENNReal.tsum_mul_right

theorem Concrete.sampledChainTrajectoryFromCache_zero_probability
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (epoch : Epoch) (chain : ChainIndex) (position : Nat)
    (target : Vector Digest 1) :
    Pr[fun result : Vector Digest 1 × QueryCache HashSpec => result.1 = target |
      Concrete.sampledChainTrajectoryFromCache cache parameter epoch chain position 0] =
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  unfold Concrete.sampledChainTrajectoryFromCache
  let singleton : Digest → Vector Digest 1 := fun value => Vector.ofFn fun _ => value
  change Pr[fun result : Vector Digest 1 × QueryCache HashSpec => result.1 = target |
    (fun value => (singleton value, cache)) <$> ($ᵗ Digest)] = _
  rw [probEvent_map]
  have htarget : target = singleton target[0] := by
    ext index
    have : index = 0 := by omega
    subst index
    rfl
  rw [htarget]
  have hevent : (fun value => singleton value = singleton target[0]) =
      (fun value => value = target[0]) := by
    funext value
    apply propext
    constructor
    · intro heq
      have hvalue := congrArg (fun values : Vector Digest 1 => values[0]) heq
      exact hvalue
    · intro heq
      rw [heq]
  change Pr[fun value : Digest => singleton value = singleton target[0] |
    $ᵗ Digest] = _
  rw [hevent]
  simpa only [probEvent_eq_eq_probOutput] using
    HiddenValue.uniform_digest_point_probability target[0]

theorem Concrete.sampledChainTrajectoryFromCache_probability
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (epoch : Epoch) (chain : ChainIndex) (position steps : Nat)
    (target : Vector Digest (steps + 1))
    (hvalid : position + steps ≤ chainLength - 1)
    (habsent : ∀ offset, offset < steps →
      ∀ hstep : position + offset < chainLength - 1,
        ∀ input, AtHashAddress parameter (.chain epoch chain
          ⟨position + offset, hstep⟩) input → cache input = none) :
    Pr[fun result : Vector Digest (steps + 1) × QueryCache HashSpec =>
        result.1 = target |
      Concrete.sampledChainTrajectoryFromCache cache parameter epoch chain position steps] =
      (((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ^ (steps + 1) := by
  induction steps with
  | zero =>
      rw [Concrete.sampledChainTrajectoryFromCache_zero_probability]
      simp
  | succ steps ih =>
      let targetValues : Vector Digest (steps + 1) := target.pop.cast (by omega)
      have htarget : targetValues.push target.back = target := by
        simpa [targetValues] using Vector.push_pop_back target
      rw [← htarget]
      rw [Concrete.sampledChainTrajectoryFromCache_succ_probability]
      · rw [ih targetValues (by omega) (fun offset hoffset => habsent offset (by omega))]
        exact (pow_succ _ (steps + 1)).symm
      · omega
      · exact habsent steps (by omega) _

end XmssSecurity

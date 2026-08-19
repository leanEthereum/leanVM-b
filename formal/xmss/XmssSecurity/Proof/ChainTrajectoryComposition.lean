import XmssSecurity.Proof.ChainTrajectoryUniformity

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

set_option linter.constructorNameAsVariable false in
theorem Concrete.sampledChainTrajectoryFromCache_preserves_other_epoch
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (epoch targetEpoch : Epoch) (chain : ChainIndex) (position steps : Nat)
    (hne : epoch ≠ targetEpoch)
    (habsent : ∀ targetStep : ChainStep, ∀ input,
      AtHashAddress parameter (.chain targetEpoch chain targetStep) input →
        cache input = none)
    (result : Vector Digest (steps + 1) × QueryCache HashSpec)
    (hresult : result ∈ support
      (Concrete.sampledChainTrajectoryFromCache cache parameter epoch chain position steps)) :
    ∀ targetStep : ChainStep, ∀ input,
      AtHashAddress parameter (.chain targetEpoch chain targetStep) input →
        result.2 input = none := by
  intro targetStep input hinput
  unfold Concrete.sampledChainTrajectoryFromCache Concrete.sampleChainSeed at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨value, _hvalue, htrajectory⟩ := hresult
  apply Concrete.CacheReplay.cache_none_of_zero_query_bound
    (Concrete.chainTrajectory parameter epoch chain position steps value)
    input cache result.2 result.1
  · apply OracleComp.IsQueryBoundP.of_imp
      (p' := AtHashAddress parameter (.chain targetEpoch chain targetStep))
    · intro candidate heq
      simpa only [heq] using hinput
    · apply Concrete.chainTrajectory_queryBound_zero_of_avoids
      intro offset hoffset hvalid heq
      simp only [HashDomain.chain.injEq] at heq
      exact hne heq.1
  · exact habsent targetStep input hinput
  · exact htrajectory

noncomputable def Concrete.sampledTwoChainTrajectoriesFromCache
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (firstEpoch secondEpoch : Epoch) (chain : ChainIndex) (position steps : Nat) :
    ProbComp ((Vector Digest (steps + 1) × Vector Digest (steps + 1)) ×
      QueryCache HashSpec) := do
  let first ← Concrete.sampledChainTrajectoryFromCache cache parameter firstEpoch chain
    position steps
  let second ← Concrete.sampledChainTrajectoryFromCache first.2 parameter secondEpoch chain
    position steps
  return ((first.1, second.1), second.2)

set_option maxHeartbeats 800000 in
set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem Concrete.sampledTwoChainTrajectoriesFromCache_probability
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (firstEpoch secondEpoch : Epoch) (chain : ChainIndex) (position steps : Nat)
    (hne : firstEpoch ≠ secondEpoch)
    (hvalid : position + steps ≤ chainLength - 1)
    (hfirstAbsent : ∀ step : ChainStep, ∀ input,
      AtHashAddress parameter (.chain firstEpoch chain step) input → cache input = none)
    (hsecondAbsent : ∀ step : ChainStep, ∀ input,
      AtHashAddress parameter (.chain secondEpoch chain step) input → cache input = none)
    (targetFirst targetSecond : Vector Digest (steps + 1)) :
    Pr[fun result :
        (Vector Digest (steps + 1) × Vector Digest (steps + 1)) × QueryCache HashSpec =>
        result.1 = (targetFirst, targetSecond) |
      Concrete.sampledTwoChainTrajectoriesFromCache cache parameter firstEpoch secondEpoch
        chain position steps] =
      (((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ^ (steps + 1) *
        (((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ^ (steps + 1) := by
  unfold Concrete.sampledTwoChainTrajectoriesFromCache
  rw [probEvent_bind_eq_tsum]
  let firstRun := Concrete.sampledChainTrajectoryFromCache cache parameter firstEpoch chain
    position steps
  let uniformTrajectory : ℝ≥0∞ :=
    (((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ^ (steps + 1)
  calc
    (∑' first : Vector Digest (steps + 1) × QueryCache HashSpec,
        Pr[= first | firstRun] *
          Pr[fun result :
              (Vector Digest (steps + 1) × Vector Digest (steps + 1)) ×
                QueryCache HashSpec => result.1 = (targetFirst, targetSecond) |
            do
              let second ← Concrete.sampledChainTrajectoryFromCache first.2 parameter
                secondEpoch chain position steps
              pure ((first.1, second.1), second.2)]) =
        ∑' first : Vector Digest (steps + 1) × QueryCache HashSpec,
          Pr[= first | firstRun] *
            (if first.1 = targetFirst then uniformTrajectory else 0) := by
      apply tsum_congr
      intro first
      by_cases htarget : first.1 = targetFirst
      · by_cases hmem : first ∈ support firstRun
        · dsimp only [firstRun] at hmem
          have hsecondProbability :=
            Concrete.sampledChainTrajectoryFromCache_probability first.2 parameter secondEpoch
              chain position steps targetSecond hvalid (by
                intro offset hoffset hstep input hinput
                unfold Concrete.sampledChainTrajectoryFromCache Concrete.sampleChainSeed at hmem
                rw [mem_support_bind_iff] at hmem
                obtain ⟨value, _hvalue, htrajectory⟩ := hmem
                apply Concrete.CacheReplay.cache_none_of_zero_query_bound
                  (Concrete.chainTrajectory parameter firstEpoch chain position steps value)
                  input cache first.2 first.1
                · apply OracleComp.IsQueryBoundP.of_imp
                    (p' := AtHashAddress parameter
                      (.chain secondEpoch chain ⟨position + offset, hstep⟩))
                  · intro candidate heq
                    simpa only [heq] using hinput
                  · apply Concrete.chainTrajectory_queryBound_zero_of_avoids
                    intro firstOffset hfirstOffset hfirstStep heq
                    simp only [HashDomain.chain.injEq] at heq
                    exact hne heq.1
                · exact hsecondAbsent ⟨position + offset, hstep⟩ input hinput
                · exact htrajectory)
          have hcontinuation :
              Pr[fun result :
                  (Vector Digest (steps + 1) × Vector Digest (steps + 1)) ×
                    QueryCache HashSpec => result.1 = (targetFirst, targetSecond) |
                do
                  let second ← Concrete.sampledChainTrajectoryFromCache first.2 parameter
                    secondEpoch chain position steps
                  pure ((first.1, second.1), second.2)] = uniformTrajectory := by
            rw [bind_pure_comp, probEvent_map]
            calc
              Pr[(fun result => result.1 = (targetFirst, targetSecond)) ∘
                    (fun second : Vector Digest (steps + 1) × QueryCache HashSpec =>
                      ((first.1, second.1), second.2)) |
                  Concrete.sampledChainTrajectoryFromCache first.2 parameter secondEpoch chain
                    position steps] =
                  Pr[fun second : Vector Digest (steps + 1) × QueryCache HashSpec =>
                      second.1 = targetSecond |
                    Concrete.sampledChainTrajectoryFromCache first.2 parameter secondEpoch chain
                      position steps] := by
                apply probEvent_congr' (fun second _ => ?_) rfl
                change ((first.1, second.1) = (targetFirst, targetSecond) ↔
                  second.1 = targetSecond)
                constructor
                · intro heq
                  exact congrArg Prod.snd heq
                · intro heq
                  exact Prod.ext htarget heq
              _ = uniformTrajectory := hsecondProbability
          rw [hcontinuation, if_pos htarget]
        · rw [probOutput_eq_zero_of_not_mem_support hmem]
          simp
      · have hcontinuation :
            Pr[fun result :
                (Vector Digest (steps + 1) × Vector Digest (steps + 1)) ×
                  QueryCache HashSpec => result.1 = (targetFirst, targetSecond) |
              do
                let second ← Concrete.sampledChainTrajectoryFromCache first.2 parameter
                  secondEpoch chain position steps
                pure ((first.1, second.1), second.2)] = 0 := by
            rw [bind_pure_comp, probEvent_map]
            apply probEvent_eq_zero
            intro second _ heq
            change (first.1, second.1) = (targetFirst, targetSecond) at heq
            exact htarget (congrArg Prod.fst heq)
        rw [hcontinuation]
        simp [htarget]
    _ = (∑' first : Vector Digest (steps + 1) × QueryCache HashSpec,
          if first.1 = targetFirst then Pr[= first | firstRun] else 0) *
          uniformTrajectory := by
      rw [← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro first
      by_cases htarget : first.1 = targetFirst <;> simp [htarget]
    _ = Pr[fun first : Vector Digest (steps + 1) × QueryCache HashSpec =>
          first.1 = targetFirst | firstRun] * uniformTrajectory := by
      rw [probEvent_eq_tsum_ite]
    _ = uniformTrajectory * uniformTrajectory := by
      congr 1
      exact Concrete.sampledChainTrajectoryFromCache_probability cache parameter firstEpoch
        chain position steps targetFirst hvalid (by
          intro offset hoffset hstep input hinput
          exact hfirstAbsent ⟨position + offset, hstep⟩ input hinput)
    _ = (((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ^ (steps + 1) *
        (((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ^ (steps + 1) := rfl

noncomputable def Concrete.sampledChainTrajectoriesFromCache
    (parameter : PublicParameter) (chain : ChainIndex) (position steps : Nat) :
    (cache : QueryCache HashSpec) → (epochs : List Epoch) →
      ProbComp (List (Vector Digest (steps + 1)) × QueryCache HashSpec)
  | cache, [] => pure ([], cache)
  | cache, epoch :: epochs => do
      let first ← Concrete.sampledChainTrajectoryFromCache cache parameter epoch chain
        position steps
      let rest ← Concrete.sampledChainTrajectoriesFromCache parameter chain position steps
        first.2 epochs
      return (first.1 :: rest.1, rest.2)

theorem Concrete.sampledChainTrajectoriesFromCache_nil
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (chain : ChainIndex) (position steps : Nat) :
    Concrete.sampledChainTrajectoriesFromCache parameter chain position steps cache [] =
      pure ([], cache) := rfl

theorem Concrete.sampledChainTrajectoriesFromCache_cons
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (epoch : Epoch) (epochs : List Epoch) (chain : ChainIndex) (position steps : Nat) :
    Concrete.sampledChainTrajectoriesFromCache parameter chain position steps cache
      (epoch :: epochs) = (do
        let first ← Concrete.sampledChainTrajectoryFromCache cache parameter epoch chain
          position steps
        let rest ← Concrete.sampledChainTrajectoriesFromCache parameter chain position steps
          first.2 epochs
        return (first.1 :: rest.1, rest.2)) := rfl

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
theorem Concrete.sampledChainTrajectoriesFromCache_support_length
    (parameter : PublicParameter) (chain : ChainIndex) (position steps : Nat) :
    ∀ (epochs : List Epoch) (cache : QueryCache HashSpec)
      (result : List (Vector Digest (steps + 1)) × QueryCache HashSpec),
      result ∈ support
        (Concrete.sampledChainTrajectoriesFromCache parameter chain position steps cache epochs) →
        result.1.length = epochs.length := by
  intro epochs
  induction epochs with
  | nil =>
      intro cache result hresult
      simp only [Concrete.sampledChainTrajectoriesFromCache_nil, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      rfl
  | cons epoch epochs ih =>
      intro cache result hresult
      rw [Concrete.sampledChainTrajectoriesFromCache_cons, mem_support_bind_iff] at hresult
      obtain ⟨first, _hfirst, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      cases hpure
      simp only [List.length_cons]
      rw [ih first.2 rest hrest]

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem Concrete.sampledChainTrajectoriesFromCache_probability
    (parameter : PublicParameter) (chain : ChainIndex) (position steps : Nat)
    (hvalid : position + steps ≤ chainLength - 1) :
    ∀ (epochs : List Epoch) (cache : QueryCache HashSpec),
      epochs.Nodup →
      (∀ epoch ∈ epochs, ∀ step : ChainStep, ∀ input,
        AtHashAddress parameter (.chain epoch chain step) input → cache input = none) →
      ∀ target : List (Vector Digest (steps + 1)), target.length = epochs.length →
        Pr[fun result : List (Vector Digest (steps + 1)) × QueryCache HashSpec =>
            result.1 = target |
          Concrete.sampledChainTrajectoriesFromCache parameter chain position steps cache
            epochs] =
          ((((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ^ (steps + 1)) ^ epochs.length := by
  intro epochs
  induction epochs with
  | nil =>
      intro cache _hnodup _habsent target hlength
      have htarget : target = [] := by simpa using hlength
      subst target
      simp [Concrete.sampledChainTrajectoriesFromCache_nil]
  | cons epoch epochs ih =>
      intro cache hnodup habsent target hlength
      obtain ⟨hepoch, hepochs⟩ := List.nodup_cons.mp hnodup
      cases target with
      | nil => simp at hlength
      | cons targetFirst targetRest =>
        simp only [List.length_cons, Nat.succ.injEq] at hlength
        rw [Concrete.sampledChainTrajectoriesFromCache_cons, probEvent_bind_eq_tsum]
        let firstRun := Concrete.sampledChainTrajectoryFromCache cache parameter epoch chain
          position steps
        let uniformTrajectory : ℝ≥0∞ :=
          (((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ^ (steps + 1)
        calc
          (∑' first : Vector Digest (steps + 1) × QueryCache HashSpec,
              Pr[= first | firstRun] *
                Pr[fun result : List (Vector Digest (steps + 1)) × QueryCache HashSpec =>
                    result.1 = targetFirst :: targetRest |
                  do
                    let rest ← Concrete.sampledChainTrajectoriesFromCache parameter chain
                      position steps first.2 epochs
                    pure (first.1 :: rest.1, rest.2)]) =
              ∑' first : Vector Digest (steps + 1) × QueryCache HashSpec,
                Pr[= first | firstRun] *
                  (if first.1 = targetFirst then uniformTrajectory ^ epochs.length else 0) := by
            apply tsum_congr
            intro first
            by_cases htarget : first.1 = targetFirst
            · by_cases hmem : first ∈ support firstRun
              · dsimp only [firstRun] at hmem
                unfold Concrete.sampledChainTrajectoryFromCache Concrete.sampleChainSeed at hmem
                rw [mem_support_bind_iff] at hmem
                obtain ⟨value, _hvalue, htrajectory⟩ := hmem
                have hrestAbsent : ∀ restEpoch ∈ epochs, ∀ step : ChainStep, ∀ input,
                    AtHashAddress parameter (.chain restEpoch chain step) input →
                      first.2 input = none := by
                  intro restEpoch hrestEpoch step input hinput
                  apply Concrete.CacheReplay.cache_none_of_zero_query_bound
                    (Concrete.chainTrajectory parameter epoch chain position steps value)
                    input cache first.2 first.1
                  · apply OracleComp.IsQueryBoundP.of_imp
                      (p' := AtHashAddress parameter (.chain restEpoch chain step))
                    · intro candidate heq
                      simpa only [heq] using hinput
                    · apply Concrete.chainTrajectory_queryBound_zero_of_avoids
                      intro offset hoffset hstep heq
                      simp only [HashDomain.chain.injEq] at heq
                      exact hepoch (heq.1 ▸ hrestEpoch)
                  · exact habsent restEpoch (by simp [hrestEpoch]) step input hinput
                  · exact htrajectory
                have hrestProbability := ih first.2 hepochs hrestAbsent targetRest hlength
                have hcontinuation :
                    Pr[fun result :
                        List (Vector Digest (steps + 1)) × QueryCache HashSpec =>
                        result.1 = targetFirst :: targetRest |
                      do
                        let rest ← Concrete.sampledChainTrajectoriesFromCache parameter chain
                          position steps first.2 epochs
                        pure (first.1 :: rest.1, rest.2)] =
                      uniformTrajectory ^ epochs.length := by
                  rw [bind_pure_comp, probEvent_map]
                  calc
                    Pr[(fun result => result.1 = targetFirst :: targetRest) ∘
                          (fun rest : List (Vector Digest (steps + 1)) × QueryCache HashSpec =>
                            (first.1 :: rest.1, rest.2)) |
                        Concrete.sampledChainTrajectoriesFromCache parameter chain position steps
                          first.2 epochs] =
                        Pr[fun rest :
                            List (Vector Digest (steps + 1)) × QueryCache HashSpec =>
                            rest.1 = targetRest |
                          Concrete.sampledChainTrajectoriesFromCache parameter chain position steps
                            first.2 epochs] := by
                      apply probEvent_congr' (fun rest _ => ?_) rfl
                      change (first.1 :: rest.1 = targetFirst :: targetRest ↔
                        rest.1 = targetRest)
                      simp only [List.cons.injEq, htarget, true_and]
                    _ = uniformTrajectory ^ epochs.length := hrestProbability
                rw [hcontinuation, if_pos htarget]
              · rw [probOutput_eq_zero_of_not_mem_support hmem]
                simp
            · have hcontinuation :
                  Pr[fun result :
                      List (Vector Digest (steps + 1)) × QueryCache HashSpec =>
                      result.1 = targetFirst :: targetRest |
                    do
                      let rest ← Concrete.sampledChainTrajectoriesFromCache parameter chain
                        position steps first.2 epochs
                      pure (first.1 :: rest.1, rest.2)] = 0 := by
                rw [bind_pure_comp, probEvent_map]
                apply probEvent_eq_zero
                intro rest _ heq
                change first.1 :: rest.1 = targetFirst :: targetRest at heq
                exact htarget (List.cons.inj heq).1
              rw [hcontinuation]
              simp [htarget]
          _ = (∑' first : Vector Digest (steps + 1) × QueryCache HashSpec,
                if first.1 = targetFirst then Pr[= first | firstRun] else 0) *
                (uniformTrajectory ^ epochs.length) := by
            rw [← ENNReal.tsum_mul_right]
            apply tsum_congr
            intro first
            by_cases htarget : first.1 = targetFirst <;> simp [htarget]
          _ = Pr[fun first : Vector Digest (steps + 1) × QueryCache HashSpec =>
                first.1 = targetFirst | firstRun] *
                (uniformTrajectory ^ epochs.length) := by
            rw [probEvent_eq_tsum_ite]
          _ = uniformTrajectory * (uniformTrajectory ^ epochs.length) := by
            congr 1
            exact Concrete.sampledChainTrajectoryFromCache_probability cache parameter epoch chain
              position steps targetFirst hvalid (by
                intro offset hoffset hstep input hinput
                exact habsent epoch (by simp) ⟨position + offset, hstep⟩ input hinput)
          _ = uniformTrajectory ^ (epoch :: epochs).length := by
            simp only [List.length_cons, pow_succ]
            rw [mul_comm]
          _ = ((((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ^ (steps + 1)) ^
              (epoch :: epochs).length := rfl

abbrev FullChainTrajectory := Vector Digest (chainLength - 1 + 1)

noncomputable def allEpochs : List Epoch :=
  Finset.univ.toList

theorem allEpochs_nodup : allEpochs.Nodup := by
  exact Finset.nodup_toList Finset.univ

theorem mem_allEpochs (epoch : Epoch) : epoch ∈ allEpochs := by
  simp [allEpochs]

theorem allEpochs_length : allEpochs.length = lifetime := by
  simp [allEpochs, Epoch]

attribute [irreducible] allEpochs

noncomputable def Concrete.sampledAllEpochChainTrajectories
    (parameter : PublicParameter) (chain : ChainIndex) :
    ProbComp (List FullChainTrajectory × QueryCache HashSpec) :=
  Concrete.sampledChainTrajectoriesFromCache parameter chain 0 (chainLength - 1) ∅
    allEpochs

set_option maxRecDepth 100000 in
theorem Concrete.sampledAllEpochChainTrajectories_probability
    (parameter : PublicParameter) (chain : ChainIndex)
    (target : List FullChainTrajectory) (hlength : target.length = lifetime) :
    Pr[fun result : List FullChainTrajectory × QueryCache HashSpec => result.1 = target |
      Concrete.sampledAllEpochChainTrajectories parameter chain] =
      ((((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ^ (chainLength - 1 + 1)) ^ lifetime := by
  unfold Concrete.sampledAllEpochChainTrajectories
  have hprobability := Concrete.sampledChainTrajectoriesFromCache_probability
    (parameter := parameter) (chain := chain) (position := 0) (steps := chainLength - 1)
    (hvalid := by omega) (epochs := allEpochs) (cache := ∅)
    allEpochs_nodup (by simp) target (by simpa [allEpochs_length] using hlength)
  simpa only [allEpochs_length] using hprobability

end XmssSecurity

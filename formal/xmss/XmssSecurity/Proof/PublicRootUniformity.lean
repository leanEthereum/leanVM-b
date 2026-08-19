import XmssSecurity.Proof.ChainValueUniformity
import XmssSecurity.Proof.MerkleQueryBound
import XmssSecurity.Proof.SecretTableUniformity
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

noncomputable local instance rootUniformitySampleableDigest : SampleableType Digest :=
  SampleableType.ofFintype Digest

noncomputable local instance rootUniformitySampleableSecret :
    SampleableType (Epoch → ChainIndex → Digest) :=
  SampleableType.ofFintype (Epoch → ChainIndex → Digest)

noncomputable local instance rootUniformitySampleableEpochDigest :
    SampleableType (Epoch → Digest) :=
  SampleableType.ofFintype (Epoch → Digest)

noncomputable def Concrete.treeChildren (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) (levels : Nat)
    (node : MerkleNode) : OracleComp HashSpec (Digest × Digest) := do
  let left ← Concrete.treeNode parameter secret levels
    (Concrete.childNode node false)
  let right ← Concrete.treeNode parameter secret levels
    (Concrete.childNode node true)
  return (left, right)

theorem Concrete.treeChildren_queryBound_parentAddress
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (levels : Nat) (node : MerkleNode) (hlevel : levels < treeHeight)
    (hvalid : TreeSubtreeValid (levels + 1) node) :
    (Concrete.treeChildren parameter secret levels node).IsQueryBoundP
      (AtHashAddress parameter (.merkle ⟨levels, hlevel⟩ node)) 0 := by
  unfold Concrete.treeChildren
  have hleft := Concrete.treeNode_queryBound_merkleAddress parameter secret
    ⟨levels, hlevel⟩ node levels (Concrete.childNode node false)
    (Nat.le_of_lt hlevel) (childNode_subtreeValid levels node false hvalid)
  have hright := Concrete.treeNode_queryBound_merkleAddress parameter secret
    ⟨levels, hlevel⟩ node levels (Concrete.childNode node true)
    (Nat.le_of_lt hlevel) (childNode_subtreeValid levels node true hvalid)
  have hleftZero :
      (Concrete.treeNode parameter secret levels (Concrete.childNode node false) :
        OracleComp HashSpec Digest).IsQueryBoundP
        (AtHashAddress parameter (.merkle ⟨levels, hlevel⟩ node)) 0 := by
    simpa [MerkleAddressInSubtree] using hleft
  have hrightZero :
      (Concrete.treeNode parameter secret levels (Concrete.childNode node true) :
        OracleComp HashSpec Digest).IsQueryBoundP
        (AtHashAddress parameter (.merkle ⟨levels, hlevel⟩ node)) 0 := by
    simpa [MerkleAddressInSubtree] using hright
  refine OracleComp.isQueryBoundP_bind (n := 0) (m := 0) hleftZero ?_
  intro left _
  refine OracleComp.isQueryBoundP_bind (n := 0) (m := 0) hrightZero ?_
  intro right _
  exact OracleComp.isQueryBoundP_pure
    (p := AtHashAddress parameter (.merkle ⟨levels, hlevel⟩ node))
    (left, right) 0

/-- The root of any valid positive-height subtree is uniform because its last typed Merkle query is fresh. -/
theorem Concrete.treeNode_positive_probability_from_cache
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (levels : Nat) (node : MerkleNode) (hlevel : levels < treeHeight)
    (hvalid : TreeSubtreeValid (levels + 1) node)
    (initialCache : QueryCache HashSpec)
    (habsent : ∀ input,
      AtHashAddress parameter (.merkle ⟨levels, hlevel⟩ node) input →
        initialCache input = none)
    (target : Digest) :
    Pr[fun result : Digest × QueryCache HashSpec => result.1 = target |
      (simulateQ randomOracle
        (Concrete.treeNode parameter secret (levels + 1) node :
          OracleComp HashSpec Digest)).run initialCache] =
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  rw [Concrete.treeNode_succ_eq]
  simp only [hlevel, ↓reduceDIte]
  have hfactor :
      (do
        let left ← Concrete.treeNode parameter secret levels
          (Concrete.childNode node false)
        let right ← Concrete.treeNode parameter secret levels
          (Concrete.childNode node true)
        Concrete.nodeHash parameter ⟨levels, hlevel⟩ node left right :
          OracleComp HashSpec Digest) =
        (Concrete.treeChildren parameter secret levels node >>= fun children =>
          Concrete.nodeHash parameter ⟨levels, hlevel⟩ node
            children.1 children.2) := by
    simp [Concrete.treeChildren]
  rw [hfactor]
  rw [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum]
  have hchildrenBound := Concrete.treeChildren_queryBound_parentAddress
    parameter secret levels node hlevel hvalid
  have hconditional : ∀ childrenResult ∈ support
      ((simulateQ randomOracle
        (Concrete.treeChildren parameter secret levels node)).run initialCache),
      Pr[fun result : Digest × QueryCache HashSpec => result.1 = target |
        (simulateQ randomOracle
          (Concrete.nodeHash parameter ⟨levels, hlevel⟩ node
            childrenResult.1.1 childrenResult.1.2 :
            OracleComp HashSpec Digest)).run childrenResult.2] =
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
    intro childrenResult hchildren
    apply Concrete.tweakableHash_fresh_probability
    apply Concrete.CacheReplay.cache_none_of_zero_query_bound
      (Concrete.treeChildren parameter secret levels node)
      (tweakableHashInput parameter (.merkle ⟨levels, hlevel⟩ node)
        (Concrete.nodePayload childrenResult.1.1 childrenResult.1.2))
      initialCache childrenResult.2 childrenResult.1
    · apply OracleComp.IsQueryBoundP.of_imp
        (p := fun input => input =
          tweakableHashInput parameter (.merkle ⟨levels, hlevel⟩ node)
            (Concrete.nodePayload childrenResult.1.1 childrenResult.1.2))
        (p' := AtHashAddress parameter (.merkle ⟨levels, hlevel⟩ node))
      · intro input heq
        subst input
        exact (atHashAddress_tweakableHashInput_iff parameter _ _ _).2 rfl
      · exact hchildrenBound
    · exact habsent _ ((atHashAddress_tweakableHashInput_iff parameter _ _ _).2 rfl)
    · exact hchildren
  calc
    ∑' childrenResult,
        Pr[= childrenResult |
          (simulateQ randomOracle
            (Concrete.treeChildren parameter secret levels node)).run initialCache] *
          Pr[fun result : Digest × QueryCache HashSpec => result.1 = target |
            (simulateQ randomOracle
              (Concrete.nodeHash parameter ⟨levels, hlevel⟩ node
                childrenResult.1.1 childrenResult.1.2 :
                OracleComp HashSpec Digest)).run childrenResult.2] =
      ∑' childrenResult,
        Pr[= childrenResult |
          (simulateQ randomOracle
            (Concrete.treeChildren parameter secret levels node)).run initialCache] *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
      apply tsum_congr
      intro childrenResult
      by_cases hchildren : childrenResult ∈ support
          ((simulateQ randomOracle
            (Concrete.treeChildren parameter secret levels node)).run initialCache)
      · rw [hconditional childrenResult hchildren]
      · rw [probOutput_eq_zero_of_not_mem_support hchildren, zero_mul, zero_mul]
    _ = (∑' childrenResult,
        Pr[= childrenResult |
          (simulateQ randomOracle
            (Concrete.treeChildren parameter secret levels node)).run initialCache]) *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ :=
      ENNReal.tsum_mul_right
    _ = ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
      rw [tsum_probOutput_eq_one']
      · exact one_mul _
      · exact probFailure_eq_zero'
          (neverFail_simulateQ_randomOracle_run
            (Concrete.treeChildren parameter secret levels node) initialCache)

/-- For every fixed parameter and secret table, the public root is exactly uniform. -/
theorem Concrete.rootTree_probability (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) (target : Digest) :
    Pr[fun result : Digest × QueryCache HashSpec => result.1 = target |
      (simulateQ randomOracle
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)).run ∅] =
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  have hheight : treeHeight = (treeHeight - 1) + 1 := by
    decide
  rw [hheight]
  exact Concrete.treeNode_positive_probability_from_cache
    (parameter := parameter) (secret := secret) (levels := treeHeight - 1)
    (node := Concrete.rootNode) (hlevel := by decide)
    (hvalid := by
      unfold TreeSubtreeValid Concrete.rootNode lifetime
      change (0 + 1) * 2 ^ (treeHeight - 1 + 1) ≤ 2 ^ treeHeight
      rw [← hheight]
      simp)
    (initialCache := ∅) (habsent := by simp) target

noncomputable def Concrete.keygenAtParameter
    (parameter : PublicParameter) : ProbComp (Digest × (Epoch → ChainIndex → Digest)) := do
  let secret ← Concrete.sampleSecret
  let root ← (simulateQ randomOracle
    (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
      OracleComp HashSpec Digest)).run'
      ∅
  return (root, secret)

noncomputable def Concrete.idealKeygenAtParameter
    (_parameter : PublicParameter) : ProbComp (Digest × (Epoch → ChainIndex → Digest)) := do
  let secret ← Concrete.sampleSecret
  let root ← $ᵗ Digest
  return (root, secret)

theorem Concrete.rootTree_probOutput (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) (target : Digest) :
    Pr[= target |
      (simulateQ randomOracle
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)).run' ∅] =
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  rw [← probEvent_eq_eq_probOutput, StateT.run'_eq, probEvent_map]
  exact Concrete.rootTree_probability parameter secret target

/-- After discarding the private random-oracle cache, key generation exposes an independent uniform root. -/
theorem Concrete.evalDist_keygenAtParameter_eq_ideal
    (parameter : PublicParameter) :
    𝒟[Concrete.keygenAtParameter parameter] =
      𝒟[Concrete.idealKeygenAtParameter parameter] := by
  apply SPMF.ext
  rintro ⟨targetRoot, targetSecret⟩
  change Pr[= (targetRoot, targetSecret) | Concrete.keygenAtParameter parameter] =
    Pr[= (targetRoot, targetSecret) | Concrete.idealKeygenAtParameter parameter]
  unfold Concrete.keygenAtParameter Concrete.idealKeygenAtParameter
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  apply tsum_congr
  intro secret
  have hreturn (computation : ProbComp Digest) :
      Pr[= (targetRoot, targetSecret) |
        computation >>= fun root => pure (root, secret)] =
        if secret = targetSecret then Pr[= targetRoot | computation] else 0 := by
    by_cases hsecret : secret = targetSecret
    · subst secret
      rw [if_pos rfl, probOutput_bind_eq_tsum, tsum_eq_single targetRoot]
      · simp
      · intro root hne
        simp [hne.symm]
    · rw [if_neg hsecret, probOutput_bind_eq_tsum]
      apply ENNReal.tsum_eq_zero.mpr
      intro root
      rw [probOutput_pure,
        if_neg (fun heq => hsecret (congrArg Prod.snd heq).symm), mul_zero]
  rw [hreturn, hreturn]
  by_cases hsecret : secret = targetSecret
  · subst secret
    simp only [if_pos]
    have hleft := Concrete.rootTree_probOutput parameter targetSecret targetRoot
    have hright := HiddenValue.uniform_digest_point_probability targetRoot
    rw [hleft, hright]
  · rw [if_neg hsecret, if_neg hsecret]

noncomputable def Concrete.keygenKeysOnly : ProbComp (PublicKey × SecretKey) :=
  Prod.fst <$> (simulateQ xmssRomImpl Concrete.keygen).run ∅

noncomputable def Concrete.decomposedKeygenKeysOnly : ProbComp (PublicKey × SecretKey) := do
  let parameter ← Concrete.samplePublicParameter
  let result ← Concrete.keygenAtParameter parameter
  return (⟨result.1, parameter⟩,
    SecretKey.withoutPrecomputation parameter result.2)

noncomputable def Concrete.idealKeygenKeysOnly : ProbComp (PublicKey × SecretKey) := do
  let parameter ← Concrete.samplePublicParameter
  let result ← Concrete.idealKeygenAtParameter parameter
  return (⟨result.1, parameter⟩,
    SecretKey.withoutPrecomputation parameter result.2)

theorem Concrete.keygenKeysOnly_eq_decomposed :
    Concrete.keygenKeysOnly = Concrete.decomposedKeygenKeysOnly := by
  unfold Concrete.keygenKeysOnly Concrete.decomposedKeygenKeysOnly Concrete.keygen
    Concrete.keygenAtParameter
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
    map_eq_bind_pure_comp, bind_assoc]
  have hparameter :
      (simulateQ xmssRomImpl (liftM Concrete.samplePublicParameter)).run ∅ =
        (fun parameter => (parameter, ∅)) <$> Concrete.samplePublicParameter := by
    simpa only [xmssRomImpl] using
      (roSim.run_liftM
        (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
        Concrete.samplePublicParameter ∅)
  rw [hparameter]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  congr 1
  funext parameter
  have hsecret :
      (simulateQ xmssRomImpl (liftM Concrete.sampleSecret)).run ∅ =
        (fun secret => (secret, ∅)) <$> Concrete.sampleSecret := by
    simpa only [xmssRomImpl] using
      (roSim.run_liftM
        (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
        Concrete.sampleSecret ∅)
  rw [hsecret]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  congr 1
  funext secret
  have htree :
      simulateQ xmssRomImpl
          (liftM (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest)) =
        simulateQ
          (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest) := by
    simp only [xmssRomImpl]
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)
  rw [htree]
  simp [StateT.run'_eq, map_eq_bind_pure_comp]

set_option maxRecDepth 100000 in
theorem Concrete.evalDist_keygenKeysOnly_eq_ideal :
    𝒟[Concrete.keygenKeysOnly] = 𝒟[Concrete.idealKeygenKeysOnly] := by
  rw [Concrete.keygenKeysOnly_eq_decomposed]
  unfold Concrete.decomposedKeygenKeysOnly Concrete.idealKeygenKeysOnly
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  rw [bind_pure_comp, bind_pure_comp, evalDist_map, evalDist_map,
    Concrete.evalDist_keygenAtParameter_eq_ideal parameter]

noncomputable def Concrete.independentKeygenKeysOnly : ProbComp (PublicKey × SecretKey) := do
  let parameter ← Concrete.samplePublicParameter
  let root ← $ᵗ Digest
  let secret ← Concrete.sampleSecret
  return (⟨root, parameter⟩,
    SecretKey.withoutPrecomputation parameter secret)

theorem Concrete.evalDist_idealKeygenKeysOnly_eq_independent :
    𝒟[Concrete.idealKeygenKeysOnly] =
      𝒟[Concrete.independentKeygenKeysOnly] := by
  unfold Concrete.idealKeygenKeysOnly Concrete.idealKeygenAtParameter
    Concrete.independentKeygenKeysOnly
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  simp only [bind_assoc, pure_bind]
  exact OracleComp.DeferredSampling.evalDist_bind_comm
    Concrete.sampleSecret ($ᵗ Digest)
    (fun secret root => pure
      ((⟨root, parameter⟩ : PublicKey),
        SecretKey.withoutPrecomputation parameter secret))

/-- The actual public key is independent of the full secret table once the private key-generation cache is hidden. -/
theorem Concrete.evalDist_keygenKeysOnly_eq_independent :
    𝒟[Concrete.keygenKeysOnly] =
      𝒟[Concrete.independentKeygenKeysOnly] :=
  Concrete.evalDist_keygenKeysOnly_eq_ideal.trans
    Concrete.evalDist_idealKeygenKeysOnly_eq_independent

noncomputable def Concrete.fixedChainPublicView (chain : ChainIndex) :
    ProbComp (PublicKey × (Epoch → Digest)) :=
  (fun keys => (keys.1, fun epoch => keys.2.chainStart epoch chain)) <$>
    Concrete.keygenKeysOnly

noncomputable def Concrete.independentFixedChainPublicView (_chain : ChainIndex) :
    ProbComp (PublicKey × (Epoch → Digest)) := do
  let parameter ← Concrete.samplePublicParameter
  let root ← $ᵗ Digest
  let table ← $ᵗ (Epoch → Digest)
  return (⟨root, parameter⟩, table)

/-- For any fixed WOTS chain, its complete epoch-indexed seed table is uniform and independent of the public key. -/
theorem Concrete.evalDist_fixedChainPublicView_eq_independent
    (chain : ChainIndex) :
    𝒟[Concrete.fixedChainPublicView chain] =
      𝒟[Concrete.independentFixedChainPublicView chain] := by
  unfold Concrete.fixedChainPublicView
  rw [evalDist_map, Concrete.evalDist_keygenKeysOnly_eq_independent, ← evalDist_map]
  unfold Concrete.independentKeygenKeysOnly Concrete.independentFixedChainPublicView
  simp only [map_bind, bind_pure_comp]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro root
  simp only [Functor.map_map]
  rw [evalDist_map]
  have hsecret := evalDist_sampleSecret_fixedChain_eq_uniform chain
  rw [evalDist_map] at hsecret
  calc
    (fun secret =>
        ((⟨root, parameter⟩ : PublicKey), fun epoch => secret epoch chain)) <$>
        𝒟[Concrete.sampleSecret] =
      (Prod.mk (⟨root, parameter⟩ : PublicKey)) <$>
        ((fun secret => fun epoch => secret epoch chain) <$>
          𝒟[Concrete.sampleSecret]) := by
        rw [Functor.map_map]
    _ = (Prod.mk (⟨root, parameter⟩ : PublicKey)) <$>
        𝒟[$ᵗ (Epoch → Digest)] := by rw [hsecret]
    _ = 𝒟[(Prod.mk (⟨root, parameter⟩ : PublicKey)) <$>
        ($ᵗ (Epoch → Digest))] := by rw [evalDist_map]

noncomputable def Concrete.independentPublicKey : ProbComp PublicKey := do
  let parameter ← Concrete.samplePublicParameter
  let root ← $ᵗ Digest
  return ⟨root, parameter⟩

noncomputable def Concrete.fixedChainPublicGuessExperiment
    (chain : ChainIndex) (queries : Nat)
    (strategy : PublicKey → List Bool → Epoch × Digest) : ProbComp Bool :=
  (fun view => IndexedHiddenValue.readMany view.2 queries (strategy view.1)) <$>
    Concrete.fixedChainPublicView chain

/-- Even after seeing the concrete public key, adaptive equality probes against every epoch seed of one fixed chain cost only once per probe. -/
theorem Concrete.fixedChainPublicGuess_probability_le
    (chain : ChainIndex) (queries : Nat)
    (strategy : PublicKey → List Bool → Epoch × Digest) :
    Pr[(fun hit : Bool => hit = true) |
      Concrete.fixedChainPublicGuessExperiment chain queries strategy] ≤
      (queries : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  let strategyGenerator : ProbComp (List Bool → Epoch × Digest) :=
    do
      let parameter ← Concrete.samplePublicParameter
      let root ← $ᵗ Digest
      return strategy ⟨root, parameter⟩
  have hdist :
      𝒟[Concrete.fixedChainPublicGuessExperiment chain queries strategy] =
        𝒟[IndexedHiddenValue.adaptiveGuessExperiment
          strategyGenerator queries] := by
    unfold Concrete.fixedChainPublicGuessExperiment
    rw [evalDist_map, Concrete.evalDist_fixedChainPublicView_eq_independent chain,
      ← evalDist_map]
    unfold Concrete.independentFixedChainPublicView
      IndexedHiddenValue.adaptiveGuessExperiment IndexedHiddenValue.experiment
      strategyGenerator
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
      Function.comp_apply]
  exact (probEvent_congr' (fun _ _ => Iff.rfl) hdist).le.trans
    (IndexedHiddenValue.adaptive_guess_after_public_sampling_le
      strategyGenerator queries)

end XmssSecurity

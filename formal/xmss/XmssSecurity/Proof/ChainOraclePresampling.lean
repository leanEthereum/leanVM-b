import XmssSecurity.Proof.QueryPresence
import XmssSecurity.Proof.StatementLemmas
import XmssSecurity.Proof.ChainTableUniformity
import XmssSecurity.Proof.AdaptiveFreshTarget
import XmssSecurity.Proof.RandomOraclePresampling
import XmssSecurity.Proof.HiddenValue
import XmssSecurity.Proof.UniformFiniteTable

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.Concrete.CacheReplay

theorem chainWalk_query_cached_in_largerCache
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (position steps : Nat) (value : Digest) (offset : Nat)
    (hoffset : offset < steps)
    (hposition : position + offset < chainLength - 1)
    (initialCache resultCache largerCache : QueryCache HashSpec) (digest : Digest)
    (hmem : (digest, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.chainWalk parameter epoch chain position steps value :
          OracleComp HashSpec Digest)).run initialCache))
    (hle : resultCache ≤ largerCache) :
    ∃ output, largerCache
      (Concrete.CacheView.chainInput parameter epoch chain
        ⟨position + offset, hposition⟩
        (Wots.walk (Concrete.CacheView.chainStep largerCache parameter epoch chain)
          position offset value)) = some output := by
  induction steps generalizing offset initialCache resultCache digest with
  | zero => omega
  | succ steps ih =>
      rw [Concrete.chainWalk, simulateQ_bind, StateT.run_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨previous, middleCache⟩, hprefix, hrest⟩ := hmem
      have hmiddleLe : middleCache ≤ resultCache :=
        randomOracle_cache_le
          (if hlast : position + steps < chainLength - 1 then
            Concrete.chainHash parameter epoch chain ⟨position + steps, hlast⟩ previous
          else pure 0 : OracleComp HashSpec Digest)
          middleCache (digest, resultCache) hrest
      by_cases hbefore : offset < steps
      · exact ih offset hbefore hposition initialCache middleCache previous hprefix
          (hmiddleLe.trans hle)
      · have hoffsetEq : offset = steps := by omega
        subst offset
        simp only [hposition, ↓reduceDIte] at hrest
        obtain ⟨output, hcached, _⟩ := tweakableHash_query_cached parameter
          (.chain epoch chain ⟨position + steps, hposition⟩)
          (Concrete.digestBytes previous) middleCache resultCache digest hrest
        have hprevious := eval_answerFn_largerCache_eq_of_mem_support
          (Concrete.chainWalk parameter epoch chain position steps value :
            OracleComp HashSpec Digest)
          initialCache middleCache largerCache previous hprefix (hmiddleLe.trans hle)
        rw [eval_chainWalk] at hprevious
        refine ⟨output, ?_⟩
        rw [hprevious]
        exact hle hcached

theorem sequenceFin_component_support_in_largerCache {n : Nat}
    (computation : Fin n → OracleComp HashSpec α) (target : Fin n)
    (initialCache resultCache largerCache : QueryCache HashSpec) (values : Fin n → α)
    (hmem : (values, resultCache) ∈ support
      ((simulateQ randomOracle (Concrete.sequenceFin computation)).run initialCache))
    (hle : resultCache ≤ largerCache) :
    ∃ beforeCache afterCache value,
      (value, afterCache) ∈ support
        ((simulateQ randomOracle (computation target)).run beforeCache) ∧
      afterCache ≤ largerCache := by
  induction n generalizing initialCache resultCache largerCache with
  | zero => exact Fin.elim0 target
  | succ n ih =>
      rw [Concrete.sequenceFin, simulateQ_bind, StateT.run_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨head, headCache⟩, hhead, hrest⟩ := hmem
      obtain rfl | ⟨tailTarget, rfl⟩ := target.eq_zero_or_eq_succ
      · have hheadLe : headCache ≤ largerCache :=
          (randomOracle_cache_le
            (do
              let tail ← Concrete.sequenceFin fun index : Fin n => computation index.succ
              pure (Fin.cases head tail) : OracleComp HashSpec (Fin (n + 1) → α))
            headCache (values, resultCache) hrest).trans hle
        exact ⟨initialCache, headCache, head, hhead, hheadLe⟩
      · rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
        obtain ⟨⟨tail, tailCache⟩, htail, hfinal⟩ := hrest
        simp only [simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hfinal
        cases hfinal
        exact ih (fun index => computation index.succ) tailTarget headCache resultCache
          largerCache tail htail hle

theorem oneTimePublicKey_chain_query_cached_in_largerCache
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) (chain : ChainIndex) (step : ChainStep)
    (initialCache resultCache largerCache : QueryCache HashSpec)
    (endpoints : ChainIndex → Digest)
    (hmem : (endpoints, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.oneTimePublicKey parameter secret epoch :
          OracleComp HashSpec (ChainIndex → Digest))).run initialCache))
    (hle : resultCache ≤ largerCache) :
    ∃ output, largerCache
      (Concrete.CacheView.chainInput parameter epoch chain step
        (Wots.walk (Concrete.CacheView.chainStep largerCache parameter epoch chain)
          0 step.val (secret epoch chain))) = some output := by
  unfold Concrete.oneTimePublicKey at hmem
  obtain ⟨beforeCache, afterCache, value, hchain, hafterLe⟩ :=
    sequenceFin_component_support_in_largerCache
      (fun index => Concrete.chainWalk parameter epoch index 0 (chainLength - 1)
        (secret epoch index) : ChainIndex → OracleComp HashSpec Digest)
      chain initialCache resultCache largerCache endpoints hmem hle
  obtain ⟨output, hcached⟩ := chainWalk_query_cached_in_largerCache parameter epoch
    chain 0 (chainLength - 1) (secret epoch chain) step.val step.isLt
    (by simpa only [zero_add] using step.isLt) beforeCache afterCache largerCache value
    hchain hafterLe
  have hstepEq : (⟨0 + step.val, by simpa only [zero_add] using step.isLt⟩ : ChainStep) =
      step := by
    apply Fin.ext
    simp
  rw [hstepEq] at hcached
  exact ⟨output, hcached⟩

theorem leafAt_chain_query_cached_in_largerCache
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) (chain : ChainIndex) (step : ChainStep)
    (initialCache resultCache largerCache : QueryCache HashSpec) (digest : Digest)
    (hmem : (digest, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.leafAt parameter secret epoch : OracleComp HashSpec Digest)).run
          initialCache))
    (hle : resultCache ≤ largerCache) :
    ∃ output, largerCache
      (Concrete.CacheView.chainInput parameter epoch chain step
        (Wots.walk (Concrete.CacheView.chainStep largerCache parameter epoch chain)
          0 step.val (secret epoch chain))) = some output := by
  unfold Concrete.leafAt at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨endpoints, middleCache⟩, honeTime, hleaf⟩ := hmem
  have hmiddleLe : middleCache ≤ resultCache :=
    randomOracle_cache_le (Concrete.leafHash parameter epoch endpoints :
      OracleComp HashSpec Digest) middleCache (digest, resultCache) hleaf
  exact oneTimePublicKey_chain_query_cached_in_largerCache parameter secret epoch chain
    step initialCache middleCache largerCache endpoints honeTime (hmiddleLe.trans hle)

theorem treeNode_chain_query_cached_in_largerCache
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) (chain : ChainIndex) (step : ChainStep)
    (levels : Nat) (node : MerkleNode)
    (hlevels : levels ≤ treeHeight) (hvalid : TreeSubtreeValid levels node)
    (hcover : TreeCovers levels node epoch)
    (initialCache resultCache largerCache : QueryCache HashSpec) (digest : Digest)
    (hmem : (digest, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.treeNode parameter secret levels node :
          OracleComp HashSpec Digest)).run initialCache))
    (hle : resultCache ≤ largerCache) :
    ∃ output, largerCache
      (Concrete.CacheView.chainInput parameter epoch chain step
        (Wots.walk (Concrete.CacheView.chainStep largerCache parameter epoch chain)
          0 step.val (secret epoch chain))) = some output := by
  induction levels generalizing node initialCache resultCache digest with
  | zero =>
      have hnode : node = epoch := treeCovers_zero_iff node epoch |>.mp hcover
      subst node
      rw [Concrete.treeNode_zero_eq] at hmem
      exact leafAt_chain_query_cached_in_largerCache parameter secret epoch chain step
        initialCache resultCache largerCache digest hmem hle
  | succ levels ih =>
      have hlevel : levels < treeHeight := Nat.lt_of_succ_le hlevels
      have hleftValid := childNode_subtreeValid levels node false hvalid
      have hrightValid := childNode_subtreeValid levels node true hvalid
      rw [Concrete.treeNode_succ_eq, simulateQ_bind, StateT.run_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨left, leftCache⟩, hleft, hrest⟩ := hmem
      have hrestAll := hrest
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
      obtain ⟨⟨right, rightCache⟩, hright, hnode⟩ := hrest
      have hpartition := treeCovers_children_sum levels node epoch hvalid
      rw [if_pos hcover] at hpartition
      by_cases hleftCover : TreeCovers levels (Concrete.childNode node false) epoch
      · have hleftLe : leftCache ≤ resultCache :=
          randomOracle_cache_le
            (do
              let right ← Concrete.treeNode parameter secret levels
                (Concrete.childNode node true)
              Concrete.nodeHash parameter ⟨levels, hlevel⟩ node left right :
              OracleComp HashSpec Digest)
            leftCache (digest, resultCache) (by
              simpa only [hlevel, ↓reduceDIte] using hrestAll)
        exact ih (Concrete.childNode node false) (Nat.le_of_succ_le hlevels)
          hleftValid hleftCover initialCache leftCache left hleft (hleftLe.trans hle)
      · have hrightCover : TreeCovers levels (Concrete.childNode node true) epoch := by
          by_contra hrightCover
          simp only [hleftCover, hrightCover, if_false, zero_add] at hpartition
          omega
        have hrightLe : rightCache ≤ resultCache :=
          randomOracle_cache_le
            (Concrete.nodeHash parameter ⟨levels, hlevel⟩ node left right :
              OracleComp HashSpec Digest)
            rightCache (digest, resultCache) (by
              simpa only [hlevel, ↓reduceDIte] using hnode)
        exact ih (Concrete.childNode node true) (Nat.le_of_succ_le hlevels)
          hrightValid hrightCover leftCache rightCache right hright (hrightLe.trans hle)

theorem rootTree_chain_query_cached
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) (chain : ChainIndex) (step : ChainStep)
    (root : Digest) (cache : QueryCache HashSpec)
    (hmem : (root, cache) ∈ support
      ((simulateQ randomOracle
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)).run ∅)) :
    ∃ output, cache
      (Concrete.CacheView.chainInput parameter epoch chain step
        (Wots.walk (Concrete.CacheView.chainStep cache parameter epoch chain)
          0 step.val (secret epoch chain))) = some output := by
  apply treeNode_chain_query_cached_in_largerCache parameter secret epoch chain step
    treeHeight Concrete.rootNode le_rfl
  · unfold TreeSubtreeValid Concrete.rootNode lifetime
    norm_num
  · unfold TreeCovers Concrete.rootNode
    constructor
    · simp
    · simp [lifetime]
  · exact hmem
  · exact le_rfl

end XmssSecurity.Concrete.CacheReplay

namespace XmssSecurity

theorem Concrete.keygen_cache_has_chainInput
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (epoch : Epoch) (chain : ChainIndex) (step : ChainStep) :
    ∃ output, keyResult.2
      (Concrete.CacheView.chainInput keyResult.1.2.parameter epoch chain step
        (Wots.walk
          (Concrete.CacheView.chainStep keyResult.2 keyResult.1.2.parameter epoch chain)
          0 step.val (keyResult.1.2.chainStart epoch chain))) = some output := by
  obtain ⟨parameter, secret, root, hkey, hroot⟩ :=
    Concrete.keygen_support_rootTree keyResult hmem
  rw [hkey]
  exact Concrete.CacheReplay.rootTree_chain_query_cached parameter secret epoch chain step
    root keyResult.2 hroot

theorem Concrete.keygen_cache_chainInput_eq_none_of_ne
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (epoch : Epoch) (chain : ChainIndex) (step : ChainStep) (value : Digest)
    (hne : value ≠ Wots.walk
      (Concrete.CacheView.chainStep keyResult.2 keyResult.1.2.parameter epoch chain)
      0 step.val (keyResult.1.2.chainStart epoch chain)) :
    keyResult.2
      (Concrete.CacheView.chainInput keyResult.1.2.parameter epoch chain step value) = none := by
  obtain ⟨honestOutput, hhonest⟩ :=
    Concrete.keygen_cache_has_chainInput keyResult hmem epoch chain step
  cases hcandidate : keyResult.2
      (Concrete.CacheView.chainInput keyResult.1.2.parameter epoch chain step value) with
  | none => rfl
  | some candidateOutput =>
      exfalso
      apply hne
      apply Concrete.CacheView.chainInput_injective keyResult.1.2.parameter epoch chain step
      apply Concrete.keygen_cache_unique_chainAddress keyResult hmem epoch chain step
        (Concrete.CacheView.chainInput keyResult.1.2.parameter epoch chain step value)
        (Concrete.CacheView.chainInput keyResult.1.2.parameter epoch chain step
          (Wots.walk
            (Concrete.CacheView.chainStep keyResult.2 keyResult.1.2.parameter epoch chain)
            0 step.val (keyResult.1.2.chainStart epoch chain)))
        candidateOutput honestOutput
      · simp [Concrete.CacheView.chainInput]
      · simp [Concrete.CacheView.chainInput]
      · exact hcandidate
      · exact hhonest

/-- Every positive honest chain value is the truncated output of its preceding key-generation query. -/
theorem Concrete.keygen_cache_has_chainValue_preimage
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (epoch : Epoch) (chain : ChainIndex) (digit : Digit)
    (hpositive : 0 < digit.val) :
    ∃ previous : ChainStep, ∃ output,
      previous.val + 1 = digit.val ∧
      keyResult.2
        (Concrete.CacheView.chainInput keyResult.1.2.parameter epoch chain previous
          (Wots.walk
            (Concrete.CacheView.chainStep keyResult.2 keyResult.1.2.parameter epoch chain)
            0 previous.val (keyResult.1.2.chainStart epoch chain))) = some output ∧
      truncateHash output =
        Wots.signChain
          (Concrete.CacheView.chainStep keyResult.2 keyResult.1.2.parameter epoch chain)
          digit (keyResult.1.2.chainStart epoch chain) := by
  let previous : ChainStep := ⟨digit.val - 1, by
    have hdigit := digit.isLt
    omega⟩
  obtain ⟨output, hcached⟩ :=
    Concrete.keygen_cache_has_chainInput keyResult hmem epoch chain previous
  refine ⟨previous, output, by dsimp only [previous]; omega, hcached, ?_⟩
  let step := Concrete.CacheView.chainStep keyResult.2 keyResult.1.2.parameter epoch chain
  calc
    truncateHash output = Concrete.CacheView.digestAt keyResult.2
        (Concrete.CacheView.chainInput keyResult.1.2.parameter epoch chain previous
          (Wots.walk step 0 previous.val
            (keyResult.1.2.chainStart epoch chain))) :=
      (Concrete.CacheView.digestAt_eq_of_cache_eq_some hcached).symm
    _ = step previous.val
        (Wots.walk step 0 previous.val (keyResult.1.2.chainStart epoch chain)) := by
      symm
      exact Concrete.CacheView.chainStep_eq keyResult.2 keyResult.1.2.parameter epoch chain
        previous.val _ previous.isLt
    _ = Wots.signChain step digit (keyResult.1.2.chainStart epoch chain) := by
      unfold Wots.signChain
      rw [show digit.val = previous.val + 1 by dsimp only [previous]; omega]
      simp only [Wots.walk, zero_add]

theorem Concrete.keygen_chainWalk_eq_of_cache_le
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (epoch : Epoch) (chain : ChainIndex) (steps : Nat)
    (hsteps : steps ≤ chainLength - 1) :
    Wots.walk
        (Concrete.CacheView.chainStep keyResult.2 keyResult.1.2.parameter epoch chain)
        0 steps (keyResult.1.2.chainStart epoch chain) =
      Wots.walk
        (Concrete.CacheView.chainStep largerCache keyResult.1.2.parameter epoch chain)
        0 steps (keyResult.1.2.chainStart epoch chain) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      have hstep : steps < chainLength - 1 := by omega
      have ih' := ih (by omega)
      obtain ⟨output, hcached⟩ := Concrete.keygen_cache_has_chainInput keyResult hmem
        epoch chain ⟨steps, hstep⟩
      have hcachedLarger := hle hcached
      rw [ih'] at hcached hcachedLarger
      simp only [Wots.walk, zero_add]
      rw [ih']
      rw [Concrete.CacheView.chainStep_eq _ _ _ _ _ _ hstep,
        Concrete.CacheView.chainStep_eq _ _ _ _ _ _ hstep]
      rw [Concrete.CacheView.digestAt_eq_of_cache_eq_some hcached,
        Concrete.CacheView.digestAt_eq_of_cache_eq_some hcachedLarger]

end XmssSecurity


namespace XmssSecurity

abbrev ChainEdgeIndex := Epoch × ChainStep

def chainTableEdgeInput
    (parameter : PublicParameter) (chain : ChainIndex)
    (table : ChainValueIndex → Digest) (edge : ChainEdgeIndex) : HashInput :=
  Concrete.CacheView.chainInput parameter edge.1 chain edge.2
    (table (edge.1, chainStepDigit edge.2))

def chainStepNextDigit (step : ChainStep) : Digit :=
  ⟨step.val + 1, by
    have hstep := step.isLt
    omega⟩

def chainTableEdgeTarget
    (table : ChainValueIndex → Digest) (edge : ChainEdgeIndex) : Digest :=
  table (edge.1, chainStepNextDigit edge.2)

def ChainTableSeedsMatch
    (secretKey : SecretKey) (chain : ChainIndex)
    (table : ChainValueIndex → Digest) : Prop :=
  ∀ epoch, secretKey.chainStart epoch chain = table (epoch, ⟨0, by simp [chainLength]⟩)

def ChainTableEdgesMatch
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (chain : ChainIndex) (table : ChainValueIndex → Digest) : Prop :=
  ∀ edge, ∃ output,
    cache (chainTableEdgeInput parameter chain table edge) = some output ∧
      truncateHash output = chainTableEdgeTarget table edge

theorem ChainTableEdgesMatch.mono
    {cache larger : QueryCache HashSpec} {parameter : PublicParameter}
    {chain : ChainIndex} {table : ChainValueIndex → Digest}
    (hmatch : ChainTableEdgesMatch cache parameter chain table)
    (hle : cache ≤ larger) :
    ChainTableEdgesMatch larger parameter chain table := by
  intro edge
  obtain ⟨output, hcached, htarget⟩ := hmatch edge
  exact ⟨output, hle hcached, htarget⟩

noncomputable local instance presamplingSampleableChainEdges :
    SampleableType (ChainEdgeIndex → Digest) :=
  SampleableType.ofFintype (ChainEdgeIndex → Digest)

abbrev FlatSecret := Epoch × ChainIndex → Digest

noncomputable local instance presamplingSampleableFlatSecret :
    SampleableType FlatSecret :=
  SampleableType.ofFintype FlatSecret

noncomputable local instance presamplingSampleableSecret :
    SampleableType (Epoch → ChainIndex → Digest) :=
  SampleableType.ofFintype (Epoch → ChainIndex → Digest)

def unflattenSecret (table : FlatSecret) :
    Epoch → ChainIndex → Digest := fun epoch chain => table (epoch, chain)

def flatSecretEquiv :
    (Epoch → ChainIndex → Digest) ≃ FlatSecret where
  toFun secret index := secret index.1 index.2
  invFun := unflattenSecret
  left_inv secret := by
    funext epoch chain
    rfl
  right_inv table := by
    funext index
    rfl

noncomputable def extractFixedChainSeeds
    (chain : ChainIndex) : List Epoch →
      ProbComp (List Digest × FlatSecret)
  | [] => do
      let table ← $ᵗ FlatSecret
      return ([], table)
  | epoch :: epochs => do
      let value ← $ᵗ Digest
      let rest ← extractFixedChainSeeds chain epochs
      return (value :: rest.1,
        Function.update rest.2 (epoch, chain) value)

@[simp]
theorem extractFixedChainSeeds_nil (chain : ChainIndex) :
    extractFixedChainSeeds chain [] = do
      let table ← $ᵗ FlatSecret
      return ([], table) := rfl

theorem extractFixedChainSeeds_cons
    (chain : ChainIndex) (epoch : Epoch) (epochs : List Epoch) :
    extractFixedChainSeeds chain (epoch :: epochs) = do
      let value ← $ᵗ Digest
      let rest ← extractFixedChainSeeds chain epochs
      return (value :: rest.1,
        Function.update rest.2 (epoch, chain) value) := rfl

def fixedChainSeedView (chain : ChainIndex) (epochs : List Epoch)
    (table : FlatSecret) : List Digest × FlatSecret :=
  (epochs.map (fun target => table (target, chain)), table)

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
/-- Exposing the selected chain's seed tape and patching it back into a uniform flat secret preserves the joint distribution of the tape read from that secret. -/
theorem evalDist_extractFixedChainSeeds_eq_uniform
    (chain : ChainIndex) :
    ∀ (epochs : List Epoch), epochs.Nodup →
      𝒟[extractFixedChainSeeds chain epochs] =
      𝒟[fixedChainSeedView chain epochs <$> ($ᵗ FlatSecret)] := by
  intro epochs
  induction epochs with
  | nil =>
      intro _hnodup
      simp only [extractFixedChainSeeds_nil, map_eq_bind_pure_comp,
        bind_pure_comp]
      congr 2
  | cons epoch epochs ih =>
      intro hnodup
      obtain ⟨hnotMem, htailNodup⟩ := List.nodup_cons.mp hnodup
      have htailUpdate (table : FlatSecret) (value : Digest) :
          epochs.map (fun target =>
              Function.update table (epoch, chain) value (target, chain)) =
            epochs.map (fun target => table (target, chain)) := by
        apply List.map_congr_left
        intro target htarget
        rw [Function.update_of_ne]
        intro heq
        have htargetEpoch : target = epoch := congrArg Prod.fst heq
        subst target
        exact hnotMem htarget
      rw [extractFixedChainSeeds_cons]
      calc
        𝒟[$ᵗ Digest >>= fun value =>
            extractFixedChainSeeds chain epochs >>= fun rest =>
              pure (value :: rest.1,
                Function.update rest.2 (epoch, chain) value)] =
            𝒟[$ᵗ Digest >>= fun value =>
              (fixedChainSeedView chain epochs <$> ($ᵗ FlatSecret)) >>=
                  fun rest => pure (value :: rest.1,
                    Function.update rest.2 (epoch, chain) value)] := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro value
          conv_lhs => rw [evalDist_bind]
          conv_rhs => rw [evalDist_bind]
          rw [ih htailNodup]
        _ = 𝒟[$ᵗ Digest >>= fun value =>
              $ᵗ FlatSecret >>= fun table =>
                pure (value :: epochs.map (fun target => table (target, chain)),
                  Function.update table (epoch, chain) value)] := by
          simp [fixedChainSeedView]
        _ = 𝒟[$ᵗ Digest >>= fun value =>
              $ᵗ FlatSecret >>= fun table =>
                pure ((fun updated : FlatSecret =>
                  ((epoch :: epochs).map
                    (fun target => updated (target, chain)), updated))
                  (Function.update table (epoch, chain) value))] := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro value
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro table
          simp [htailUpdate table value]
        _ = 𝒟[fixedChainSeedView chain (epoch :: epochs) <$>
              ($ᵗ FlatSecret)] :=
          OracleComp.evalDist_uniformSample_bind_update_map
            (R := Digest) (epoch, chain)
            (fixedChainSeedView chain (epoch :: epochs))

theorem evalDist_listOfFn_uniform_eq_drawList (count : Nat) :
    𝒟[List.ofFn <$> ($ᵗ (Fin count → Digest))] =
      𝒟[OracleComp.drawList ($ᵗ Digest) count] :=
  (evalDist_drawList_uniform_eq_uniformFunction Digest count).symm

structure ProgrammedFixedChainKeygenView where
  publicKey : PublicKey
  secretKey : SecretKey
  cache : QueryCache HashSpec
  table : ChainValueIndex → Digest

noncomputable def actualFixedChainKeygen
    (chain : ChainIndex) : ProbComp ProgrammedFixedChainKeygenView := do
  let keyResult ← (simulateQ romImpl Concrete.keygen).run ∅
  return {
    publicKey := keyResult.1.1
    secretKey := keyResult.1.2
    cache := keyResult.2
    table := keygenChainValueTable keyResult.2 keyResult.1.2 chain
  }

noncomputable def explicitFixedChainKeygenFromSecret
    (parameter : PublicParameter) (chain : ChainIndex)
    (secret : Epoch → ChainIndex → Digest) :
    ProbComp ProgrammedFixedChainKeygenView := do
  let rootResult ← (simulateQ randomOracle
    (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
      OracleComp HashSpec Digest)).run ∅
  return {
    publicKey := ⟨rootResult.1, parameter⟩
    secretKey := (SecretKey.withoutPrecomputation parameter secret)
    cache := rootResult.2
    table := keygenChainValueTable rootResult.2 (SecretKey.withoutPrecomputation parameter secret) chain
  }

noncomputable def explicitFixedChainKeygen
    (chain : ChainIndex) : ProbComp ProgrammedFixedChainKeygenView := do
  let parameter ← Concrete.samplePublicParameter
  let secret ← Concrete.sampleSecret
  explicitFixedChainKeygenFromSecret parameter chain secret

theorem evalDist_actualFixedChainKeygen_eq_explicit
    (chain : ChainIndex) :
    evalDist (actualFixedChainKeygen chain) =
      evalDist (explicitFixedChainKeygen chain) := by
  unfold actualFixedChainKeygen explicitFixedChainKeygen
    explicitFixedChainKeygenFromSecret Concrete.keygen
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure,
    StateT.run_pure, bind_assoc, pure_bind]
  have hparameter :
      (simulateQ romImpl
        (liftM Concrete.samplePublicParameter)).run ∅ =
        (fun parameter => (parameter, ∅)) <$>
          Concrete.samplePublicParameter := by
    simpa only [romImpl] using
      (roSim.run_liftM
        (randomOracle : QueryImpl HashSpec
          (StateT (QueryCache HashSpec) ProbComp))
        Concrete.samplePublicParameter ∅)
  rw [hparameter]
  simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  have hsecret :
      (simulateQ romImpl (liftM Concrete.sampleSecret)).run ∅ =
        (fun secret => (secret, ∅)) <$> Concrete.sampleSecret := by
    simpa only [romImpl] using
      (roSim.run_liftM
        (randomOracle : QueryImpl HashSpec
          (StateT (QueryCache HashSpec) ProbComp))
        Concrete.sampleSecret ∅)
  rw [hsecret]
  simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro secret
  have htree :
      simulateQ romImpl
          (liftM (Concrete.treeNode parameter secret treeHeight
            Concrete.rootNode : OracleComp HashSpec Digest)) =
        simulateQ
          (randomOracle : QueryImpl HashSpec
            (StateT (QueryCache HashSpec) ProbComp))
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest) := by
    simp only [romImpl]
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec
        (StateT (QueryCache HashSpec) ProbComp))
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)
  rw [htree]

set_option maxRecDepth 100000 in
theorem evalDist_unflatten_uniformFlatSecret_eq_sampleSecret :
    evalDist (unflattenSecret <$> ($ᵗ FlatSecret)) =
      evalDist Concrete.sampleSecret := by
  unfold Concrete.sampleSecret
  exact evalDist_map_bijective_uniform_cross
    (α := FlatSecret) (β := Epoch → ChainIndex → Digest)
    (fun table : FlatSecret => unflattenSecret table)
    flatSecretEquiv.symm.bijective

noncomputable def flatExplicitFixedChainKeygen
    (chain : ChainIndex) : ProbComp ProgrammedFixedChainKeygenView := do
  let parameter ← Concrete.samplePublicParameter
  let flatSecret ← $ᵗ FlatSecret
  explicitFixedChainKeygenFromSecret parameter chain
    (unflattenSecret flatSecret)

theorem evalDist_explicitFixedChainKeygen_eq_flat
    (chain : ChainIndex) :
    evalDist (explicitFixedChainKeygen chain) =
      evalDist (flatExplicitFixedChainKeygen chain) := by
  unfold explicitFixedChainKeygen flatExplicitFixedChainKeygen
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  calc
    evalDist (Concrete.sampleSecret >>= fun secret =>
        explicitFixedChainKeygenFromSecret parameter chain secret) =
        evalDist ((unflattenSecret <$> ($ᵗ FlatSecret)) >>= fun secret =>
          explicitFixedChainKeygenFromSecret parameter chain secret) := by
      conv_lhs => rw [evalDist_bind]
      conv_rhs => rw [evalDist_bind]
      rw [evalDist_unflatten_uniformFlatSecret_eq_sampleSecret]
    _ = evalDist (($ᵗ FlatSecret) >>= fun flatSecret =>
          explicitFixedChainKeygenFromSecret parameter chain
            (unflattenSecret flatSecret)) := by
      simp [map_eq_bind_pure_comp, bind_assoc]

noncomputable def extractedExplicitFixedChainKeygen
    (chain : ChainIndex) : ProbComp ProgrammedFixedChainKeygenView := do
  let parameter ← Concrete.samplePublicParameter
  let secretView ← extractFixedChainSeeds chain allEpochs
  explicitFixedChainKeygenFromSecret parameter chain
    (unflattenSecret secretView.2)

theorem evalDist_flatExplicitFixedChainKeygen_eq_extracted
    (chain : ChainIndex) :
    evalDist (flatExplicitFixedChainKeygen chain) =
      evalDist (extractedExplicitFixedChainKeygen chain) := by
  unfold flatExplicitFixedChainKeygen extractedExplicitFixedChainKeygen
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  symm
  calc
    evalDist (extractFixedChainSeeds chain allEpochs >>= fun secretView =>
        explicitFixedChainKeygenFromSecret parameter chain
          (unflattenSecret secretView.2)) =
        evalDist ((fixedChainSeedView chain allEpochs <$>
          ($ᵗ FlatSecret)) >>= fun secretView =>
            explicitFixedChainKeygenFromSecret parameter chain
              (unflattenSecret secretView.2)) := by
      conv_lhs => rw [evalDist_bind]
      conv_rhs => rw [evalDist_bind]
      rw [evalDist_extractFixedChainSeeds_eq_uniform chain allEpochs allEpochs_nodup]
    _ = evalDist (($ᵗ FlatSecret) >>= fun flatSecret =>
          explicitFixedChainKeygenFromSecret parameter chain
            (unflattenSecret flatSecret)) := by
      simp [map_eq_bind_pure_comp, bind_assoc, fixedChainSeedView]

theorem evalDist_actualFixedChainKeygen_eq_extracted
    (chain : ChainIndex) :
    evalDist (actualFixedChainKeygen chain) =
      evalDist (extractedExplicitFixedChainKeygen chain) :=
  (evalDist_actualFixedChainKeygen_eq_explicit chain).trans
    ((evalDist_explicitFixedChainKeygen_eq_flat chain).trans
      (evalDist_flatExplicitFixedChainKeygen_eq_extracted chain))

theorem keygenChainValueTable_seedsMatch
    (cache : QueryCache HashSpec) (secretKey : SecretKey) (chain : ChainIndex) :
    ChainTableSeedsMatch secretKey chain
      (keygenChainValueTable cache secretKey chain) := by
  intro epoch
  simp [keygenChainValueTable]

set_option maxRecDepth 10000 in
theorem Concrete.keygenChainValueTable_edgesMatch
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (chain : ChainIndex) :
    ChainTableEdgesMatch keyResult.2 keyResult.1.2.parameter chain
      (keygenChainValueTable keyResult.2 keyResult.1.2 chain) := by
  intro edge
  let nextDigit := chainStepNextDigit edge.2
  have hpositive : 0 < nextDigit.val := by
    simp [nextDigit, chainStepNextDigit]
  obtain ⟨previous, output, hprevious, hcached, houtput⟩ :=
    Concrete.keygen_cache_has_chainValue_preimage keyResult hkeygen edge.1 chain
      nextDigit hpositive
  have hstep : previous = edge.2 := by
    apply Fin.ext
    dsimp only [nextDigit, chainStepNextDigit] at hprevious
    omega
  subst previous
  refine ⟨output, ?_, ?_⟩
  · simpa [chainTableEdgeInput, keygenChainValueTable, chainStepDigit] using hcached
  · simpa [chainTableEdgeTarget, keygenChainValueTable, nextDigit,
      Wots.signChain] using houtput

theorem Concrete.CacheReplay.rootTree_chain_query_cached_from_cache
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) (chain : ChainIndex) (step : ChainStep)
    (initialCache : QueryCache HashSpec)
    (result : Digest × QueryCache HashSpec)
    (hresult : result ∈ support
      ((simulateQ randomOracle
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)).run initialCache)) :
    ∃ output, result.2
      (Concrete.CacheView.chainInput parameter epoch chain step
        (Wots.walk
          (Concrete.CacheView.chainStep result.2 parameter epoch chain)
          0 step.val (secret epoch chain))) = some output := by
  apply Concrete.CacheReplay.treeNode_chain_query_cached_in_largerCache
    parameter secret epoch chain step treeHeight Concrete.rootNode le_rfl
  · unfold TreeSubtreeValid Concrete.rootNode lifetime
    norm_num
  · unfold TreeCovers Concrete.rootNode
    constructor
    · simp
    · simp [lifetime]
  · exact hresult
  · exact le_rfl

theorem evalDist_rootTree_run_eq_chainHash_then_rootTree
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) (chain : ChainIndex) (steps : Nat)
    (previous : Digest)
    (initialCache prefixCache : QueryCache HashSpec)
    (hvalid : steps < chainLength - 1)
    (hprefix : (previous, prefixCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.chainWalk parameter epoch chain 0 steps
          (secret epoch chain) :
          OracleComp HashSpec Digest)).run initialCache)) :
    evalDist ((simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run prefixCache) =
      evalDist ((simulateQ randomOracle
        (Concrete.chainHash parameter epoch chain
          ⟨steps, hvalid⟩ previous : OracleComp HashSpec Digest)).run
            prefixCache >>= fun hashResult =>
        (simulateQ randomOracle
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest)).run hashResult.2) := by
  let target := Concrete.CacheView.chainInput parameter epoch chain
    ⟨steps, hvalid⟩ previous
  have hcached : ∀ result ∈ support
      ((simulateQ randomOracle
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)).run prefixCache),
      ∃ output, result.2 target = some output := by
    intro result hresult
    have hprefixLe := Concrete.CacheReplay.randomOracle_cache_le
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest) prefixCache result hresult
    have hreplay := Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
      (Concrete.chainWalk parameter epoch chain 0 steps
        (secret epoch chain) :
        OracleComp HashSpec Digest)
      initialCache prefixCache result.2 previous hprefix hprefixLe
    rw [Concrete.CacheReplay.eval_chainWalk] at hreplay
    obtain ⟨output, houtput⟩ :=
      Concrete.CacheReplay.rootTree_chain_query_cached_from_cache
        parameter secret epoch chain ⟨steps, hvalid⟩
        prefixCache result hresult
    refine ⟨output, ?_⟩
    change result.2
      (Concrete.CacheView.chainInput parameter epoch chain
        ⟨steps, hvalid⟩ previous) = some output
    rw [← hreplay]
    exact houtput
  calc
    evalDist ((simulateQ randomOracle
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)).run prefixCache) =
        evalDist ((randomOracle (spec := HashSpec) target).run prefixCache >>=
          fun queryResult =>
            (simulateQ randomOracle
              (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                OracleComp HashSpec Digest)).run queryResult.2) :=
      OracleComp.evalDist_randomOracle_run_eq_query_then_of_cached
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest) prefixCache target hcached
    _ = evalDist ((simulateQ randomOracle
          (Concrete.chainHash parameter epoch chain
            ⟨steps, hvalid⟩ previous :
              OracleComp HashSpec Digest)).run prefixCache >>= fun hashResult =>
          (simulateQ randomOracle
            (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
              OracleComp HashSpec Digest)).run hashResult.2) := by
      simp [Concrete.chainHash, Concrete.tweakableHash, Concrete.oracleHash,
        target, Concrete.CacheView.chainInput]

theorem evalDist_rootTree_run_eq_chainWalk_then_rootTree
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) (chain : ChainIndex) (steps : Nat)
    (hsteps : steps ≤ chainLength - 1)
    (initialCache : QueryCache HashSpec) :
    evalDist ((simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run initialCache) =
      evalDist ((simulateQ randomOracle
        (Concrete.chainWalk parameter epoch chain 0 steps
          (secret epoch chain) : OracleComp HashSpec Digest)).run initialCache >>=
            fun chainResult =>
        (simulateQ randomOracle
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest)).run chainResult.2) := by
  induction steps generalizing initialCache with
  | zero =>
      simp [Concrete.chainWalk]
  | succ steps ih =>
      have hvalid : steps < chainLength - 1 := by omega
      calc
        evalDist ((simulateQ randomOracle
            (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
              OracleComp HashSpec Digest)).run initialCache) =
            evalDist ((simulateQ randomOracle
              (Concrete.chainWalk parameter epoch chain 0 steps
                (secret epoch chain) : OracleComp HashSpec Digest)).run
                  initialCache >>= fun prefixResult =>
              (simulateQ randomOracle
                (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                  OracleComp HashSpec Digest)).run prefixResult.2) :=
          ih (by omega) initialCache
        _ = evalDist ((simulateQ randomOracle
              (Concrete.chainWalk parameter epoch chain 0 steps
                (secret epoch chain) : OracleComp HashSpec Digest)).run
                  initialCache >>= fun prefixResult =>
              (simulateQ randomOracle
                (Concrete.chainHash parameter epoch chain ⟨steps, hvalid⟩
                  prefixResult.1 : OracleComp HashSpec Digest)).run
                    prefixResult.2 >>= fun hashResult =>
              (simulateQ randomOracle
                (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                  OracleComp HashSpec Digest)).run hashResult.2) := by
          apply evalDist_bind_congr
          intro prefixResult hprefix
          exact evalDist_rootTree_run_eq_chainHash_then_rootTree
            parameter secret epoch chain steps prefixResult.1 initialCache
            prefixResult.2 hvalid hprefix
        _ = evalDist ((simulateQ randomOracle
              (Concrete.chainWalk parameter epoch chain 0 (steps + 1)
                (secret epoch chain) : OracleComp HashSpec Digest)).run
                  initialCache >>= fun chainResult =>
              (simulateQ randomOracle
                (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                  OracleComp HashSpec Digest)).run chainResult.2) := by
          rw [Concrete.chainWalk, simulateQ_bind, StateT.run_bind]
          simp only [zero_add]
          simp only [hvalid, ↓reduceDIte, bind_assoc]

theorem Concrete.chainTrajectory_back_map_eq_chainWalk
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (position steps : Nat) (value : Digest) :
    Vector.back <$> Concrete.chainTrajectory parameter epoch chain position steps value =
      (Concrete.chainWalk parameter epoch chain position steps value :
        OracleComp HashSpec Digest) := by
  induction steps with
  | zero =>
      rw [Concrete.chainTrajectory_zero]
      simp only [map_pure, Concrete.chainWalk]
      simp [Vector.back_ofFn]
  | succ steps ih =>
      calc
        Vector.back <$>
            Concrete.chainTrajectory parameter epoch chain position
              (steps + 1) value =
            (Vector.back <$> Concrete.chainTrajectory parameter epoch chain
              position steps value) >>= fun previous =>
              if hvalid : position + steps < chainLength - 1 then
                Concrete.chainHash parameter epoch chain
                  ⟨position + steps, hvalid⟩ previous
              else pure 0 := by
          rw [Concrete.chainTrajectory_succ]
          by_cases hvalid : position + steps < chainLength - 1
          · simp [hvalid, map_eq_bind_pure_comp, bind_assoc]
          · simp [hvalid, map_eq_bind_pure_comp, bind_assoc]
        _ = Concrete.chainWalk parameter epoch chain position
            (steps + 1) value := by
          rw [ih]
          rfl

theorem evalDist_chainTrajectory_run_cache_eq_chainWalk_run_cache
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (position steps : Nat) (value : Digest)
    (initialCache : QueryCache HashSpec) :
    evalDist ((fun result : Vector Digest (steps + 1) × QueryCache HashSpec =>
      (result.1.back, result.2)) <$>
        (simulateQ randomOracle
          (Concrete.chainTrajectory parameter epoch chain position steps value)).run
            initialCache) =
      evalDist ((simulateQ randomOracle
        (Concrete.chainWalk parameter epoch chain position steps value :
          OracleComp HashSpec Digest)).run initialCache) := by
  rw [← StateT.run_map]
  rw [← simulateQ_map]
  rw [Concrete.chainTrajectory_back_map_eq_chainWalk]

theorem evalDist_rootTree_run_eq_chainTrajectory_then_rootTree
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) (chain : ChainIndex) (steps : Nat)
    (hsteps : steps ≤ chainLength - 1)
    (initialCache : QueryCache HashSpec) :
    evalDist ((simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run initialCache) =
      evalDist ((simulateQ randomOracle
        (Concrete.chainTrajectory parameter epoch chain 0 steps
          (secret epoch chain))).run initialCache >>= fun trajectoryResult =>
        (simulateQ randomOracle
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest)).run trajectoryResult.2) := by
  calc
    evalDist ((simulateQ randomOracle
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)).run initialCache) =
        evalDist ((simulateQ randomOracle
          (Concrete.chainWalk parameter epoch chain 0 steps
            (secret epoch chain) : OracleComp HashSpec Digest)).run initialCache >>=
              fun chainResult =>
          (simulateQ randomOracle
            (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
              OracleComp HashSpec Digest)).run chainResult.2) :=
      evalDist_rootTree_run_eq_chainWalk_then_rootTree parameter secret epoch
        chain steps hsteps initialCache
    _ = evalDist (((fun result : Vector Digest (steps + 1) × QueryCache HashSpec =>
          (result.1.back, result.2)) <$>
            (simulateQ randomOracle
              (Concrete.chainTrajectory parameter epoch chain 0 steps
                (secret epoch chain))).run initialCache) >>= fun chainResult =>
          (simulateQ randomOracle
            (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
              OracleComp HashSpec Digest)).run chainResult.2) := by
      conv_lhs => rw [evalDist_bind]
      conv_rhs => rw [evalDist_bind]
      rw [evalDist_chainTrajectory_run_cache_eq_chainWalk_run_cache]
    _ = evalDist ((simulateQ randomOracle
          (Concrete.chainTrajectory parameter epoch chain 0 steps
            (secret epoch chain))).run initialCache >>= fun trajectoryResult =>
          (simulateQ randomOracle
            (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
              OracleComp HashSpec Digest)).run trajectoryResult.2) := by
      simp [map_eq_bind_pure_comp, bind_assoc]

noncomputable def Concrete.fixedSeedChainTrajectoriesFromCache
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) :
    QueryCache HashSpec → List Epoch →
      ProbComp (List (Vector Digest (steps + 1)) × QueryCache HashSpec)
  | cache, [] => pure ([], cache)
  | cache, epoch :: epochs => do
      let first ← (simulateQ randomOracle
        (Concrete.chainTrajectory parameter epoch chain 0 steps
          (secret epoch chain))).run cache
      let rest ← Concrete.fixedSeedChainTrajectoriesFromCache
        parameter secret chain steps first.2 epochs
      return (first.1 :: rest.1, rest.2)

@[simp]
theorem Concrete.fixedSeedChainTrajectoriesFromCache_nil
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) (cache : QueryCache HashSpec) :
    Concrete.fixedSeedChainTrajectoriesFromCache parameter secret chain steps
      cache [] = pure ([], cache) := rfl

theorem Concrete.fixedSeedChainTrajectoriesFromCache_cons
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) (cache : QueryCache HashSpec)
    (epoch : Epoch) (epochs : List Epoch) :
    Concrete.fixedSeedChainTrajectoriesFromCache parameter secret chain steps
      cache (epoch :: epochs) = (do
        let first ← (simulateQ randomOracle
          (Concrete.chainTrajectory parameter epoch chain 0 steps
            (secret epoch chain))).run cache
        let rest ← Concrete.fixedSeedChainTrajectoriesFromCache
          parameter secret chain steps first.2 epochs
        return (first.1 :: rest.1, rest.2)) := rfl

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem Concrete.fixedSeedChainTrajectoriesFromCache_support_info
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) :
    ∀ (epochs : List Epoch) (cache : QueryCache HashSpec)
      (result : List (Vector Digest (steps + 1)) × QueryCache HashSpec),
      result ∈ support
        (Concrete.fixedSeedChainTrajectoriesFromCache parameter secret chain
          steps cache epochs) →
      cache ≤ result.2 ∧ result.1.length = epochs.length ∧
        List.Forall₂
          (fun epoch trajectory =>
            evalWithAnswerFn (Concrete.CacheReplay.answerFn result.2)
              (Concrete.chainTrajectory parameter epoch chain 0 steps
                (secret epoch chain)) = trajectory)
          epochs result.1 := by
  intro epochs
  induction epochs with
  | nil =>
      intro cache result hresult
      simp only [Concrete.fixedSeedChainTrajectoriesFromCache_nil,
        support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨le_rfl, rfl, List.Forall₂.nil⟩
  | cons epoch epochs ih =>
      intro cache result hresult
      rw [Concrete.fixedSeedChainTrajectoriesFromCache_cons,
        mem_support_bind_iff] at hresult
      obtain ⟨first, hfirst, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      obtain ⟨hfirstCacheLe, hlength, hpairs⟩ :=
        ih first.2 rest hrest
      constructor
      · exact (Concrete.CacheReplay.randomOracle_cache_le
          (Concrete.chainTrajectory parameter epoch chain 0 steps
            (secret epoch chain)) cache first hfirst).trans hfirstCacheLe
      · constructor
        · simp [hlength]
        · apply List.Forall₂.cons
          · exact Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
              (Concrete.chainTrajectory parameter epoch chain 0 steps
                (secret epoch chain)) cache first.2 rest.2 first.1 hfirst
                hfirstCacheLe
          · exact hpairs

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem Concrete.fixedSeedChainTrajectoriesFromCache_replay_in_largerCache
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) :
    ∀ (epochs : List Epoch) (cache : QueryCache HashSpec)
      (result : List (Vector Digest (steps + 1)) × QueryCache HashSpec)
      (largerCache : QueryCache HashSpec),
      result ∈ support
        (Concrete.fixedSeedChainTrajectoriesFromCache parameter secret chain
          steps cache epochs) →
      result.2 ≤ largerCache →
      List.Forall₂
        (fun epoch trajectory =>
          evalWithAnswerFn (Concrete.CacheReplay.answerFn largerCache)
            (Concrete.chainTrajectory parameter epoch chain 0 steps
              (secret epoch chain)) = trajectory)
        epochs result.1 := by
  intro epochs
  induction epochs with
  | nil =>
      intro cache result largerCache hresult _hle
      simp only [Concrete.fixedSeedChainTrajectoriesFromCache_nil,
        support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact List.Forall₂.nil
  | cons epoch epochs ih =>
      intro cache result largerCache hresult hlarger
      rw [Concrete.fixedSeedChainTrajectoriesFromCache_cons,
        mem_support_bind_iff] at hresult
      obtain ⟨first, hfirst, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      have hrestInfo :=
        Concrete.fixedSeedChainTrajectoriesFromCache_support_info parameter
          secret chain steps epochs first.2 rest hrest
      apply List.Forall₂.cons
      · exact Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
          (Concrete.chainTrajectory parameter epoch chain 0 steps
            (secret epoch chain)) cache first.2 largerCache first.1 hfirst
            (hrestInfo.1.trans hlarger)
      · exact ih first.2 rest largerCache hrest hlarger

theorem Concrete.fixedSeedChainTrajectoriesFromCache_table_eq_in_largerCache
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex)
    (result : List FullChainTrajectory × QueryCache HashSpec)
    (largerCache : QueryCache HashSpec)
    (hresult : result ∈ support
      (Concrete.fixedSeedChainTrajectoriesFromCache parameter secret chain
        (chainLength - 1) ∅ allEpochs))
    (hle : result.2 ≤ largerCache) :
    chainValueTableOfList result.1 =
      keygenChainValueTable largerCache (SecretKey.withoutPrecomputation parameter secret) chain := by
  have hinfo := Concrete.fixedSeedChainTrajectoriesFromCache_support_info
    parameter secret chain (chainLength - 1) allEpochs ∅ result hresult
  have hpairs :=
    Concrete.fixedSeedChainTrajectoriesFromCache_replay_in_largerCache
      parameter secret chain (chainLength - 1) allEpochs ∅ result largerCache
      hresult hle
  funext index
  unfold chainValueTableOfList
  split
  · rename_i htableLength
    let position := epochPosition index.1
    have hresultPosition : position.val < result.1.length := by
      rw [← htableLength]
      exact position.isLt
    have hpair := hpairs.get position.isLt hresultPosition
    have hepoch : allEpochs.get position = index.1 := by
      exact allEpochs_get_epochPosition index.1
    rw [hepoch] at hpair
    have hvalue := congrArg
      (fun trajectory : FullChainTrajectory =>
        trajectory[index.2.val]'(by
          have hdigit := index.2.isLt
          omega)) hpair
    rw [Concrete.chainTrajectory_getElem] at hvalue
    exact hvalue.symm
  · rename_i htableLength
    exact (htableLength hinfo.2.1.symm).elim

theorem evalDist_rootTree_run_eq_fixedSeedTrajectories_then_rootTree
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) (hsteps : steps ≤ chainLength - 1)
    (epochs : List Epoch) (initialCache : QueryCache HashSpec) :
    evalDist ((simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run initialCache) =
      evalDist (Concrete.fixedSeedChainTrajectoriesFromCache
        parameter secret chain steps initialCache epochs >>= fun trajectoryResult =>
        (simulateQ randomOracle
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest)).run trajectoryResult.2) := by
  induction epochs generalizing initialCache with
  | nil =>
      simp
  | cons epoch epochs ih =>
      calc
        evalDist ((simulateQ randomOracle
            (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
              OracleComp HashSpec Digest)).run initialCache) =
            evalDist ((simulateQ randomOracle
              (Concrete.chainTrajectory parameter epoch chain 0 steps
                (secret epoch chain))).run initialCache >>= fun first =>
              (simulateQ randomOracle
                (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                  OracleComp HashSpec Digest)).run first.2) :=
          evalDist_rootTree_run_eq_chainTrajectory_then_rootTree
            parameter secret epoch chain steps hsteps initialCache
        _ = evalDist ((simulateQ randomOracle
              (Concrete.chainTrajectory parameter epoch chain 0 steps
                (secret epoch chain))).run initialCache >>= fun first =>
              Concrete.fixedSeedChainTrajectoriesFromCache
                parameter secret chain steps first.2 epochs >>= fun rest =>
              (simulateQ randomOracle
                (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                  OracleComp HashSpec Digest)).run rest.2) := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro first
          exact ih first.2
        _ = evalDist (Concrete.fixedSeedChainTrajectoriesFromCache parameter
              secret chain steps initialCache (epoch :: epochs) >>=
                fun trajectoryResult =>
              (simulateQ randomOracle
                (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                  OracleComp HashSpec Digest)).run trajectoryResult.2) := by
          rw [Concrete.fixedSeedChainTrajectoriesFromCache_cons]
          simp only [bind_assoc, pure_bind]

noncomputable def chronologicallyWarmedExtractedFixedChainKeygen
    (chain : ChainIndex) : ProbComp ProgrammedFixedChainKeygenView := do
  let parameter ← Concrete.samplePublicParameter
  let secretView ← extractFixedChainSeeds chain allEpochs
  let secret := unflattenSecret secretView.2
  let rootResult ← (do
    let trajectoryResult ← Concrete.fixedSeedChainTrajectoriesFromCache
      parameter secret chain (chainLength - 1) ∅ allEpochs
    (simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run trajectoryResult.2)
  return {
    publicKey := ⟨rootResult.1, parameter⟩
    secretKey := (SecretKey.withoutPrecomputation parameter secret)
    cache := rootResult.2
    table := keygenChainValueTable rootResult.2 (SecretKey.withoutPrecomputation parameter secret) chain
  }

theorem evalDist_extractedFixedChainKeygen_eq_chronologicallyWarmed
    (chain : ChainIndex) :
    evalDist (extractedExplicitFixedChainKeygen chain) =
      evalDist (chronologicallyWarmedExtractedFixedChainKeygen chain) := by
  unfold extractedExplicitFixedChainKeygen
    chronologicallyWarmedExtractedFixedChainKeygen
    explicitFixedChainKeygenFromSecret
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro secretView
  let secret := unflattenSecret secretView.2
  let makeView : Digest × QueryCache HashSpec →
      ProbComp ProgrammedFixedChainKeygenView := fun rootResult =>
    pure ({
      publicKey := ⟨rootResult.1, parameter⟩
      secretKey := (SecretKey.withoutPrecomputation parameter secret)
      cache := rootResult.2
      table := keygenChainValueTable rootResult.2 (SecretKey.withoutPrecomputation parameter secret) chain
    } : ProgrammedFixedChainKeygenView)
  change evalDist ((simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run ∅ >>= makeView) =
    evalDist ((Concrete.fixedSeedChainTrajectoriesFromCache parameter secret
      chain (chainLength - 1) ∅ allEpochs >>= fun trajectoryResult =>
        (simulateQ randomOracle
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest)).run trajectoryResult.2) >>= makeView)
  conv_lhs => rw [evalDist_bind]
  conv_rhs => rw [evalDist_bind]
  rw [evalDist_rootTree_run_eq_fixedSeedTrajectories_then_rootTree
    parameter secret chain (chainLength - 1) le_rfl allEpochs ∅]

theorem evalDist_actualFixedChainKeygen_eq_chronologicallyWarmed
    (chain : ChainIndex) :
    evalDist (actualFixedChainKeygen chain) =
      evalDist (chronologicallyWarmedExtractedFixedChainKeygen chain) :=
  (evalDist_actualFixedChainKeygen_eq_extracted chain).trans
    (evalDist_extractedFixedChainKeygen_eq_chronologicallyWarmed chain)

end XmssSecurity

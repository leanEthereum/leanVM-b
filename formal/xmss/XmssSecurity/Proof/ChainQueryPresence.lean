import XmssSecurity.Proof.QueryPresence
import XmssSecurity.Proof.StatementLemmas

open OracleComp OracleSpec

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

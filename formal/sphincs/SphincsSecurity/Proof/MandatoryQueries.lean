import SphincsSecurity.Proof.CacheSize
import SphincsSecurity.Proof.Cached
import SphincsSecurity.Proof.Secrets
import SphincsSecurity.Proof.SettledPath
import SphincsSecurity.Proof.Support

/-!
# Mandatory hash queries

The public-key root computation settles a one-time leaf and all of its chains. Their domains differ,
so every root cache has at least `numChains = 42` entries. Consequently every complete-game
hash-query bound is at least 42, which absorbs the constant terms in the final security arithmetic.
-/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

theorem QueryCache.two_le_enncard_of_cached_of_ne
    {cache : QueryCache HashSpec} {left right : HashInput}
    (hleft : cache left ≠ none) (hright : cache right ≠ none) (hne : left ≠ right) :
    (2 : ℝ≥0∞) ≤ QueryCache.enncard cache := by
  obtain ⟨leftAnswer, hleftAnswer⟩ := Option.ne_none_iff_exists'.mp hleft
  obtain ⟨rightAnswer, hrightAnswer⟩ := Option.ne_none_iff_exists'.mp hright
  let leftEntry : (input : HashInput) × HashOutput := ⟨left, leftAnswer⟩
  let rightEntry : (input : HashInput) × HashOutput := ⟨right, rightAnswer⟩
  have hentryNe : leftEntry ≠ rightEntry := by
    intro heq
    exact hne (congrArg Sigma.fst heq)
  have hsubset : ({leftEntry, rightEntry} : Set ((input : HashInput) × HashOutput)) ⊆
      cache.toSet := by
    intro entry hentry
    rcases hentry with hentry | hentry
    · subst entry
      exact hleftAnswer
    · have hentryEq : entry = rightEntry := by simpa using hentry
      subst entry
      exact hrightAnswer
  have hcard := Set.encard_le_encard hsubset
  rw [Set.encard_pair hentryNe] at hcard
  simpa only [QueryCache.enncard, ENat.toENNReal_ofNat] using ENat.toENNReal_mono hcard

theorem cachedInput_ne_of_position_ne
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (cache : QueryCache HashSpec) {left right : Position} (hne : left ≠ right) :
    cachedInput parameter otsSecret ftsSecret cache left ≠
      cachedInput parameter otsSecret ftsSecret cache right := by
  intro hinput
  have hdomain : left.domain = right.domain :=
    (tweakableHashInput_injective parameter left.domain_inRange right.domain_inRange
      (by simpa only [cachedInput, honestInput] using hinput)).1
  exact hne (Position.domain_injective hdomain)

namespace Concrete

theorem numChains_le_of_root_queryBound
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (q : Nat)
    (hbound : (liftM
      (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree) :
        OracleComp HashSpec Digest) : OracleComp OracleWorld Digest).IsQueryBoundP
          (· matches Sum.inr _) q) :
    numChains ≤ q := by
  let rootComputation : OracleComp HashSpec Digest :=
    treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree)
  let answerFn : QueryImpl HashSpec Id := fromCache ∅
  have hagrees : (∅ : QueryCache HashSpec).AgreesWithFn answerFn :=
    agreesWithFn_fromCache ∅
  obtain ⟨rootCache, hroot⟩ :=
    (exists_agreesWithFn_evalWithAnswerFn_eq_iff_mem_support rootComputation ∅
      (evalWithAnswerFn answerFn rootComputation)).mp ⟨answerFn, hagrees, rfl⟩
  obtain ⟨_, replayFn, hreplayAgrees, _, hcached⟩ :=
    exists_answerFn_replay_of_mem_support rootComputation ∅
      (evalWithAnswerFn answerFn rootComputation) rootCache hroot
  let rootPosition : Position :=
    .node topLayer rootTree ⟨layerHeight topLayer - 1, by decide⟩ ⟨0, by positivity⟩
  have hrootSettled : Settled parameter otsSecret (fun _ _ _ => 0) rootCache rootPosition := by
    exact settled_treeRoot_of_cachedRun (ftsSecret := fun _ _ _ => 0) hreplayAgrees
      topLayer rootTree hcached
  let leafIdx : LeafIndex := 0
  have hleafSettled :
      Settled parameter otsSecret (fun _ _ _ => 0) rootCache
        (.leaf topLayer rootTree leafIdx) :=
    (settled_tree_path_of_settled_root topLayer rootTree leafIdx (by
      norm_num [leafIdx, layerHeight, topLayer, maxLayerHeight, numLayers]) hrootSettled).1
  let chainPosition : ChainIndex → Position := fun chainIdx =>
    .chain topLayer rootTree leafIdx chainIdx Position.lastChainStep
  have hchainSettled : ∀ chainIdx,
      Settled parameter otsSecret (fun _ _ _ => 0) rootCache (chainPosition chainIdx) := by
    intro chainIdx
    exact settled_chain_of_settled_leaf topLayer rootTree leafIdx hleafSettled chainIdx
      Position.lastChainStep.val Position.lastChainStep.isLt
  let chainAnswer : ChainIndex → HashOutput := fun chainIdx =>
    Classical.choose (Option.ne_none_iff_exists'.mp (hchainSettled chainIdx).cached)
  have hchainAnswer : ∀ chainIdx,
      rootCache (cachedInput parameter otsSecret (fun _ _ _ => 0) rootCache
        (chainPosition chainIdx)) = some (chainAnswer chainIdx) := by
    intro chainIdx
    exact Classical.choose_spec (Option.ne_none_iff_exists'.mp (hchainSettled chainIdx).cached)
  let chainEmbedding : (Set.univ : Set ChainIndex) ↪ rootCache.toSet :=
    ⟨fun chainIdx => ⟨⟨cachedInput parameter otsSecret (fun _ _ _ => 0) rootCache
          (chainPosition chainIdx.1), chainAnswer chainIdx.1⟩, hchainAnswer chainIdx.1⟩,
      by
        intro left right heq
        apply Subtype.ext
        by_contra hne
        have hinput := congrArg (fun entry : rootCache.toSet => entry.1.1) heq
        exact cachedInput_ne_of_position_ne parameter otsSecret (fun _ _ _ => 0) rootCache
          (by simpa [chainPosition, Fin.ext_iff] using hne) hinput⟩
  have hencard : (Set.univ : Set ChainIndex).encard ≤ rootCache.toSet.encard :=
    chainEmbedding.encard_le
  have hcacheLower : (numChains : ℝ≥0∞) ≤ QueryCache.enncard rootCache := by
    have huniv : (Set.univ : Set ChainIndex).encard = (numChains : ENat) := by
      rw [Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin]
    have hreal := ENat.toENNReal_mono hencard
    rw [huniv] at hreal
    simpa only [QueryCache.enncard, ENat.toENNReal_coe] using hreal
  have hrootLifted :
      ((evalWithAnswerFn answerFn rootComputation, rootCache) ∈ support
        ((simulateQ romImpl
          (liftM rootComputation : OracleComp OracleWorld Digest)).run ∅)) := by
    rw [simulateQ_romImpl_liftM]
    exact hroot
  have hcacheUpper : QueryCache.enncard rootCache ≤ (q : ℝ≥0∞) :=
    simulateQ_romImpl_enncard_le_queryBound
      (liftM rootComputation : OracleComp OracleWorld Digest) q hbound
      (evalWithAnswerFn answerFn rootComputation, rootCache) hrootLifted
  exact_mod_cast hcacheLower.trans hcacheUpper

theorem two_le_of_root_queryBound
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (q : Nat)
    (hbound : (liftM
      (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree) :
        OracleComp HashSpec Digest) : OracleComp OracleWorld Digest).IsQueryBoundP
          (· matches Sum.inr _) q) :
    2 ≤ q := by
  exact (show 2 ≤ numChains by norm_num [numChains]).trans
    (numChains_le_of_root_queryBound parameter otsSecret q hbound)

theorem two_le_of_hasHashQueryBound
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    2 ≤ q := by
  have hgame := isQueryBoundP_gameAfterSecrets adversary q hq hparameter hots hfts
  rw [gameAfterSecrets] at hgame
  exact two_le_of_root_queryBound parameter otsSecret q (IsQueryBoundP.of_bind_left hgame)

theorem numChains_le_of_hasHashQueryBound
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    numChains ≤ q := by
  have hgame := isQueryBoundP_gameAfterSecrets adversary q hq hparameter hots hfts
  rw [gameAfterSecrets] at hgame
  exact numChains_le_of_root_queryBound parameter otsSecret q (IsQueryBoundP.of_bind_left hgame)

end Concrete

end SphincsSecurity

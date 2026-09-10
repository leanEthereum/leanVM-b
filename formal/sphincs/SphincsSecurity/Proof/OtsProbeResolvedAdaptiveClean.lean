import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeResolvedSampling

/-!
# Clean terminal lift for adaptive one-time probes

The canonical delayed failure is transported to the uniformly completed clean interpreter. The
clean endpoint itself is already the generic `q * 2^-128` lazy-probe bound.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedTreeRoot
attribute [local semireducible] sampleOtsSecrets

noncomputable def constantDigestAnswer (digest : Digest) : QueryImpl HashSpec Id :=
  fun _ => hashOutputOfDigest digest

@[simp] theorem eval_tweakableHash_constantDigestAnswer
    (digest : Digest) (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) :
    evalWithAnswerFn (constantDigestAnswer digest)
      (tweakableHash parameter domain payload) = digest := by
  rw [Concrete.eval_tweakableHash]
  exact truncateHash_hashOutputOfDigest digest

theorem eval_treeNode_constantDigestAnswer
    (digest : Digest) (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (secret : LeafIndex → ChainIndex → Digest) :
    ∀ level nodeIdx,
      evalWithAnswerFn (constantDigestAnswer digest)
        (treeNode parameter lay tree secret level nodeIdx) = digest := by
  intro level
  induction level with
  | zero =>
      intro nodeIdx
      rw [treeNode_zero_eq]
      simp only [evalWithAnswerFn_bind]
      exact eval_tweakableHash_constantDigestAnswer digest parameter _ _
  | succ level ih =>
      intro nodeIdx
      rw [treeNode_succ_eq]
      simp [evalWithAnswerFn_bind, ih]

theorem mem_support_treeRoot_all
    (digest : Digest) (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (secret : LeafIndex → ChainIndex → Digest) :
    digest ∈ support (treeRoot parameter lay tree secret : OracleComp HashSpec Digest) := by
  have hsim := (OracleComp.exists_agreesWithFn_evalWithAnswerFn_eq_iff_mem_support
    (treeRoot parameter lay tree secret) ∅ digest).mp ⟨constantDigestAnswer digest,
      (by simp [QueryCache.AgreesWithFn]), by
        simp only [treeRoot]
        exact eval_treeNode_constantDigestAnswer digest parameter lay tree secret
          (layerHeight lay) 0⟩
  obtain ⟨cache, hcache⟩ := hsim
  apply OracleComp.support_simulateQ_run'_subset
    (randomOracle : QueryImpl HashSpec _) (treeRoot parameter lay tree secret) ∅
  rw [StateT.run'_eq, support_map]
  exact ⟨(digest, cache), hcache, rfl⟩

theorem isQueryBoundP_gameRest_all_roots
    (adversary : Adversary) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets)
    (root : Digest) :
    (gameRest scheme adversary ⟨root, parameter⟩
      ⟨parameter, root, otsSecret, ftsSecret⟩).IsQueryBoundP
        (· matches Sum.inr _) q := by
  have hgame := Concrete.isQueryBoundP_gameAfterSecrets adversary q hq hparameter hots hfts
  rw [Concrete.gameAfterSecrets] at hgame
  have hroot : root ∈ support
      (OracleComp.liftComp
        (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree) :
          OracleComp HashSpec Digest)
        OracleWorld) := by
    rw [OracleComp.support_liftComp]
    exact mem_support_treeRoot_all root parameter topLayer rootTree
      (otsSecret topLayer rootTree)
  exact isQueryBoundP_of_bind hgame root (by
    simpa only [OracleComp.liftComp_eq_liftM] using hroot)

theorem mem_support_sampleOtsSecrets_all
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) :
    otsSecret ∈ support sampleOtsSecrets := by
  change otsSecret ∈ support
    (@SampleableType.selectElem
      (Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
      otsSecretsSampleableType)
  exact otsSecretsSampleableType.mem_support_selectElem otsSecret

theorem isQueryBoundP_expandedRetained_all_tables_roots
    (adversary : Adversary) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets)
    (root : Digest) :
    (simulateQ
      (SphincsSecurity.expandedAdversaryImpl
        (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
      (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
        (· matches Sum.inr _) q := by
  let secretKey : SecretKey :=
    ⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩
  have hrest := isQueryBoundP_gameRest_all_roots adversary q hq parameter hparameter
    secretKey.otsSecret (mem_support_sampleOtsSecrets_all secretKey.otsSecret)
    ftsSecret hfts root
  have hbound :=
    Concrete.FtsProbeSimulation.simulateQ_expanded_retainedGameRestComputation_isQueryBoundP
      adversary secretKey q hrest
  convert hbound using 1 <;> rfl

noncomputable def rejectingHashOutput : HashOutput :=
  hashOutputCoordinatesEquiv.symm
    ((default, ⟨1, by norm_num [ftsTreeHeight]⟩), 0)

noncomputable def rejectingRomAnswer : QueryImpl OracleWorld Id
  | .inl n => (0 : Fin (n + 1))
  | .inr _ => rejectingHashOutput

@[simp] theorem eval_lift_hash_rejecting (input : HashInput) :
    evalWithAnswerFn rejectingRomAnswer
      (liftM (HashSpec.query input) : OracleComp OracleWorld HashOutput) =
        rejectingHashOutput := by
  rfl

theorem startTableAgrees_completedStartTable
    (state : LazyRevealProbe.State Coordinate) (base : OtsSecretIndex → HashOutput) :
    StartTableAgrees state (completedStartTable state base) := by
  intro index output hvalue
  simp [completedStartTable, hvalue]

theorem maskedPublishedTreeRoot_probeFree : ProbeFree maskedPublishedTreeRoot := by
  intro cache
  rw [maskedPublishedTreeRoot_eq, StateT.run_bind]
  apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
    (maskedTreeRoot_probeFree topLayer rootTree cache)
  intro rootResult _hroot
  rcases rootResult with ⟨root, nextCache⟩
  rw [StateT.run_bind]
  exact OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
    (publishCoordinate_probeFree (.position (.node topLayer rootTree
      ⟨layerHeight topLayer - 1, by norm_num [layerHeight, topLayer, maxLayerHeight]⟩ 0))
        nextCache)
    (fun _ _ => by simp)

end SphincsSecurity.Concrete.OtsProbeSimulation

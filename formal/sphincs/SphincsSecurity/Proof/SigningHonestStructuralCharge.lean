import SphincsSecurity.Proof.SigningHonestStructuralQueries
import SphincsSecurity.Proof.RootStructuralCharge

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

noncomputable def signingStructuralCharge (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  parentStoppedEncodingQueryCharge secretKey cache input + ftsParentQueryCharge secretKey cache input

theorem expectedQueryCharge_eq_zero_of_honest_structural
    (secretKey : SecretKey) (computation : OracleComp HashSpec α)
    (hsettling : ∀ f, SettlingRun secretKey.parameter secretKey.otsSecret secretKey.ftsSecret f computation)
    (hhonest : ∀ f, HonestStructuralQueries secretKey.parameter secretKey.otsSecret secretKey.ftsSecret f computation)
    (cache : QueryCache HashSpec) :
    expectedQueryCharge (signingStructuralCharge secretKey) (liftM computation : OracleComp OracleWorld α) cache = 0 := by
  apply expectedQueryCharge_lift_eq_zero_of_supported_cuts
  intro ordinal middleCache input next hcut
  exact structuralCharge_eq_zero_at_supported_honest_query secretKey computation hsettling hhonest ordinal cache middleCache input next hcut

theorem expectedQueryCharge_chainWalk_eq_zero
    (secretKey : SecretKey) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (steps : Nat) (cache : QueryCache HashSpec) :
    expectedQueryCharge (signingStructuralCharge secretKey)
      (liftM (chainWalk secretKey.parameter lay tree leafIdx chainIdx 0 steps (secretKey.otsSecret lay tree leafIdx chainIdx) :
        OracleComp HashSpec Digest) : OracleComp OracleWorld Digest) cache = 0 :=
  expectedQueryCharge_eq_zero_of_honest_structural secretKey _
    (fun f => settlingRun_chainWalk secretKey.parameter secretKey.otsSecret secretKey.ftsSecret f lay tree leafIdx chainIdx steps)
    (fun f => honestStructuralQueries_chainWalk secretKey.parameter secretKey.otsSecret secretKey.ftsSecret f lay tree leafIdx chainIdx steps) cache

theorem expectedQueryCharge_treePath_eq_zero
    (secretKey : SecretKey) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (cache : QueryCache HashSpec) :
    expectedQueryCharge (signingStructuralCharge secretKey)
      (liftM (treePath secretKey.parameter lay tree (secretKey.otsSecret lay tree) leafIdx : OracleComp HashSpec (Fin maxLayerHeight → Digest)) :
        OracleComp OracleWorld (Fin maxLayerHeight → Digest)) cache = 0 :=
  expectedQueryCharge_eq_zero_of_honest_structural secretKey _
    (fun f => settlingRun_treePath secretKey.parameter secretKey.otsSecret secretKey.ftsSecret f lay tree leafIdx)
    (fun f => honestStructuralQueries_treePath secretKey.parameter secretKey.otsSecret secretKey.ftsSecret f lay tree leafIdx) cache

theorem expectedQueryCharge_ftsOpen_eq_zero
    (secretKey : SecretKey) (index : Index) (leaves : DigestTree → FtsLeaf) (cache : QueryCache HashSpec) :
    expectedQueryCharge (signingStructuralCharge secretKey)
      (liftM (ftsOpen secretKey.parameter index leaves (secretKey.ftsSecret index) : OracleComp HashSpec (FtsTree → Fin ftsTreeHeight → Digest)) :
        OracleComp OracleWorld (FtsTree → Fin ftsTreeHeight → Digest)) cache = 0 :=
  expectedQueryCharge_eq_zero_of_honest_structural secretKey _
    (fun f => settlingRun_ftsOpen secretKey.parameter secretKey.otsSecret secretKey.ftsSecret f index leaves)
    (fun f => honestStructuralQueries_ftsOpen secretKey.parameter secretKey.otsSecret secretKey.ftsSecret f index leaves) cache

theorem expectedQueryCharge_layerMessage_eq_zero
    (secretKey : SecretKey) (index : Index) (lay : Layer) (cache : QueryCache HashSpec) :
    expectedQueryCharge (signingStructuralCharge secretKey)
      (liftM (layerMessage secretKey index lay : OracleComp HashSpec Digest) : OracleComp OracleWorld Digest) cache = 0 :=
  expectedQueryCharge_eq_zero_of_honest_structural secretKey _
    (fun f => settlingRun_layerMessage f secretKey index lay)
    (fun f => honestStructuralQueries_layerMessage f secretKey index lay) cache

end SphincsSecurity.Concrete

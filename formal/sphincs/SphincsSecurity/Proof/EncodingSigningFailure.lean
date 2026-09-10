import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.EncodingExhaustionProbability
import SphincsSecurity.Proof.NoMessage

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

theorem cachedOtsEncodingFailure_of_signLayer_none
    (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (index : Index) (lay : Layer)
    (hagrees : cache.AgreesWithFn f)
    (hrun : CachedRun cache f (signLayer secretKey index lay))
    (hfailed : evalWithAnswerFn f (signLayer secretKey index lay) = none) :
    CachedOtsEncodingFailure cache := by
  rw [signLayer] at hrun
  rw [signLayer, evalWithAnswerFn_bind, evalWithAnswerFn_bind] at hfailed
  have hots := hrun.bind_right.bind_left
  cases hvalue : evalWithAnswerFn f (otsSign secretKey.parameter lay (treeIndexAt index lay)
      (leafIndexAt index lay) (secretKey.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay))
      (evalWithAnswerFn f (layerMessage secretKey index lay))) with
  | none =>
      exact ⟨f, secretKey.parameter, ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩,
        secretKey.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay),
        evalWithAnswerFn f (layerMessage secretKey index lay), hagrees, hots, hvalue⟩
  | some values => simp [hvalue] at hfailed

theorem exists_none_of_traverseOption_none {α : Type} {n : Nat}
    (family : Fin n → Option α) (hfailed : traverseOption family = none) :
    ∃ index, family index = none := by
  induction n with
  | zero => simp [traverseOption] at hfailed
  | succ n ih =>
      cases hhead : family 0 with
      | none => exact ⟨0, hhead⟩
      | some head =>
          cases htail : traverseOption (fun index : Fin n => family index.succ) with
          | none =>
              obtain ⟨index, hindex⟩ := ih (fun index : Fin n => family index.succ) htail
              exact ⟨index.succ, hindex⟩
          | some tail => simp [traverseOption, hhead, htail] at hfailed

theorem cachedOtsEncodingFailure_of_signAfterDigest_none
    (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (hagrees : cache.AgreesWithFn f)
    (hrun : CachedRun cache f (signAfterDigest secretKey randomness index leaves))
    (hfailed : evalWithAnswerFn f (signAfterDigest secretKey randomness index leaves) = none) :
    CachedOtsEncodingFailure cache := by
  rw [signAfterDigest] at hrun
  have hlayers := hrun.bind_right.bind_left
  rw [signAfterDigest, evalWithAnswerFn_bind, evalWithAnswerFn_bind,
    evalWithAnswerFn_sequenceFin] at hfailed
  cases hparts : traverseOption (fun lay => evalWithAnswerFn f (signLayer secretKey index lay)) with
  | none =>
      obtain ⟨lay, hlay⟩ := exists_none_of_traverseOption_none _ hparts
      exact cachedOtsEncodingFailure_of_signLayer_none f cache secretKey index lay hagrees
        (hlayers.sequenceFin_component _ lay) hlay
  | some parts => simp [hparts] at hfailed

end SphincsSecurity.Concrete

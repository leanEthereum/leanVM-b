import SphincsSecurity.Proof.SignSupport

/-!
# Cached encoding queries

Successful verifier and signer executions retain the encoding query that selected their counter.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

theorem CachedRun.encode_cached {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {parameter : PublicParameter} {lay : Layer}
    {tree : TreeIndex} {leafIdx : LeafIndex} {message : Digest} {counter : Counter}
    (hrun : CachedRun cache f (encode parameter lay tree leafIdx message counter)) :
    cache (tweakableHashInput parameter (.encoding lay tree leafIdx)
      (digestBytes message ++ counterBytes counter)) ≠ none := by
  apply hrun
  rw [encode]
  apply queriedInputs_mono_bind_left
  simp only [queriedInputs_tweakableHash, List.mem_singleton]

theorem CachedRun.otsLeaf_encode_cached {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {parameter : PublicParameter} {lay : Layer}
    {tree : TreeIndex} {leafIdx : LeafIndex} {message : Digest} {counter : Counter}
    {values : ChainIndex → Digest}
    (hrun : CachedRun cache f (otsLeaf parameter lay tree leafIdx message counter values)) :
    cache (tweakableHashInput parameter (.encoding lay tree leafIdx)
      (digestBytes message ++ counterBytes counter)) ≠ none :=
  CachedRun.encode_cached hrun.bind_left

theorem cached_encode_of_otsSignFrom_some (f : QueryImpl HashSpec Id)
    (cache : QueryCache HashSpec) (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leafIdx : LeafIndex) (secret : ChainIndex → Digest)
    (message : Digest) (attempts counter : Nat) (resultCounter : Counter)
    (values : ChainIndex → Digest)
    (hsign : evalWithAnswerFn f
      (otsSignFrom parameter lay tree leafIdx secret message attempts counter)
        = some (resultCounter, values))
    (hrun : CachedRun cache f
      (otsSignFrom parameter lay tree leafIdx secret message attempts counter)) :
    cache (tweakableHashInput parameter (.encoding lay tree leafIdx)
      (digestBytes message ++ counterBytes resultCounter)) ≠ none := by
  induction attempts generalizing counter with
  | zero => simp [otsSignFrom] at hsign
  | succ attempts ih =>
      rw [otsSignFrom, evalWithAnswerFn_bind] at hsign
      rw [otsSignFrom] at hrun
      cases hencode : evalWithAnswerFn f
          (encode parameter lay tree leafIdx message (BitVec.ofNat counterBits counter)) with
      | none =>
          simp only [hencode] at hsign
          exact ih (counter + 1) hsign (by
            have hrest := hrun.bind_right
            simpa only [hencode] using hrest)
      | some codeword =>
          simp only [hencode, evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin,
            evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at hsign
          have hcounter : BitVec.ofNat counterBits counter = resultCounter := hsign.1
          rw [← hcounter]
          exact CachedRun.encode_cached hrun.bind_left

theorem SuccessfulSignRun.signed_encode_cached {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {message : Message}
    {signature : Signature} (hrun : SuccessfulSignRun f cache secretKey message signature)
    (lay : Layer) :
    ∃ index leaves, SuccessfulDigestRun f cache secretKey message signature.randomness index leaves
      ∧ cache (tweakableHashInput secretKey.parameter
        (.encoding lay (treeIndexAt index lay) (leafIndexAt index lay))
        (digestBytes (evalWithAnswerFn f (layerMessage secretKey index lay)) ++
          counterBytes (signature.counter lay))) ≠ none := by
  obtain ⟨index, leaves, parts, hdigest, _, _, hcounter, _, _, _, heval, hcached⟩ := hrun
  have hlayerEval := heval lay
  have hlayerRun := hcached lay
  rw [signLayer, evalWithAnswerFn_bind, evalWithAnswerFn_bind] at hlayerEval
  rw [signLayer] at hlayerRun
  have hrestRun := hlayerRun.bind_right
  let layerValue := evalWithAnswerFn f (layerMessage secretKey index lay)
  cases hots : evalWithAnswerFn f
      (otsSign secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
        (secretKey.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay)) layerValue) with
  | none =>
      simp only [layerValue, hots, evalWithAnswerFn_pure] at hlayerEval
      cases hlayerEval
  | some signed =>
      obtain ⟨counter, values⟩ := signed
      have hotsRun : CachedRun cache f
          (otsSign secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
            (secretKey.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay))
            layerValue) := by
        have := hrestRun.bind_left
        simpa only [layerValue] using this
      simp only [layerValue, hots, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
        Option.some.injEq] at hlayerEval
      have hpartCounter : counter = (parts lay).1 := congrArg Prod.fst hlayerEval
      have hsignatureCounter : signature.counter lay = (parts lay).1 := congrFun hcounter lay
      have hc := cached_encode_of_otsSignFrom_some f cache secretKey.parameter lay
        (treeIndexAt index lay) (leafIndexAt index lay)
        (secretKey.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay)) layerValue
        encodingAttemptLimit 0 counter values (by simpa only [otsSign] using hots)
        (by simpa only [otsSign] using hotsRun)
      rw [hpartCounter, ← hsignatureCounter] at hc
      exact ⟨index, leaves, hdigest, by simpa only [layerValue] using hc⟩

theorem SuccessfulSignRun.signed_encode_cached_of_digest {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {message : Message}
    {signature : Signature} (hrun : SuccessfulSignRun f cache secretKey message signature)
    {index : Index} {leaves : DigestTree → FtsLeaf}
    (hdigest : SuccessfulDigestRun f cache secretKey message signature.randomness index leaves)
    (lay : Layer) :
    cache (tweakableHashInput secretKey.parameter
      (.encoding lay (treeIndexAt index lay) (leafIndexAt index lay))
      (digestBytes (evalWithAnswerFn f (layerMessage secretKey index lay)) ++
        counterBytes (signature.counter lay))) ≠ none := by
  obtain ⟨runIndex, _, hrunDigest, hcached⟩ := hrun.signed_encode_cached lay
  obtain ⟨_, runValue, hrunValue, _, hrunIndex, _, _⟩ := hrunDigest.extract
  obtain ⟨_, digestValue, hdigestValue, _, hdigestIndex, _, _⟩ := hdigest.extract
  have hvalue : runValue = digestValue := by rw [← hrunValue, ← hdigestValue]
  have hindex : runIndex = index := by rw [hrunIndex, hdigestIndex, hvalue]
  rw [hindex] at hcached
  exact hcached

end SphincsSecurity.Concrete

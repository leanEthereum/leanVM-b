import SphincsSecurity.Proof.Logged
import SphincsSecurity.Proof.Extract

/-!
# From the run to an answer function

The extraction lemmas are facts about `evalWithAnswerFn f`, and the game runs under the lazy oracle.
The bridge is VCVio's support characterization: a value comes out of the lazy oracle exactly when some
total answer function agreeing with the cache evaluates the computation to it.

That characterization is stated for a computation over one spec, and the game's spec is
`unifSpec + HashSpec`. It applies anyway, because the part the extraction analyses is verification,
and verification samples nothing: it is an `OracleComp HashSpec Bool`, lifted into the sum.
-/

namespace SphincsSecurity

open OracleComp OracleSpec

/-- Simulating a lifted hash-only computation is simulating it under the random oracle. -/
theorem simulateQ_romImpl_liftM {α : Type} (oa : OracleComp HashSpec α) :
    simulateQ romImpl (liftM oa : OracleComp OracleWorld α)
      = simulateQ (randomOracle : QueryImpl HashSpec _) oa :=
  QueryImpl.simulateQ_add_liftM_right _ _ oa

/-- **The bridge.** If verification accepts in the run, some answer function agreeing with the cache
accepts too, and every extraction lemma applies to that function. -/
theorem exists_answerFn_of_verify (publicKey : PublicKey) (message : Message)
    (signature : Signature) (cache cache' : QueryCache HashSpec)
    (hmem : (true, cache')
      ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _)
          (Concrete.verify publicKey message signature)).run cache)) :
    ∃ f : QueryImpl HashSpec Id, cache.AgreesWithFn f
      ∧ evalWithAnswerFn f (Concrete.verify publicKey message signature) = true :=
  (exists_agreesWithFn_evalWithAnswerFn_eq_iff_mem_support
    (Concrete.verify publicKey message signature) cache true).mpr ⟨cache', hmem⟩

/-! ### One layer of the walk, unpeeled

What the extraction consumes is the two facts of a single layer: that `Ots.leaf` returned something,
and that folding it reached what the layer above was handed. This peels them off `verifyLayers`.
-/

namespace Concrete

open OracleComp

theorem verifyLayers_succ_extract (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (signature : Signature) (remaining : Nat) (hlayer : remaining < numLayers)
    (message : Digest) (target : Digest)
    (hverify : evalWithAnswerFn f
        (verifyLayers parameter index signature (remaining + 1) message) = some target) :
    ∃ leafValue, evalWithAnswerFn f (otsLeaf parameter ⟨remaining, hlayer⟩
          (treeIndexAt index ⟨remaining, hlayer⟩) (leafIndexAt index ⟨remaining, hlayer⟩) message
          (signature.counter ⟨remaining, hlayer⟩) (signature.chainValue ⟨remaining, hlayer⟩))
        = some leafValue
      ∧ evalWithAnswerFn f (verifyLayers parameter index signature remaining
          (foldValue f parameter ⟨remaining, hlayer⟩ (treeIndexAt index ⟨remaining, hlayer⟩)
            (leafIndexAt index ⟨remaining, hlayer⟩) (signaturePath signature ⟨remaining, hlayer⟩)
            leafValue (layerHeight ⟨remaining, hlayer⟩))) = some target := by
  rcases hleaf : evalWithAnswerFn f (otsLeaf parameter ⟨remaining, hlayer⟩
      (treeIndexAt index ⟨remaining, hlayer⟩) (leafIndexAt index ⟨remaining, hlayer⟩) message
      (signature.counter ⟨remaining, hlayer⟩) (signature.chainValue ⟨remaining, hlayer⟩))
    with _ | leafValue
  · rw [verifyLayers_succ_eq, dif_pos hlayer, evalWithAnswerFn_bind, hleaf] at hverify
    simp at hverify
  · refine ⟨leafValue, rfl, ?_⟩
    rw [verifyLayers_succ_eq, dif_pos hlayer, evalWithAnswerFn_bind, hleaf] at hverify
    simpa [foldValue, evalWithAnswerFn_bind] using hverify

end Concrete

end SphincsSecurity

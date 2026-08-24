import SphincsSecurity.Proof.Layer

/-!
# The hypertree

Three layers, bottom first. Each layer's fold produces the root of its tree, which is exactly the
message the layer above it signs, so the layers chain; layer `0`'s fold is the public root.
-/

namespace SphincsSecurity.Concrete

open OracleComp

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

theorem layerMessage_bottomLayer (secretKey : SecretKey) (index : Index) :
    layerMessage (m := m) secretKey index bottomLayer
      = ftsKey secretKey.parameter index (secretKey.ftsSecret index) := by
  rw [layerMessage, dif_neg (by decide)]

theorem layerMessage_of_lt (secretKey : SecretKey) (index : Index) (lay : Layer)
    (hbelow : lay.val + 1 < numLayers) :
    layerMessage (m := m) secretKey index lay
      = treeRoot secretKey.parameter ⟨lay.val + 1, hbelow⟩
          (treeIndexAt index ⟨lay.val + 1, hbelow⟩)
          (secretKey.otsSecret ⟨lay.val + 1, hbelow⟩ (treeIndexAt index ⟨lay.val + 1, hbelow⟩)) := by
  rw [layerMessage, dif_pos hbelow]

/-- Honest leaf indices are in range for their layer, which is what lets a fold reach the root. -/
theorem leafIndexAt_lt (index : Index) (lay : Layer) :
    (leafIndexAt index lay).val < 2 ^ layerHeight lay := by
  rw [leafIndexAt_val]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- **The hypertree.** An honest signature's layers chain from the few-time public key up to the
public root: each layer's fold is the message the layer above signs. -/
theorem eval_verifyLayers (f : QueryImpl HashSpec Id) (secretKey : SecretKey) (index : Index)
    (signature : Signature) (codeword : Layer → Encoding)
    (hchain : ∀ lay : Layer, signature.chainValue lay
      = fun chainIdx => evalWithAnswerFn f (chainWalk secretKey.parameter lay (treeIndexAt index lay)
          (leafIndexAt index lay) chainIdx 0 (codeword lay chainIdx).val
          (secretKey.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx)))
    (hpath : ∀ (lay : Layer) (level : Nat), level < layerHeight lay →
      signaturePath signature lay level = evalWithAnswerFn f (treeNode secretKey.parameter lay
        (treeIndexAt index lay) (secretKey.otsSecret lay (treeIndexAt index lay)) level
        (Nat.xor ((leafIndexAt index lay).val / 2 ^ level) 1)))
    (hencode : ∀ lay : Layer, evalWithAnswerFn f (encode secretKey.parameter lay
        (treeIndexAt index lay) (leafIndexAt index lay)
        (evalWithAnswerFn f (layerMessage secretKey index lay)) (signature.counter lay))
      = some (codeword lay)) :
    evalWithAnswerFn f (verifyLayers secretKey.parameter index signature numLayers
        (evalWithAnswerFn f (ftsKey secretKey.parameter index (secretKey.ftsSecret index))))
      = some (evalWithAnswerFn f (treeRoot secretKey.parameter topLayer rootTree
          (secretKey.otsSecret topLayer rootTree))) := by
  have hstep : ∀ (remaining : Nat) (hlayer : remaining < numLayers) (message : Digest),
      evalWithAnswerFn f (encode secretKey.parameter ⟨remaining, hlayer⟩
          (treeIndexAt index ⟨remaining, hlayer⟩) (leafIndexAt index ⟨remaining, hlayer⟩) message
          (signature.counter ⟨remaining, hlayer⟩)) = some (codeword ⟨remaining, hlayer⟩) →
      evalWithAnswerFn f (verifyLayers secretKey.parameter index signature (remaining + 1) message)
        = evalWithAnswerFn f (verifyLayers secretKey.parameter index signature remaining
            (evalWithAnswerFn f (treeRoot secretKey.parameter ⟨remaining, hlayer⟩
              (treeIndexAt index ⟨remaining, hlayer⟩)
              (secretKey.otsSecret ⟨remaining, hlayer⟩ (treeIndexAt index ⟨remaining, hlayer⟩))))) := by
    intro remaining hlayer message hmessage
    rw [verifyLayers_succ_eq, dif_pos hlayer, hchain ⟨remaining, hlayer⟩]
    exact eval_layer f secretKey.parameter ⟨remaining, hlayer⟩ (treeIndexAt index ⟨remaining, hlayer⟩)
      (secretKey.otsSecret ⟨remaining, hlayer⟩ (treeIndexAt index ⟨remaining, hlayer⟩))
      (leafIndexAt index ⟨remaining, hlayer⟩) _ _ _ hmessage
      (leafIndexAt_lt index ⟨remaining, hlayer⟩) _
      (fun level hlevel => hpath ⟨remaining, hlayer⟩ level hlevel) _ _
  have hbottom := hstep 2 (by decide)
    (evalWithAnswerFn f (ftsKey secretKey.parameter index (secretKey.ftsSecret index)))
    (hencode ⟨2, by decide⟩)
  have hmiddle := hstep 1 (by decide)
    (evalWithAnswerFn f (treeRoot secretKey.parameter ⟨2, by decide⟩
      (treeIndexAt index ⟨2, by decide⟩)
      (secretKey.otsSecret ⟨2, by decide⟩ (treeIndexAt index ⟨2, by decide⟩))))
    (hencode ⟨1, by decide⟩)
  have htop := hstep 0 (by decide)
    (evalWithAnswerFn f (treeRoot secretKey.parameter ⟨1, by decide⟩
      (treeIndexAt index ⟨1, by decide⟩)
      (secretKey.otsSecret ⟨1, by decide⟩ (treeIndexAt index ⟨1, by decide⟩))))
    (hencode ⟨0, by decide⟩)
  have hroot : treeIndexAt index topLayer = rootTree := by
    ext
    rw [treeIndexAt_topLayer]
    rfl
  rw [show numLayers = 2 + 1 from rfl, hbottom, hmiddle, htop, verifyLayers_zero_eq,
    evalWithAnswerFn_pure, show (⟨0, by decide⟩ : Layer) = topLayer from rfl, hroot]

end SphincsSecurity.Concrete

import SphincsSecurity.Proof.FtsOpeningQueryCost

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ConsumesHashQueries

theorem consumesHashQueries_signAttempt (key : SecretKey) (message : Message) (randomness : Randomness) :
    ConsumesHashQueries (liftM (signAttempt key message randomness : OracleComp HashSpec _)) 1 := by
  unfold signAttempt messageDigest
  rw [liftM_bind, liftM_bind, bind_assoc]
  apply consumesHashQueries_bind _ _ 1 0 (consumesHashQueries_hash _)
  intro output
  exact consumesHashQueries_zero _

theorem consumesHashQueries_signDigestLoop_bind {α : Type} (key : SecretKey) (message : Message)
    (cost attempts : Nat)
    (next : Option (Randomness × Index × (DigestTree → FtsLeaf)) → OracleComp OracleWorld α)
    (hnext : ∀ selected, ConsumesHashQueries (next (some selected)) cost) :
    ConsumesHashQueries (signDigestLoop attempts key message >>= next) (min attempts cost) := by
  induction attempts with
  | zero => exact consumesHashQueries_zero _
  | succ attempts ih =>
      rw [signDigestLoop, bind_assoc]
      rw [← Nat.zero_add (min (attempts + 1) cost)]
      apply consumesHashQueries_bind _ _ 0 (min (attempts + 1) cost) (consumesHashQueries_zero _)
      intro randomness
      rw [bind_assoc]
      apply ConsumesHashQueries.mono (a := 1 + min attempts cost) ?_ (by omega)
      apply consumesHashQueries_bind _ _ 1 (min attempts cost) (consumesHashQueries_signAttempt _ _ _)
      intro attempt
      cases attempt with
      | none => exact ih
      | some selected =>
          simp only [pure_bind]
          exact ConsumesHashQueries.mono (hnext _) (min_le_right _ _)

theorem consumesHashQueries_sign (key : SecretKey) (message : Message) :
    ConsumesHashQueries (sign key message) 1024 := by
  rw [sign_eq]
  apply ConsumesHashQueries.mono (a := min digestAttemptLimit 1024) ?_ (by decide)
  apply consumesHashQueries_signDigestLoop_bind
  rintro ⟨randomness, index, leaves⟩
  apply consumesHashQueries_bind _ _ 1024 0 (consumesHashQueries_ftsOpen_1024 _ _ _ _)
  intro path
  exact consumesHashQueries_zero _

end SphincsSecurity.Concrete

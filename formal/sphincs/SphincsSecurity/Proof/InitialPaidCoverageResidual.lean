import SphincsSecurity.Proof.InitialSigningCoveragePayment
import SphincsSecurity.Proof.SigningCoverageExecutionPayment

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem targetShapeEnvelope_signings_mono (uniform reuse arrival : ENNReal) (queries : Nat) (f : TargetShapeVector)
    {small large : Nat} (h : small ≤ large) :
    targetShapeEnvelope uniform reuse arrival queries small f ≤ targetShapeEnvelope uniform reuse arrival queries large f :=
  Function.monotone_iterate_of_id_le (show ∀ f : TargetShapeVector, f ≤ targetShapeSigning uniform reuse f from
    fun _ _ _ => le_self_add.trans le_self_add) h _

namespace FtsProbeSimulation

theorem newTargetCoverageExcess_initial_eq_zero_of_le (key : SecretKey) (cache : QueryCache HashSpec)
    (hnone : ∀ input, MessageHashInput key.parameter input → cache input = none)
    (reference : HashInput) (q : Nat) (hq : q ≤ 2 ^ 127)
    (queries signings : Nat) (hqueries : queries ≤ q) (hsignings : signings ≤ signatureLimit) :
    newTargetCoverageExcess key cache [] reference (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
      (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) queries signings = 0 := by
  unfold newTargetCoverageExcess
  apply ENNReal.tsum_eq_zero.mpr
  intro source
  have hvalid : TargetShapeValid ∅ (Finset.univ : Finset FtsTree) := by constructor <;> simp
  have henv := (targetShapeEnvelope_queries_mono (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
    (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
      signings (targetShapeMoments key cache [] reference source) hqueries ∅ Finset.univ hvalid).trans
        (targetShapeEnvelope_signings_mono _ _ _ q _ hsignings ∅ Finset.univ)
  have hscaled := (mul_le_mul' henv (le_refl (((2 ^ 140 : Nat) : ENNReal)⁻¹))).trans
    (initialTargetShape_scaled_le_signingAllowance key cache hnone reference source q hq)
  rw [tsub_eq_zero_of_le hscaled, mul_zero]

end FtsProbeSimulation

theorem signingRemainingCoverageResidual_initial_eq_zero (key : SecretKey) (cache : QueryCache HashSpec)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none)
    (q : Nat) (hq : q ≤ 2 ^ 127) (budget : Nat) (hbudget : budget ≤ q) (message : Message) :
    signingRemainingCoverageResidual key q budget message (cache, []) = 0 := by
  have hsigned : SigningDigestsCached key.parameter cache key.root [] := by
    intro entry hentry
    simp only [List.not_mem_nil] at hentry
  apply le_antisymm ?_ bot_le
  exact (FtsProbeSimulation.signingNewTargetCoverageResidual_le_excess key message cache [] hsigned []
    (hnone _ ⟨[], rfl⟩) _ _ _ _ _).trans_eq
      (FtsProbeSimulation.newTargetCoverageExcess_initial_eq_zero_of_le key cache hnone [] q hq
        (budget - signingExecutionHashCost (.inr message)) (signatureLimit - ([].length + 1))
        ((Nat.sub_le _ _).trans hbudget) (Nat.sub_le _ _))

namespace FtsProbeSimulation.JointOriginal

theorem signingRemainingCoverageResidual_initializeRoot_eq_zero
    (parameter : PublicParameter) (otsTable : OtsProbeSimulation.OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q : Nat) (hq : q ≤ 2 ^ 127) (fuel : Nat) (message : Message)
    (initial : Option Frame × (Digest × QueryCache HashSpec))
    (hi : initial ∈ support (initializeRoot parameter otsTable ftsTable q fuel)) :
    signingRemainingCoverageResidual (secretKey parameter initial.2.1 otsTable ftsTable) q q message (initial.2.2, []) = 0 := by
  apply signingRemainingCoverageResidual_initial_eq_zero _ _ ?_ q hq q le_rfl message
  have hroot := initializeRoot_original_support parameter otsTable ftsTable q fuel initial hi
  rw [originalRoot, simulateQ_romImpl_liftM] at hroot
  intro input hmessage
  obtain ⟨payload, rfl⟩ := hmessage
  exact treeRoot_cache_message_none parameter topLayer rootTree
    ((secretKey parameter initial.2.1 otsTable ftsTable).otsSecret topLayer rootTree) initial.2.1 initial.2.2 hroot payload

end FtsProbeSimulation.JointOriginal
end SphincsSecurity.Concrete

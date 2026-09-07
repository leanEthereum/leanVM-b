import SphincsSecurity.Proof.InitialMixedEnvelope
import SphincsSecurity.Proof.MixedMomentBinomial

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
set_option backward.isDefEq.respectTransparency false

theorem initialMixedDerivativeVector_order_zero (power order : Nat) (horder : 15 ≤ order) :
    initialMixedDerivativeVector power order = 0 := by
  simp only [initialMixedDerivativeVector, show ¬ order < 15 by omega, and_false, if_false]

noncomputable def finiteInitialMixedEnvelope (q : Nat) : ENNReal :=
  ∑ degree ∈ Finset.range 29, (signatureLimit.choose degree : ENNReal) *
    (mixedSigningIncrement (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q))^[degree]
      (finiteMixedQueryEnvelope (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ / (Fintype.card Index : ENNReal)) q
        initialMixedDerivativeVector) 0 0

theorem initialMixedEnvelope_eq_finite (q : Nat) :
    mixedRemainingEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
      (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ / (Fintype.card Index : ENNReal)) q signatureLimit initialMixedDerivativeVector 0 0 =
      finiteInitialMixedEnvelope q :=
  mixedRemainingEnvelope_zero_zero_eq_finite _ _ _ q signatureLimit initialMixedDerivativeVector initialMixedDerivativeVector_order_zero

theorem expected_adaptive_validOccupancy_le_finiteInitialEnvelope {α : Type} (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec)
    (hnone : ∀ input, MessageHashInput key.parameter input → cache input = none)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q) :
    (∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])] *
      (if SigningTranscript.Valid result.2.2 then observedLogOccupancy key result.2 else 0)) ≤ finiteInitialMixedEnvelope q := by
  rw [← initialMixedEnvelope_eq_finite]
  exact expected_adaptive_validOccupancy_le_initialMixedEnvelope key q hq computation cache hnone hbudget

end SphincsSecurity.Concrete

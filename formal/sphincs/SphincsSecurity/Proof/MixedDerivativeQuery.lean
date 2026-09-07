import SphincsSecurity.Proof.MixedIndexQuery
import SphincsSecurity.Proof.WorldIndexMoment

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem occupancyDerivativePolynomial_sum {α : Type} [DecidableEq α] (indices : Finset α)
    (order remaining : Nat) (moments : α → Nat → ENNReal) :
    occupancyDerivativePolynomial order (fun degree => ∑ index ∈ indices, moments index degree) remaining =
      ∑ index ∈ indices, occupancyDerivativePolynomial order (moments index) remaining := by
  induction indices using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, occupancyDerivativePolynomial_zero]
  | @insert index indices hnot ih => simp only [Finset.sum_insert hnot, occupancyDerivativePolynomial_add, ih]

theorem expected_message_mixedDerivative (power order remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput) (hfresh : before input = none)
    (hsigned : SigningDigestsCached key.parameter before key.root log) (hmessage : FtsProbeSimulation.MessageHashInput key.parameter input) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      occupancyDerivativePolynomial order
        (mixedIndexBinomialMoments key (before.cacheQuery input output) power (before.cacheQuery input output, log)) remaining) =
      occupancyDerivativePolynomial order (mixedIndexBinomialMoments key before power (before, log)) remaining +
        (∑ lower ∈ Finset.range power, (power.choose lower : ENNReal) *
          occupancyDerivativePolynomial order (mixedIndexBinomialMoments key before lower (before, log)) remaining) *
          (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ / (Fintype.card Index : ENNReal)) := by
  rw [expected_occupancyDerivativePolynomial]
  simp only [expected_message_mixedIndexBinomialMoments key power _ before log input hfresh hsigned hmessage,
    occupancyDerivativePolynomial_add, occupancyDerivativePolynomial_mul_right, occupancyDerivativePolynomial_sum]
  congr 2
  apply Finset.sum_congr rfl
  intro lower _
  simp_rw [mul_comm ((power.choose lower : Nat) : ENNReal)]
  rw [occupancyDerivativePolynomial_mul_right]

end SphincsSecurity.Concrete

import SphincsSecurity.Proof.RawIndexSigningGrowth
import SphincsSecurity.Proof.RawIndexMomentAlgebra

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem expected_signWithView_rawIndexGrowth_le_mass_mul_uniform (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (power degree : Nat)
    (hsigned : SigningDigestsCached key.parameter before key.root log) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      rawIndexSigningGrowth key before power (result.2, log ++ [⟨message, result.1.1⟩]) degree) ≤
      freshDigestSelectionProbability key message before *
        ∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] * newRawIndexWeight key before log power source degree := by
  exact expected_signWithView_newAdmissible_cost_le_mass_mul key message before _ _
    (fun result hr => signWithView_rawIndexGrowth_le_newEvents key message before log
      power degree hsigned result hr)

theorem expected_signWithView_rawIndexGrowth_le_uniform (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (power degree : Nat)
    (hsigned : SigningDigestsCached key.parameter before key.root log) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      rawIndexSigningGrowth key before power (result.2, log ++ [⟨message, result.1.1⟩]) degree) ≤
      ∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] * newRawIndexWeight key before log power source degree :=
  (expected_signWithView_rawIndexGrowth_le_mass_mul_uniform key message before log power degree hsigned).trans
    (mul_le_of_le_one_left' (freshDigestSelectionProbability_le_one key message before))

theorem expected_newRawIndexWeight (key : SecretKey) (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (power degree : Nat) :
    (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] * newRawIndexWeight key before log power source degree) =
      (Fintype.card Index : ENNReal)⁻¹ *
        (targetIndexCacheLower (targetIndexMoments key before log) power degree +
          targetIndexCacheLower (targetIndexTreeLower (targetIndexMoments key before log)) power degree) := by
  unfold newRawIndexWeight
  rw [uniform_view_index_weight_expectation (fun index => cachePowerArrival power (cachedIndexMultiplicity key.parameter before index) *
    (((signingSlotsAtIndex (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) index).card + 1 : Nat) : ENNReal) ^ degree),
    weighted_cachePowerArrival_sum]
  simp only [targetIndexMoments_raised, mul_add, Finset.sum_add_distrib, targetIndexCacheLower, div_eq_mul_inv]
  ring

end SphincsSecurity.Concrete

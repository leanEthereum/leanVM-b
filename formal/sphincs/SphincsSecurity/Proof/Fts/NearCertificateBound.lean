import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.PoissonProposalMoments
import SphincsSecurity.Proof.Fts.TerminalCertificateCharge
namespace SphincsSecurity.Concrete

open _root_.OracleComp ENNReal

set_option maxHeartbeats 2000000 in
theorem poissonPowerMoment_thirteen :
    poissonPowerMoment (19 / 50) 13 =
      (1986585224814431503899382459 : ENNReal) / 12207031250000000000000 := by
  unfold poissonPowerMoment
  apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.sum_ne_top.mpr (fun _ _ => by finiteness)) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_sum, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
  norm_num [Finset.sum_range_succ, Nat.stirlingSecond]

theorem terminalProposalAverage_nearPrice (required : Finset FtsTree) (hdegree : required.card = 13) :
    terminalProposalAverage (terminalCertificatePrice required) ≤
      ((557 : ENNReal) / 14) / (2 ^ 128 : Nat) := by
  rw [terminalProposalAverage_certificatePrice, hdegree, poissonPowerMoment_thirteen]
  unfold targetCertificateScale
  rw [hdegree]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ftsTreeHeight, FtsLeaf, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_div, ENNReal.toReal_pow]

end SphincsSecurity.Concrete

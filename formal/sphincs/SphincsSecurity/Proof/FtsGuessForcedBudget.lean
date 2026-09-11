import SphincsSecurity.Proof.SecretGuessForceBound
import SphincsSecurity.Proof.FtsGuessBudget

namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec ENNReal
open FtsGuessSigning (Coordinate)
open SecretGuessObservation (State forcedRun initialState)
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs canonicalGraphGameInputs instFintypePosition
  frontierRoot maskOtsPrefixes frontierSigningRun boundaryEval

theorem forced_original_completedRun_budget (dummy : OtsReferenceWords) (adversary : Adversary) (q slot : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary (canonicalGraphGameInputs adversary))
    (hauxiliary : auxiliary ∈ (referenceAuxiliarySample (canonicalGraphGameInputs adversary)).support)
    (result : Completed × State Coordinate Digest PUnit)
    (hr : forcedRun (SecretGuessObservation.environment (originalAnswers dummy adversary parameter otsSecret labels auxiliary)) slot
      (completedRun parameter (canonicalGraphRoot labels) labels adversary) (initialState PUnit.unit) result ≠ 0) :
    1212415 + completedWork result.1 ≤ q ∧ result.2.probes ≤ completedWork result.1 :=
  lazy_original_completedRun_budget dummy adversary q hbound parameter otsSecret labels auxiliary hauxiliary result
    (SecretGuessObservation.forcedRun_nonzero _ slot _ _ result hr)

end SphincsSecurity.Concrete.FtsGuessHash

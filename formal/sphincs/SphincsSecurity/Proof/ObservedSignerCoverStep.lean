import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.FewTimeAdaptiveCoverage
import SphincsSecurity.Proof.FewTimeConditionalSignerCompletion
import SphincsSecurity.Proof.FewTimePrehit
import SphincsSecurity.Proof.FewTimeSignerView
import SphincsSecurity.Proof.FewTimeWeightedOriginRace
import SphincsSecurity.Proof.ObservedAdaptiveCoverBound
import SphincsSecurity.Proof.ObservedSignerCompletion
import SphincsSecurity.Proof.RomQueryCharge

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def observedSignerCoverCharge (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (log : QueryLog SigningSpec) (q : Nat) : ENNReal :=
  expectedQueryCharge (freshCoverageCharge key.parameter (fixedSigningViews key.parameter cache key.root log))
      (signWithView key message) cache * ((2 ^ 176 : Nat) : ENNReal)⁻¹ +
    (∑ target ∈ cachedAdmissibleMessageInputs key.parameter cache hfinite,
      completionProbability (fixedSigningViews key.parameter cache key.root log target) (cachedFewTimeView cache target)) +
    cachedMessageEntryCountWhere cache key.parameter key.root message
      (CompletesSomeFewTimeTarget (cachedAdmissibleMessageInputs key.parameter cache hfinite)
        (fixedSigningViews key.parameter cache key.root log) (cachedFewTimeView cache)) * digestReuseWeight q

end SphincsSecurity.Concrete

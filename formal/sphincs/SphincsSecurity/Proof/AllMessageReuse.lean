import SphincsSecurity.Proof.CacheMessageSignerWeight
import SphincsSecurity.Proof.CachedSourceIncrement
import SphincsSecurity.Proof.OccupancyCompletionIncrement

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
set_option backward.isDefEq.respectTransparency false

noncomputable def allMessageTargetReuseCharge (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (q : Nat) : ENNReal :=
  cacheMessageWeight key.parameter (cachedTargetFutureIncrement remaining key before log) before * digestReuseWeight q

noncomputable def allMessageOccupancyReuseCharge (remaining : Nat) (key : SecretKey)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (q : Nat) : ENNReal :=
  cacheMessageWeight key.parameter (fun _ source => coverageOccupancyCompletionIncrement
    (observedOptionalSigningViews (messageAnswers key.parameter before) key.root log) remaining source) before * digestReuseWeight q

theorem cachedFutureCoverageReuseCharge_le_allMessage (remaining : Nat) (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (q : Nat) :
    cachedFutureCoverageReuseCharge remaining key message before log q ≤ allMessageTargetReuseCharge remaining key before log q := by
  rw [cachedFutureCoverageReuseCharge_eq_sources]
  exact mul_le_mul' (ENNReal.tsum_le_tsum
    (cachedSignerInputWeight_le_cacheMessageEntryWeight key message before (cachedTargetFutureIncrement remaining key before log))) le_rfl

end SphincsSecurity.Concrete

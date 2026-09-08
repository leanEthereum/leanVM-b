import SphincsSecurity.Proof.MessageDeficitConcentration
import SphincsSecurity.Proof.CacheEntryExceptionInvariant

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

theorem messageAdmissibleDeficit_le_of_monitor_clean (key : SecretKey)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (hnone : ∀ payload, cache (tweakableHashInput key.parameter .message payload) = none)
    (result : (α × QueryCache HashSpec) × Bool)
    (hr : result ∈ support
      (runExceptionMonitor (cacheEntryException (MessageDeficitExceptional key)) computation cache false))
    (hclean : result.2 = false) (message : Message) :
    messageAdmissibleDeficit key message result.1.2 ≤ ((2 ^ 83 : Nat) : ENNReal) := by
  have hnot := runCacheEntryException_clean_of_no_hit (MessageDeficitExceptional key) computation cache false
    (fun _ => messageDeficitExceptional_not_of_no_inputs key cache hnone) result hr hclean
  exact le_of_not_gt (fun h => hnot ⟨message, h⟩)

theorem exactDigestReuseWeight_le_near_uniform_of_monitor_clean (key : SecretKey)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (hnone : ∀ payload, cache (tweakableHashInput key.parameter .message payload) = none)
    (result : (α × QueryCache HashSpec) × Bool)
    (hr : result ∈ support
      (runExceptionMonitor (cacheEntryException (MessageDeficitExceptional key)) computation cache false))
    (hclean : result.2 = false) (q : Nat) (hq : q ≤ 2 ^ 127)
    (hcache : QueryCache.enncard result.1.2 ≤ q) (message : Message) :
    exactDigestReuseWeight key message result.1.2 ≤ (1025 / 1024 : ENNReal) * ((2 ^ 118 : Nat) : ENNReal)⁻¹ :=
  exactDigestReuseWeight_le_near_uniform_of_deficit key message result.1.2 q hq hcache
    (messageAdmissibleDeficit_le_of_monitor_clean key computation cache hnone result hr hclean message)

end SphincsSecurity.Concrete

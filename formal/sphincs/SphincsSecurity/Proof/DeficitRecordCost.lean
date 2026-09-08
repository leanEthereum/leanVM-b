import SphincsSecurity.Proof.DeficitExceptionRecord
import SphincsSecurity.Proof.FirstExceptionSelection

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open OracleComp OracleSpec ENNReal

theorem probEvent_firstDeficitMessageRecord_le_monitor
    (key : SecretKey) (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (hparent : ∀ cache input answer, exception cache input answer →
      ParentSettlement key.parameter key.otsSecret key.ftsSecret cache input answer)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    Pr[fun result => ∃ record ∈ result.2, MessageHashInput key.parameter record.input |
      runFirstException (deficitStoppingException key exception) computation cache none] ≤
    Pr[fun result => result.2 = true |
      runExceptionMonitor (cacheEntryException (MessageDeficitExceptional key)) computation cache false] := by
  apply probEvent_firstException_selected_le_monitor
    (deficitStoppingException key exception) (fun record => MessageHashInput key.parameter record.input)
    (cacheEntryException (MessageDeficitExceptional key)) ?_ computation cache
  intro before input answer hexception hmessage
  rcases hexception with hbase | hbad
  · obtain ⟨_, child, parent, hat, _⟩ := hparent before input answer hbase
    exact False.elim (atPosition_not_message hat hmessage)
  · exact hbad

theorem probEvent_firstDeficitMessageRecord_le
    (key : SecretKey) (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (hparent : ∀ cache input answer, exception cache input answer →
      ParentSettlement key.parameter key.otsSecret key.ftsSecret cache input answer)
    (computation : OracleComp OracleWorld α) (q : Nat)
    (hbound : computation.IsQueryBoundP (· matches Sum.inr _) q) (hq : q ≤ 2 ^ 127)
    (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (hnone : ∀ payload, cache (tweakableHashInput key.parameter .message payload) = none) :
    Pr[fun result => ∃ record ∈ result.2, MessageHashInput key.parameter record.input |
      runFirstException (deficitStoppingException key exception) computation cache none] ≤ (q : ENNReal) / 2 ^ 223 :=
  (probEvent_firstDeficitMessageRecord_le_monitor key exception hparent computation cache).trans
    (probEvent_messageDeficitExceptional_le key computation q hbound hq cache hfinite hnone)

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

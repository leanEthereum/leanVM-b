import SphincsSecurity.Proof.QueryOccurrencePrefix
import SphincsSecurity.Proof.JointProbeLiveValueErasure
import SphincsSecurity.Proof.JointProbeObserverCost

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (HistoryResolvedPrefix)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def JointRawReturned (event : α → Prop) : AdaptiveRevealProbe.RawResult Coordinate (Option (HistoryResolvedPrefix α)) → Prop
  | .done _ _ (some entry) => event entry.value
  | _ => False

noncomputable def rawSourceEventProbability (table : Coordinate → Digest) (source : JointSource α) (event : α → Prop)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe) (cache : JointSourceCache) : ENNReal :=
  Pr[JointRawReturned (fun value => event value.1) |
    AdaptiveRevealProbe.runRaw table state ftsFuel (runJointErasedHistory (source.run cache) context fuel history)]

private theorem jointHistoryReturned_done_imp_raw
    (event : α → Prop) (hit : Bool) (state : AdaptiveRevealProbe.State Coordinate) (remaining : Nat)
    (result : Option (HistoryResolvedPrefix α))
    (he : JointHistoryReturned event (.done hit state result)) : JointRawReturned event (.done state remaining result) := by
  obtain ⟨entry, hentry, hevent⟩ := he
  cases hit with
  | true => cases hentry
  | false =>
      change result = some entry at hentry
      subst result
      exact hevent

private theorem jointHistoryReturned_finalize_imp_raw
    (table : Coordinate → Digest) (event : α → Prop)
    (result : AdaptiveRevealProbe.RawResult Coordinate (Option (HistoryResolvedPrefix α)))
    (he : JointHistoryReturned event (result.finalize table)) : JointRawReturned event result := by
  cases result with
  | stopped hit =>
      obtain ⟨entry, hentry, _⟩ := he
      cases hentry
  | done finalState remaining entry =>
      exact jointHistoryReturned_done_imp_raw event (AdaptiveRevealProbe.tableHits finalState table) finalState remaining entry he

theorem probEvent_jointHistoryReturned_le_raw
    (table : Coordinate → Digest) (computation : OracleComp JointProbeWorld α) (event : α → Prop)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe) :
    Pr[JointHistoryReturned event | AdaptiveRevealProbe.runDetailed table state ftsFuel (runJointErasedHistory computation context fuel history)] ≤
      Pr[JointRawReturned event | AdaptiveRevealProbe.runRaw table state ftsFuel (runJointErasedHistory computation context fuel history)] := by
  rw [← AdaptiveRevealProbe.finalize_runRaw_eq_runDetailed, probEvent_map]
  exact probEvent_mono fun result _ he => jointHistoryReturned_finalize_imp_raw table event result he

theorem rawSourceEventProbability_pure
    (table : Coordinate → Digest) (value : α) (event : α → Prop)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe) (cache : JointSourceCache) :
    rawSourceEventProbability table (jointSourceNativeBlock (pure value)) event state ftsFuel context fuel history cache =
      if event value then 1 else 0 := by
  have hbody : (jointSourceNativeBlock (pure value)).run cache =
      pure (value, prepareNativeCache cache.2 cache.1, withNativeOrdinaryCache cache.2 (prepareNativeCache cache.2 cache.1)) := rfl
  unfold rawSourceEventProbability
  rw [hbody]
  simp [runJointErasedHistory, AdaptiveRevealProbe.runRaw, JointRawReturned]

theorem rawSourceEventProbability_bind
    (table : Coordinate → Digest) (left : JointSource α) (next : α → JointSource β) (step : NativeFtsStep α)
    (hleft : JointSourceImplements left step) (event : β → Prop)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe) (cache : JointSourceCache) :
    rawSourceEventProbability table (left >>= next) event state ftsFuel context fuel history cache =
      ∑' result, Pr[= result | AdaptiveRevealProbe.runRaw table state ftsFuel ((step context fuel history cache.1).run cache.2)] *
        match result with
        | .stopped _ => 0
        | .done finalState remaining (entry, finalCache) => match entry with
          | none => 0
          | some entry => rawSourceEventProbability table (next entry.value.1) event finalState remaining
              entry.context entry.remaining entry.history (entry.value.2, finalCache) := by
  unfold rawSourceEventProbability
  rw [StateT.run_bind, runJointErasedHistory_bind, AdaptiveRevealProbe.runRaw_bind, probEvent_bind_eq_tsum,
    hleft, AdaptiveRevealProbe.runRaw_mapValue, tsum_probOutput_map_mul]
  apply tsum_congr
  intro result
  congr 1
  cases result with
  | stopped hit => simp [AdaptiveRevealProbe.RawResult.mapValue, JointRawReturned]
  | done finalState remaining value =>
      rcases value with ⟨entry, finalCache⟩
      cases entry with
      | none => simp [AdaptiveRevealProbe.RawResult.mapValue, packJointStepResult, AdaptiveRevealProbe.runRaw, JointRawReturned]
      | some entry => rfl

end SphincsSecurity.Concrete.FtsProbeSimulation

import SphincsSecurity.Proof.OtsProbeOuterCapLive
import SphincsSecurity.Proof.OtsProbeNativeErasedFts

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem runResolvedLiveValue_map
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext) (fuel : Nat)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (project : α → β) :
    runResolvedLiveValue table context fuel (project <$> computation) =
      Option.map (fun result => (result.1, project result.2)) <$> runResolvedLiveValue table context fuel computation := by
  simp only [runResolvedLiveValue, runResolvedFromTable_map, bind_map_left, map_bind]
  apply bind_congr
  intro result
  cases result with
  | none => rfl
  | some result =>
      simp only [Option.map_some]
      split_ifs <;> rfl

def someLiveValue : Option (Nat × α) → Option (Nat × Option α) :=
  Option.map (fun result => (result.1, some result.2))

theorem probEvent_live_option_le_raw
    (computation : OracleComp (LazyRevealProbe.World Coordinate) (Option α))
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (event : α → Prop) :
    Pr[fun result => ∃ remaining value, result = some (remaining, some value) ∧ event value |
      runResolvedLiveValue table context fuel computation] ≤
      Pr[fun result => ∃ value, resolvedPrefixValue result = some (some value) ∧ event value |
        runResolvedFromTable context fuel table computation] := by
  unfold runResolvedLiveValue
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  cases result with
  | none => simp [resolvedPrefixValue]
  | some result =>
      dsimp only
      by_cases hcomplete : DeferredCompletable table result.context
      · simp only [if_pos hcomplete, probEvent_pure]
        cases hvalue : result.value <;> simp [resolvedPrefixValue, hvalue]
      · simp [hcomplete]

end SphincsSecurity.Concrete.OtsProbeSimulation

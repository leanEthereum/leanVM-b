import SphincsSecurity.Proof.JointProbeResolvedOrder
import SphincsSecurity.Proof.OtsProbeSourceChargeComposition

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex)
set_option backward.isDefEq.respectTransparency false

theorem resolvedCore_of_mem_jointRaw
    (table : Coordinate → Digest) (computation : OracleComp JointProbeWorld α)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel remaining : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput)
    (entry : ResolvedRunResult α) (hconsistent : context.ValuesConsistent)
    (hstarts : OtsProbeSimulation.StartTableAgrees context.state otsTable)
    (hresult : .done finalState remaining (some entry) ∈ support
      (AdaptiveRevealProbe.runRaw table state ftsFuel (runJointResolved computation context fuel otsTable))) :
    entry.table = otsTable ∧ entry.context.ValuesConsistent ∧
      OtsProbeSimulation.StartTableAgrees entry.context.state otsTable := by
  have hmap : rawJointResolved (.done finalState remaining (some entry)) ∈ support
      (rawJointResolved <$> AdaptiveRevealProbe.runRaw table state ftsFuel (runJointResolved computation context fuel otsTable)) := by
    rw [support_map]
    exact ⟨_, hresult, rfl⟩
  rw [runJointFtsRaw_resolved_commute, support_map] at hmap
  obtain ⟨nativeOption, hnative, heq⟩ := hmap
  cases nativeOption with
  | none => simp [flattenRawResolved, rawJointResolved] at heq
  | some native =>
      have hcore := OtsProbeSimulation.resolvedCore_of_mem_runResolvedFromTable _ context fuel otsTable native hconsistent hstarts hnative
      cases hvalue : native.value with
      | stopped hit => simp [flattenRawResolved, rawJointResolved, hvalue] at heq
      | done nativeState nativeRemaining value =>
          simp only [flattenRawResolved, rawJointResolved, hvalue, Option.map_some, Option.some.injEq] at heq
          have hcontext := congrArg ResolvedRunResult.context heq
          have htable := congrArg ResolvedRunResult.table heq
          exact ⟨htable.symm.trans hcore.1, hcontext ▸ hcore.2.1, hcontext ▸ hcore.2.2⟩

end SphincsSecurity.Concrete.FtsProbeSimulation

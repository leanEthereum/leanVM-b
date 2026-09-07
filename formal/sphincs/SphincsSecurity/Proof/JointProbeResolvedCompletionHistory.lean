import SphincsSecurity.Proof.JointProbeFailurePersistence
import SphincsSecurity.Proof.OtsProbeResolvedComputedExecution

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex)
set_option backward.isDefEq.respectTransparency false

theorem exists_native_of_mem_jointDetailed
    (table : Coordinate → Digest) (computation : OracleComp JointProbeWorld α)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput)
    (entry : ResolvedRunResult α)
    (hresult : .done false finalState (some entry) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel (runJointResolved computation context fuel otsTable))) :
    ∃ native : ResolvedRunResult (Option α), some native ∈ support
      (OtsProbeSimulation.runResolvedFromTable context fuel otsTable (runJointFts table computation state ftsFuel)) ∧
      native.context = entry.context ∧ native.table = entry.table := by
  have hmap : some entry ∈ support
      (cleanJointResolved <$> AdaptiveRevealProbe.runDetailed table state ftsFuel (runJointResolved computation context fuel otsTable)) := by
    rw [support_map]
    exact ⟨_, hresult, rfl⟩
  rw [runJointFts_resolved_commute, support_map] at hmap
  obtain ⟨nativeOption, hnative, heq⟩ := hmap
  cases nativeOption with
  | none => simp [flattenOptionalResolved] at heq
  | some native =>
      cases hvalue : native.value with
      | none => simp [flattenOptionalResolved, hvalue] at heq
      | some value =>
          simp only [flattenOptionalResolved, hvalue, Option.map_some, Option.some.injEq] at heq
          subst entry
          exact ⟨native, hnative, rfl, rfl⟩

theorem completion_of_mem_jointDetailed
    (table : Coordinate → Digest) (computation : OracleComp JointProbeWorld α)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput)
    (entry : ResolvedRunResult α) (hconsistent : context.ValuesConsistent)
    (hstarts : OtsProbeSimulation.StartTableAgrees context.state otsTable)
    (hresult : .done false finalState (some entry) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel (runJointResolved computation context fuel otsTable)))
    (completion : OtsProbeSimulation.Coordinate → HashOutput)
    (hcompletion : OtsProbeSimulation.DeferredCompletion otsTable entry.context completion) :
    OtsProbeSimulation.DeferredCompletion otsTable context completion := by
  obtain ⟨native, hnative, hcontext, _⟩ := exists_native_of_mem_jointDetailed table computation state finalState ftsFuel context fuel otsTable entry hresult
  exact OtsProbeSimulation.DeferredCompletion.of_mem_runResolvedFromTable _ context fuel otsTable native completion
    hconsistent hstarts hnative (hcontext.symm ▸ hcompletion)

theorem computed_of_mem_jointDetailed
    (table : Coordinate → Digest) (computation : OracleComp JointProbeWorld α)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput)
    (entry : ResolvedRunResult α) (hcomputed : OtsProbeSimulation.DeferredComputationsClosed context)
    (hresult : .done false finalState (some entry) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel (runJointResolved computation context fuel otsTable))) :
    OtsProbeSimulation.DeferredComputationsClosed entry.context := by
  obtain ⟨native, hnative, hcontext, _⟩ := exists_native_of_mem_jointDetailed table computation state finalState ftsFuel context fuel otsTable entry hresult
  exact hcontext ▸ OtsProbeSimulation.DeferredComputationsClosed.of_mem_runResolved _ context fuel otsTable native hcomputed hnative

end SphincsSecurity.Concrete.FtsProbeSimulation

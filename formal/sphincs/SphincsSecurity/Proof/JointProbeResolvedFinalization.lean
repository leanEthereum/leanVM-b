import SphincsSecurity.Proof.JointProbeResolvedOrder

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def cleanJointResolved : AdaptiveRevealProbe.DetailedResult Coordinate (Option (ResolvedRunResult α)) →
    Option (ResolvedRunResult α)
  | .stopped _ => none
  | .done true _ _ => none
  | .done false _ result => result

def flattenOptionalResolved : Option (ResolvedRunResult (Option α)) → Option (ResolvedRunResult α)
  | none => none
  | some entry => entry.value.map (fun value => ⟨entry.context, entry.remaining, value, entry.table⟩)

theorem runJointFts_resolved_commute
    (table : Coordinate → Digest) (computation : OracleComp JointProbeWorld α)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) :
    cleanJointResolved <$>
      AdaptiveRevealProbe.runDetailed table state ftsFuel (runJointResolved computation context fuel otsTable) =
      flattenOptionalResolved <$>
        OtsProbeSimulation.runResolvedFromTable context fuel otsTable (runJointFts table computation state ftsFuel) := by
  induction computation using OracleComp.inductionOn generalizing state ftsFuel context fuel otsTable with
  | pure value =>
      simp only [runJointResolved_pure, AdaptiveRevealProbe.runDetailed, runJointFts_pure]
      cases hhit : AdaptiveRevealProbe.tableHits state table <;>
        simp [cleanJointResolved, flattenOptionalResolved, OtsProbeSimulation.runResolvedFromTable, hhit]
  | query_bind input next ih =>
      rw [runJointResolved_query_bind, runJointFts_query_bind]
      cases input with
      | inl input =>
          rw [AdaptiveRevealProbe.runDetailed_liftProbComp_bind, map_bind,
            OtsProbeSimulation.runResolvedFromTable_bind, map_bind]
          apply bind_congr
          intro result
          cases result with
          | none =>
              cases hhit : AdaptiveRevealProbe.tableHits state table <;>
                simp [AdaptiveRevealProbe.runDetailed, cleanJointResolved, flattenOptionalResolved, hhit]
          | some entry => exact ih entry.value state ftsFuel entry.context entry.remaining entry.table
      | inr input =>
          cases input with
          | uniform n =>
              rw [AdaptiveRevealProbe.runDetailed_uniform_query_bind, map_bind]
              simp only [OtsProbeSimulation.runResolvedFromTable]
              exact bind_congr (fun output => ih output state ftsFuel context fuel otsTable)
          | hashOutput =>
              rw [AdaptiveRevealProbe.runDetailed_hashOutput_query_bind, map_bind]
              simp only [OtsProbeSimulation.runResolvedFromTable]
              exact bind_congr (fun output => ih output state ftsFuel context fuel otsTable)
          | probe coordinate candidate =>
              rw [AdaptiveRevealProbe.runDetailed_probe_query_bind]
              dsimp only
              cases ftsFuel with
              | zero =>
                  simp [cleanJointResolved, flattenOptionalResolved, OtsProbeSimulation.runResolvedFromTable]
              | succ remaining =>
                  cases state.revealed coordinate with
                  | none => exact ih () (state.addPending coordinate candidate) remaining context fuel otsTable
                  | some value => exact ih () state remaining context fuel otsTable
          | reveal coordinate =>
              rw [AdaptiveRevealProbe.runDetailed_reveal_query_bind]
              dsimp only
              cases state.revealed coordinate with
              | some value => exact ih value state ftsFuel context fuel otsTable
              | none =>
                  split_ifs
                  · simp [cleanJointResolved, flattenOptionalResolved, OtsProbeSimulation.runResolvedFromTable]
                  · exact ih (table coordinate) (state.install coordinate (table coordinate)) ftsFuel context fuel otsTable

theorem runJointResolved_probeBound (computation : OracleComp JointProbeWorld α)
    (q : Nat) (hbound : computation.IsQueryBoundP JointProbeIsProbe q)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) :
    (runJointResolved computation context fuel otsTable).IsQueryBoundP AdaptiveRevealProbe.IsProbe q := by
  induction computation using OracleComp.inductionOn generalizing q context fuel otsTable with
  | pure value => simp [runJointResolved_pure]
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      rw [runJointResolved_query_bind]
      cases input with
      | inl input =>
          dsimp only
          refine (OracleComp.isQueryBoundP_bind (n := 0) (m := q)
            (AdaptiveRevealProbe.liftProbComp_isProbeBound _ 0) ?_).mono (by omega)
          intro result _
          cases result with
          | none => simp
          | some entry =>
              apply (ih entry.value _ (hbound.2 entry.value) entry.context entry.remaining entry.table).mono
              split_ifs <;> omega
      | inr input =>
          rw [isQueryBoundP_query_bind_iff]
          refine ⟨hbound.1, fun output => ih output _ ?_ context fuel otsTable⟩
          by_cases hp : AdaptiveRevealProbe.IsProbe input <;> simpa [JointProbeIsProbe, hp] using hbound.2 output

end SphincsSecurity.Concrete.FtsProbeSimulation

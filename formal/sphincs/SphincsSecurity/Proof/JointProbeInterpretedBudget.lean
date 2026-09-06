import SphincsSecurity.Proof.JointProbeInterpreterOrder

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] jointSourceRetained jointRetainedDetailed OtsProbeSimulation.maskedPublishedTreeRoot

theorem runJointErasedHistory_probeBound (computation : OracleComp JointProbeWorld α)
    (q : Nat) (hbound : computation.IsQueryBoundP JointProbeIsProbe q)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe) :
    (runJointErasedHistory computation context fuel history).IsQueryBoundP AdaptiveRevealProbe.IsProbe q := by
  induction computation using OracleComp.inductionOn generalizing q context fuel history with
  | pure value => simp [runJointErasedHistory_pure]
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      rw [runJointErasedHistory_query_bind]
      cases input with
      | inl input =>
          dsimp only
          refine (OracleComp.isQueryBoundP_bind (n := 0) (m := q)
            (AdaptiveRevealProbe.liftProbComp_isProbeBound _ 0) ?_).mono (by omega)
          intro result _
          cases result with
          | none => simp
          | some entry =>
              apply (ih entry.value _ (hbound.2 entry.value) entry.context entry.remaining entry.history).mono
              split_ifs <;> omega
      | inr input =>
          rw [isQueryBoundP_query_bind_iff]
          refine ⟨hbound.1, fun output => ih output _ ?_ context fuel history⟩
          by_cases hp : AdaptiveRevealProbe.IsProbe input <;> simpa [JointProbeIsProbe, hp] using hbound.2 output

theorem jointRetainedDetailed_not_stopped_false
    (adversary : Adversary) (parameter : PublicParameter) (table : Coordinate → Digest) (q : Nat) :
    AdaptiveRevealProbe.DetailedResult.stopped false ∉ support (jointRetainedDetailed adversary parameter table q) := by
  intro hresult
  have hmap : AdaptiveRevealProbe.DetailedResult.stopped false ∈ support
      (AdaptiveRevealProbe.DetailedResult.mapValue packJointStepResult <$> jointRetainedDetailed adversary parameter table q) := by
    rw [support_map]
    exact ⟨_, hresult, rfl⟩
  rw [← runDetailed_jointSourceRetained] at hmap
  exact AdaptiveRevealProbe.stopped_false_not_mem_support_runDetailed table AdaptiveRevealProbe.State.empty q _
    (runJointErasedHistory_probeBound _ q (jointSourceRetained_probeBound adversary parameter q _)
      (OtsProbeSimulation.ensuredInitialContext ∅) 0 []) hmap

end SphincsSecurity.Concrete.FtsProbeSimulation

import SphincsSecurity.Proof.OtsProbeErasedHistoryTotal
import SphincsSecurity.Proof.JointProbeErasedFields

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (HistoryResolvedPrefix)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] jointRetainedDetailed jointSourceRetained

theorem runJointErasedHistory_not_done_none
    (table : Coordinate → Digest) (computation : OracleComp JointProbeWorld α)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat) (hit : Bool)
    (context : OtsProbeSimulation.DeferredContext)
    (hconsistent : context.ValuesConsistent) (hpending : context.state.pending = ∅) :
    .done hit finalState none ∉ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel (runJointErasedHistory computation context 0 [])) := by
  intro hresult
  induction computation using OracleComp.inductionOn generalizing state ftsFuel context with
  | pure value => simp [runJointErasedHistory_pure, AdaptiveRevealProbe.runDetailed] at hresult
  | query_bind input next ih =>
      rw [runJointErasedHistory_query_bind] at hresult
      cases input with
      | inl input =>
          rw [AdaptiveRevealProbe.runDetailed_liftProbComp_bind, mem_support_bind_iff] at hresult
          obtain ⟨entry, hentry, htail⟩ := hresult
          cases entry with
          | none =>
              exact OtsProbeSimulation.none_not_mem_historyPrefix_of_probeFree _ context 0
                (OtsProbeSimulation.eraseProbeQueries_probeFree _) hconsistent hpending hentry
          | some entry =>
              have hinvariant := OtsProbeSimulation.erasedHistoryPrefix_some_invariants _ context entry hconsistent hpending hentry
              have hfields := OtsProbeSimulation.erasedHistoryPrefix_fields _ context entry hentry
              dsimp only at htail
              rw [hfields.1, hfields.2] at htail
              exact ih entry.value state ftsFuel entry.context hinvariant.1 hinvariant.2.1 htail
      | inr input =>
          cases input with
          | uniform n =>
              rw [AdaptiveRevealProbe.runDetailed_uniform_query_bind, mem_support_bind_iff] at hresult
              obtain ⟨output, _, htail⟩ := hresult
              exact ih output state ftsFuel context hconsistent hpending htail
          | hashOutput =>
              rw [AdaptiveRevealProbe.runDetailed_hashOutput_query_bind, mem_support_bind_iff] at hresult
              obtain ⟨output, _, htail⟩ := hresult
              exact ih output state ftsFuel context hconsistent hpending htail
          | probe coordinate candidate =>
              rw [AdaptiveRevealProbe.runDetailed_probe_query_bind] at hresult
              cases ftsFuel with
              | zero => simp at hresult
              | succ remaining =>
                  cases hrevealed : state.revealed coordinate with
                  | none =>
                      rw [hrevealed] at hresult
                      exact ih () (state.addPending coordinate candidate) remaining context hconsistent hpending hresult
                  | some value =>
                      rw [hrevealed] at hresult
                      exact ih () state remaining context hconsistent hpending hresult
          | reveal coordinate =>
              rw [AdaptiveRevealProbe.runDetailed_reveal_query_bind] at hresult
              cases hrevealed : state.revealed coordinate with
              | some value =>
                  rw [hrevealed] at hresult
                  exact ih value state ftsFuel context hconsistent hpending hresult
              | none =>
                  rw [hrevealed] at hresult
                  dsimp only at hresult
                  split_ifs at hresult with hhit
                  · simp at hresult
                  · exact ih (table coordinate) (state.install coordinate (table coordinate)) ftsFuel context hconsistent hpending hresult

theorem jointRetainedDetailed_not_done_native_none
    (adversary : Adversary) (parameter : PublicParameter) (table : Coordinate → Digest) (q : Nat)
    (state : AdaptiveRevealProbe.State Coordinate) (cache : SplitHashCache) (hit : Bool) :
    .done hit state (none, cache) ∉ support (jointRetainedDetailed adversary parameter table q) := by
  intro hresult
  have hmap : .done hit state none ∈ support
      (AdaptiveRevealProbe.DetailedResult.mapValue packJointStepResult <$>
        jointRetainedDetailed adversary parameter table q) := by
    rw [support_map]
    exact ⟨_, hresult, rfl⟩
  rw [← runDetailed_jointSourceRetained] at hmap
  exact runJointErasedHistory_not_done_none table _ AdaptiveRevealProbe.State.empty state q hit
    (OtsProbeSimulation.ensuredInitialContext ∅)
    (OtsProbeSimulation.ensuredInitialContext_valid ∅).valuesConsistent rfl hmap

theorem jointRetainedFailure_iff_hit
    (adversary : Adversary) (parameter : PublicParameter) (table : Coordinate → Digest) (q : Nat)
    (result : AdaptiveRevealProbe.DetailedResult Coordinate (NativeStepResult (Option RetainedGameResult) × SplitHashCache))
    (hresult : result ∈ support (jointRetainedDetailed adversary parameter table q)) :
    JointRetainedFailure result ↔ result.hit = true := by
  refine ⟨?_, Or.inl⟩
  rintro (hhit | ⟨state, cache, rfl⟩)
  · exact hhit
  · exact False.elim (jointRetainedDetailed_not_done_native_none adversary parameter table q state cache false hresult)

theorem probEvent_nativeFtsErased_value_none_le_hit
    (adversary : Adversary) (parameter : PublicParameter) (table : Coordinate → Digest) (q : Nat) :
    Pr[fun result => OtsProbeSimulation.historyPrefixValue result = some none |
      nativeFtsRetainedErasedHistory adversary parameter table q] ≤ jointRetainedFtsHitRisk adversary parameter table q := by
  apply (probEvent_mono (q := fun result => flattenOptionalHistory result = none) (fun result _ hevent => by
    cases result with
    | none => simp [OtsProbeSimulation.historyPrefixValue] at hevent
    | some entry =>
        simp only [OtsProbeSimulation.historyPrefixValue, Option.map_some, Option.some.injEq] at hevent
        simp [flattenOptionalHistory, hevent])).trans_eq
  rw [← probEvent_jointRetainedFailure_eq_nativeFts]
  apply probEvent_congr' _ rfl
  exact jointRetainedFailure_iff_hit adversary parameter table q

end SphincsSecurity.Concrete.FtsProbeSimulation

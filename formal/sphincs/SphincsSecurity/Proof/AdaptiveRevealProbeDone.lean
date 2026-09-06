import SphincsSecurity.Proof.AdaptiveRevealProbe

namespace SphincsSecurity.AdaptiveRevealProbe

open OracleComp OracleSpec ENNReal

variable {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]

theorem tableHits_of_mem_runDetailed_done
    (table : Coordinate → Digest) (state finalState : State Coordinate) (fuel : Nat)
    (computation : OracleComp (World Coordinate) α) (hit : Bool) (value : α)
    (hresult : .done hit finalState value ∈ support (runDetailed table state fuel computation)) :
    tableHits finalState table = hit := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure result =>
      simp only [runDetailed, construct_pure, mem_support_pure_iff, DetailedResult.done.injEq] at hresult
      obtain ⟨rfl, rfl, _⟩ := hresult
      rfl
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runDetailed_uniform_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _, hrest⟩ := hresult
          exact ih output state fuel hrest
      | hashOutput =>
          rw [runDetailed_hashOutput_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _, hrest⟩ := hresult
          exact ih output state fuel hrest
      | probe coordinate candidate =>
          rw [runDetailed_probe_query_bind] at hresult
          cases fuel with
          | zero => simp at hresult
          | succ remaining =>
              cases hlookup : state.revealed coordinate with
              | none => exact ih () (state.addPending coordinate candidate) remaining (by simpa [hlookup] using hresult)
              | some output => exact ih () state remaining (by simpa [hlookup] using hresult)
      | reveal coordinate =>
          rw [runDetailed_reveal_query_bind] at hresult
          cases hlookup : state.revealed coordinate with
          | some output => exact ih output state fuel (by simpa [hlookup] using hresult)
          | none =>
              simp only [hlookup] at hresult
              split_ifs at hresult with hhit
              · simp at hresult
              · exact ih (table coordinate) (state.install coordinate (table coordinate)) fuel hresult

end SphincsSecurity.AdaptiveRevealProbe

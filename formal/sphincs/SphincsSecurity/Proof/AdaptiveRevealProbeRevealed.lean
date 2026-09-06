import SphincsSecurity.Proof.AdaptiveRevealProbe

namespace SphincsSecurity.AdaptiveRevealProbe

open OracleComp OracleSpec ENNReal

variable {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]

theorem revealed_of_mem_runDetailed_done
    (table : Coordinate → Digest) (state finalState : State Coordinate) (fuel : Nat)
    (computation : OracleComp (World Coordinate) α) (hit : Bool) (value : α)
    (coordinate : Coordinate) (output : Digest)
    (hrevealed : state.revealed coordinate = some output)
    (hresult : .done hit finalState value ∈ support (runDetailed table state fuel computation)) :
    finalState.revealed coordinate = some output := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure result =>
      simp only [runDetailed, construct_pure, mem_support_pure_iff, DetailedResult.done.injEq] at hresult
      obtain ⟨_, rfl, _⟩ := hresult
      exact hrevealed
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runDetailed_uniform_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨reply, _, hrest⟩ := hresult
          exact ih reply state fuel hrevealed hrest
      | hashOutput =>
          rw [runDetailed_hashOutput_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨reply, _, hrest⟩ := hresult
          exact ih reply state fuel hrevealed hrest
      | probe target candidate =>
          rw [runDetailed_probe_query_bind] at hresult
          cases fuel with
          | zero => simp at hresult
          | succ remaining =>
              cases hlookup : state.revealed target with
              | none => exact ih () (state.addPending target candidate) remaining hrevealed (by simpa [hlookup] using hresult)
              | some reply => exact ih () state remaining hrevealed (by simpa [hlookup] using hresult)
      | reveal target =>
          rw [runDetailed_reveal_query_bind] at hresult
          cases hlookup : state.revealed target with
          | some reply => exact ih reply state fuel hrevealed (by simpa [hlookup] using hresult)
          | none =>
              simp only [hlookup] at hresult
              split_ifs at hresult with hhit
              · simp at hresult
              · apply ih (table target) (state.install target (table target)) fuel _ hresult
                have hne : coordinate ≠ target := by intro h; subst target; simp [hlookup] at hrevealed
                simpa [State.install, hne] using hrevealed

end SphincsSecurity.AdaptiveRevealProbe

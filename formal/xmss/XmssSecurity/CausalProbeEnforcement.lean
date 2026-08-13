import XmssSecurity.CausalFilteredGame

open OracleComp OracleSpec

namespace XmssSecurity.RevealProbeOracleSimulation

variable {Index : Type} [Fintype Index] [DecidableEq Index]

def probeEnforcementImpl :
    QueryImpl (World Index) (StateT Nat (OracleComp (World Index))) :=
  fun input fuel =>
    match input with
    | .uniform n => do
        let output ← uniformQuery n
        pure (output, fuel)
    | .probe index target =>
        match fuel with
        | 0 => pure ((), 0)
        | remaining + 1 => do
            probeQuery index target
            pure ((), remaining)
    | .reveal index => do
        let value ← revealQuery index
        pure (value, fuel)

noncomputable def enforceProbeBound
    (fuel : Nat) (computation : OracleComp (World Index) α) :
    OracleComp (World Index) α :=
  Prod.fst <$> (simulateQ probeEnforcementImpl computation).run fuel

theorem simulate_probeEnforcementImpl_run_isProbeQueryBoundP
    (computation : OracleComp (World Index) α) (fuel : Nat) :
    (simulateQ probeEnforcementImpl computation).run fuel |>.IsQueryBoundP
      IsProbeQuery fuel := by
  induction computation using OracleComp.inductionOn generalizing fuel with
  | pure result => simp
  | query_bind input next ih =>
      rw [simulateQ_query_bind, StateT.run_bind]
      cases input with
      | uniform n =>
          change (uniformQuery n >>= fun output =>
            (simulateQ probeEnforcementImpl (next output)).run fuel)
              |>.IsQueryBoundP IsProbeQuery fuel
          rw [uniformQuery, OracleComp.isQueryBoundP_query_bind_iff]
          constructor
          · simp [IsProbeQuery]
          · intro output
            simpa [IsProbeQuery] using ih output fuel
      | probe index target =>
          cases fuel with
          | zero => simpa [probeEnforcementImpl] using ih () 0
          | succ remaining =>
              change (probeQuery index target >>= fun _ =>
                (simulateQ probeEnforcementImpl (next ())).run remaining)
                  |>.IsQueryBoundP IsProbeQuery (remaining + 1)
              rw [probeQuery, OracleComp.isQueryBoundP_query_bind_iff]
              constructor
              · simp [IsProbeQuery]
              · intro _
                simpa [IsProbeQuery] using ih () remaining
      | reveal index =>
          change (revealQuery index >>= fun value =>
            (simulateQ probeEnforcementImpl (next value)).run fuel)
              |>.IsQueryBoundP IsProbeQuery fuel
          rw [revealQuery, OracleComp.isQueryBoundP_query_bind_iff]
          constructor
          · simp [IsProbeQuery]
          · intro value
            simpa [IsProbeQuery] using ih value fuel

theorem enforceProbeBound_isProbeQueryBoundP
    (fuel : Nat) (computation : OracleComp (World Index) α) :
    (enforceProbeBound fuel computation).IsQueryBoundP IsProbeQuery fuel := by
  unfold enforceProbeBound
  apply (OracleComp.isQueryBoundP_map_iff _ _ fuel).2
  exact simulate_probeEnforcementImpl_run_isProbeQueryBoundP computation fuel

end XmssSecurity.RevealProbeOracleSimulation

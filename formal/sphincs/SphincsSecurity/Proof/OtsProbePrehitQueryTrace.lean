import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.EncodingPrehitViewedTrace
import SphincsSecurity.Proof.OtsProbeCanonicalSelectionCoupling

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

structure PrehitQuerySnapshot where
  input : (OracleWorld + SigningSpec).Domain
  state : ViewedFullTraceState × Bool

def PrehitQuerySnapshot.actual (entry : PrehitQuerySnapshot) : ActualQuerySelection :=
  ⟨entry.input, entry.state.1.cache⟩

noncomputable def runPrehitQueryTrace (accountingKey secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ViewedFullTraceState × Bool →
      ProbComp ((α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot) :=
  OracleComp.construct (fun value state => pure ((value, state), []))
    (fun input _ next state => do
      let result ← (encodingPrehitViewedAdversaryImpl accountingKey secretKey input).run state
      let tail ← next result.1 result.2
      pure (tail.1, (⟨input, state⟩ : PrehitQuerySnapshot) :: tail.2)) computation

theorem runPrehitQueryTrace_query_bind (accountingKey secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (state : ViewedFullTraceState × Bool) :
    runPrehitQueryTrace accountingKey secretKey (OracleSpec.query input >>= next) state = (do
      let result ← (encodingPrehitViewedAdversaryImpl accountingKey secretKey input).run state
      let tail ← runPrehitQueryTrace accountingKey secretKey (next result.1) result.2
      pure (tail.1, (⟨input, state⟩ : PrehitQuerySnapshot) :: tail.2)) := rfl

theorem runPrehitQueryTrace_projection (accountingKey secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : ViewedFullTraceState × Bool) :
    Prod.fst <$> runPrehitQueryTrace accountingKey secretKey computation state =
      (simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey) computation).run state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp [runPrehitQueryTrace]
  | query_bind input next ih =>
      rw [runPrehitQueryTrace_query_bind]
      simp only [map_bind, map_pure, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      apply bind_congr
      intro result
      simpa only [map_eq_bind_pure_comp, Function.comp_def] using ih result.1 result.2

end SphincsSecurity.Concrete.OtsProbeSimulation

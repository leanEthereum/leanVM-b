import SphincsSecurity.Proof.QueryPause

namespace SphincsSecurity.QueryPause

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {Source Target Memory Result : Type} {source : OracleSpec Source} {target : OracleSpec Target}

theorem run_translation (stop : Memory → Prop) [DecidablePred stop]
    (sourceStep : (input : source.Domain) → source.Range input → Memory → Memory)
    (targetStep : (input : target.Domain) → target.Range input → Memory → Memory)
    (queryMap : source.Domain → target.Domain)
    (answerMap : (input : source.Domain) → target.Range (queryMap input) → source.Range input)
    (impl : QueryImpl source (OracleComp target))
    (himpl : ∀ input, impl input = answerMap input <$> liftM (target.query (queryMap input)))
    (hstep : ∀ input answer memory, targetStep (queryMap input) answer memory = sourceStep input (answerMap input answer) memory)
    (computation : OracleComp source Result) (memory : Memory) :
    run stop targetStep (simulateQ impl computation) memory =
      (fun paused => (paused.1, simulateQ impl paused.2)) <$> simulateQ impl (run stop sourceStep computation memory) := by
  induction computation using OracleComp.inductionOn generalizing memory with
  | pure result => simp only [simulateQ_pure, run_pure, map_pure]
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, himpl, bind_map_left, run_query_bind]
      by_cases hs : stop memory
      · simp only [if_pos hs, simulateQ_pure, map_pure, simulateQ_bind, simulateQ_spec_query, himpl, bind_map_left]
      · simp only [if_neg hs, simulateQ_bind, simulateQ_spec_query, himpl, bind_map_left, map_bind, hstep, ih]

end SphincsSecurity.QueryPause

import XmssSecurity.Statement
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

noncomputable def xmssRomImpl :
    QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp) :=
  unifFwdImpl HashSpec +
    (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))

theorem xmssRom_lift_probComp_cache_eq {α : Type} (computation : ProbComp α)
    (initialCache : QueryCache HashSpec) (result : α × QueryCache HashSpec)
    (hmem : result ∈ support
      ((simulateQ xmssRomImpl (liftM computation)).run initialCache)) :
    result.2 = initialCache := by
  have hsupport := roSim.run_liftM_support
    (hashSpec := HashSpec)
    (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
    computation initialCache
  rw [show support ((simulateQ xmssRomImpl (liftM computation)).run initialCache) =
      (fun output => (output, initialCache)) '' support computation by
    simpa [xmssRomImpl] using hsupport] at hmem
  obtain ⟨output, _houtput, heq⟩ := hmem
  exact (congrArg Prod.snd heq).symm

theorem xmssRom_cache_le {α : Type} (computation : OracleComp OracleWorld α)
    (initialCache : QueryCache HashSpec) (result : α × QueryCache HashSpec)
    (hmem : result ∈ support ((simulateQ xmssRomImpl computation).run initialCache)) :
    initialCache ≤ result.2 := by
  induction computation using OracleComp.inductionOn generalizing initialCache result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hmem
      subst result
      exact le_rfl
  | query_bind input next ih =>
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨output, middleCache⟩, hquery, hrest⟩ := hmem
      have hmiddle : initialCache ≤ middleCache := by
        cases input with
        | inl uniformInput =>
            change unifSpec.Range uniformInput at output
            have hrun :
                (unifFwdImpl HashSpec uniformInput).run initialCache =
                  (fun sample => (sample, initialCache)) <$>
                    (liftM (unifSpec.query uniformInput) : ProbComp _) := by
              simpa [simulateQ_query] using
                (unifFwdImpl.simulateQ_run
                  (hashSpec := HashSpec)
                  (liftM (unifSpec.query uniformInput) : ProbComp _) initialCache)
            simp only [simulateQ_spec_query, xmssRomImpl, QueryImpl.add_apply] at hquery
            have hquery' : (output, middleCache) ∈
                support ((unifFwdImpl HashSpec uniformInput).run initialCache) := hquery
            rw [hrun, support_map] at hquery'
            obtain ⟨sample, _hsample, heq⟩ := hquery'
            exact le_of_eq (congrArg Prod.snd heq)
        | inr hashInput =>
            rw [show simulateQ xmssRomImpl
                (liftM (OracleWorld.query (Sum.inr hashInput))) =
                (randomOracle : QueryImpl HashSpec
                  (StateT (QueryCache HashSpec) ProbComp)) hashInput by
              simp [xmssRomImpl]] at hquery
            exact QueryImpl.withCaching_cache_le uniformSampleImpl hashInput initialCache
              (output, middleCache) hquery
      exact hmiddle.trans (ih output middleCache result (by simpa using hrest))

/-- The full security game with the final lazy random-oracle cache kept in its output. -/
noncomputable def gameWithCache (scheme : Scheme) (adversary : Adversary scheme) :
    ProbComp (Bool × QueryCache HashSpec) :=
  (simulateQ xmssRomImpl (gameCore scheme adversary)).run ∅

/-- Keeping the final cache does not change the winning probability. -/
theorem forgeAdvantage_eq_gameWithCache (scheme : Scheme) (adversary : Adversary scheme) :
    forgeAdvantage scheme adversary =
      Pr[fun outcome => outcome.1 = true | gameWithCache scheme adversary] := by
  have hunif :
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (QueryCache HashSpec) ProbComp) = unifFwdImpl HashSpec := by
    simp [QueryImpl.liftTarget_apply, HasQuery.toQueryImpl, unifFwdImpl, funext_iff]
  unfold forgeAdvantage Rom.runtime ProbCompRuntime.evalDist
    SPMFSemantics.evalDist SemanticsVia.denote SPMFSemantics.withStateOracle
    simulateQ'
  rw [hunif]
  change Pr[= true | (liftM (Prod.fst <$> gameWithCache scheme adversary) : SPMF Bool)] =
    Pr[fun outcome => outcome.1 = true | gameWithCache scheme adversary]
  rw [liftM_map, ← probEvent_eq_eq_probOutput, probEvent_map]
  rfl

end XmssSecurity

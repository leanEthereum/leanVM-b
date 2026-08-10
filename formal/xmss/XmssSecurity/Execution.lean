import XmssSecurity.SecurityGame
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

noncomputable def xmssRomImpl :
    QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp) :=
  unifFwdImpl HashSpec +
    (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))

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

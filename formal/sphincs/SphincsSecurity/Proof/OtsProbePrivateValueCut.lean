import SphincsSecurity.Proof.OtsProbePrivateValueExecution

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

inductive PrivateValueCut (α : Type) where
  | done (value : α)
  | query (input : LazyRevealProbe.Query Coordinate)
      (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α)

def PrivateValueCut.resume : PrivateValueCut α → OracleComp (LazyRevealProbe.World Coordinate) α
  | .done value => pure value
  | .query input next => (liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next

noncomputable def privateValueExposureCut
    (target : Position) (before after : HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    OracleComp (LazyRevealProbe.World Coordinate) (PrivateValueCut α) :=
  OracleComp.construct (fun value => pure (.done value))
    (fun input next recursivelyCut =>
      if IsPrivateValueExposure target before after input then pure (.query input next)
      else (liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= recursivelyCut) computation

theorem privateValueExposureCut_query_bind
    (target : Position) (before after : HashOutput) (input : LazyRevealProbe.Query Coordinate)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α) :
    privateValueExposureCut target before after ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next) =
      (if IsPrivateValueExposure target before after input then pure (.query input next)
      else (liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>=
        fun output => privateValueExposureCut target before after (next output)) := rfl

theorem privateValueExposureCut_resume
    (target : Position) (before after : HashOutput) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    privateValueExposureCut target before after computation >>= PrivateValueCut.resume = computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rw [privateValueExposureCut_query_bind]
      split_ifs
      · rfl
      · rw [bind_assoc]
        exact bind_congr ih

theorem privateValueExposureCut_no_exposure
    (target : Position) (before after : HashOutput) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    (privateValueExposureCut target before after computation).IsQueryBoundP
      (IsPrivateValueExposure target before after) 0 := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [privateValueExposureCut]
  | query_bind input next ih =>
      rw [privateValueExposureCut_query_bind]
      split_ifs with hinput
      · simp
      · rw [OracleComp.isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl hinput, fun output => by simpa only [if_neg hinput] using ih output⟩

theorem privateValueExposureCut_swap
    (target : Position) (before after : HashOutput) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    privateValueExposureCut target before after computation = privateValueExposureCut target after before computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      have hexposure : IsPrivateValueExposure target before after input ↔ IsPrivateValueExposure target after before input := by
        cases input <;> simp [IsPrivateValueExposure, or_comm]
      rw [privateValueExposureCut_query_bind, privateValueExposureCut_query_bind, propext hexposure]
      split_ifs
      · rfl
      · exact bind_congr ih

theorem evalDist_privateValueExposureCut_replace
    (target : Position) (before after : HashOutput) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (h : PrivatePositionReplaceable target before after context) :
    evalDist (runResolvedFromTable (replacePrivatePosition target after context) fuel table
      (privateValueExposureCut target before after computation)) =
      evalDist (Option.map (replacePrivateRunResult target after) <$>
        runResolvedFromTable context fuel table (privateValueExposureCut target before after computation)) :=
  evalDist_runResolved_replacePrivatePosition target before after _ context fuel table h
    (privateValueExposureCut_no_exposure target before after computation)

theorem evalDist_privateValueExposureCut_value_replace
    (target : Position) (before after : HashOutput) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (h : PrivatePositionReplaceable target before after context) :
    evalDist (Option.map ResolvedRunResult.value <$> runResolvedFromTable (replacePrivatePosition target after context)
      fuel table (privateValueExposureCut target before after computation)) =
      evalDist (Option.map ResolvedRunResult.value <$>
        runResolvedFromTable context fuel table (privateValueExposureCut target before after computation)) := by
  rw [evalDist_map, evalDist_privateValueExposureCut_replace target before after computation context fuel table h,
    ← evalDist_map, Functor.map_map]
  congr 1
  apply congrArg (fun f => f <$> runResolvedFromTable context fuel table
    (privateValueExposureCut target before after computation))
  funext result
  cases result <;> rfl

theorem evalDist_privateValueExposureCut_preload_swap
    (target : Position) (before after : HashOutput) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hstate : context.state.values (.position target) = none)
    (hbefore : ¬context.state.hitAt (.position target) before)
    (hafter : ¬context.state.hitAt (.position target) after) :
    evalDist (Option.map ResolvedRunResult.value <$> runResolvedFromTable (replacePrivatePosition target before context)
      fuel table (privateValueExposureCut target before after computation)) =
      evalDist (Option.map ResolvedRunResult.value <$> runResolvedFromTable (replacePrivatePosition target after context)
        fuel table (privateValueExposureCut target after before computation)) := by
  have hreplaceable : PrivatePositionReplaceable target before after (replacePrivatePosition target before context) := by
    exact ⟨hstate, by simp [replacePrivatePosition, DeferredStructuralValues.install], hbefore, hafter⟩
  have hreplace := evalDist_privateValueExposureCut_value_replace target before after computation
    (replacePrivatePosition target before context) fuel table hreplaceable
  rw [privateValueExposureCut_swap target after before computation]
  simpa [replacePrivatePosition, DeferredStructuralValues.install] using hreplace.symm

end SphincsSecurity.Concrete.OtsProbeSimulation

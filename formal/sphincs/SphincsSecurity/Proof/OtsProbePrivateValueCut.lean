import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbePrivateValueExecution

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

inductive PrivateValueCut (α : Type) where
  | done (value : α)
  | query (input : LazyRevealProbe.Query Coordinate)
      (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α)

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

end SphincsSecurity.Concrete.OtsProbeSimulation

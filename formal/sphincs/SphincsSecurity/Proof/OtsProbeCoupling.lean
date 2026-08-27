import SphincsSecurity.Proof.OtsProbeTrace
import SphincsSecurity.Proof.FtsProbeProbability

/-!
# Retained one-time game coupling

The ordinary side of the split probing oracle is exactly the real lazy random oracle. This module
packages that distributional identity as the relational kernel used by the retained-game lift.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def RawOrdinaryResultRel :
    LazyRevealProbe.RawResult Coordinate (alpha × SplitHashCache) →
      (alpha × QueryCache HashSpec) → Prop
  | .stopped _, _ => False
  | .done _ _ (value, cache), ordinaryResult =>
      ordinaryResult = (value, ordinaryQueryCache cache)

def RawOrdinaryResultRelAt
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat) :
    LazyRevealProbe.RawResult Coordinate (alpha × SplitHashCache) →
      (alpha × QueryCache HashSpec) → Prop
  | .stopped _, _ => False
  | .done finalState remaining (value, cache), ordinaryResult =>
      finalState = state ∧ remaining = fuel ∧
        ordinaryResult = (value, ordinaryQueryCache cache)

theorem relTriple_runRaw_splitUniformImpl
    (n : Nat) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache) (fuel : Nat) :
    RelTriple
      (LazyRevealProbe.runRaw state fuel ((splitUniformImpl n).run cache))
      ((liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>= fun output =>
        pure (output, ordinaryQueryCache cache))
      (RawOrdinaryResultRelAt (alpha := Fin (n + 1)) state fuel) := by
  let uniform : ProbComp (Fin (n + 1)) := liftM (unifSpec.query n)
  have hself : RelTriple uniform uniform fun left right => left = right :=
    relTriple_refl uniform
  have hpre : RelTriple uniform uniform fun left right =>
      RawOrdinaryResultRelAt state fuel
        (.done state fuel (left, cache)) (right, ordinaryQueryCache cache) := by
    apply relTriple_post_mono hself
    intro left right heq
    subst right
    simp [RawOrdinaryResultRelAt]
  have hmapped := relTriple_map
    (R := RawOrdinaryResultRelAt (alpha := Fin (n + 1)) state fuel)
    (f := fun output => LazyRevealProbe.RawResult.done state fuel (output, cache))
    (g := fun output => (output, ordinaryQueryCache cache)) hpre
  simpa [uniform, splitUniformImpl, LazyRevealProbe.uniformQuery,
    LazyRevealProbe.runRaw_uniform_query_bind, LazyRevealProbe.runRaw,
    map_eq_bind_pure_comp] using hmapped

set_option maxRecDepth 10000 in
theorem relTriple_runRaw_simulateQ_ordinaryHashImpl
    [Inhabited alpha]
    (computation : OracleComp HashSpec alpha)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache) (fuel : Nat) :
    RelTriple
      (LazyRevealProbe.runRaw state fuel
        ((simulateQ ordinaryHashImpl computation).run cache))
      ((simulateQ (randomOracle : QueryImpl HashSpec _) computation).run
        (ordinaryQueryCache cache))
      (RawOrdinaryResultRel (alpha := alpha)) := by
  have hproject :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_of_project_eq_some_exact
      projectRawOrdinary
      (default, ∅)
      (LazyRevealProbe.runRaw state fuel
        ((simulateQ ordinaryHashImpl computation).run cache))
      ((simulateQ (randomOracle : QueryImpl HashSpec _) computation).run
        (ordinaryQueryCache cache))
      (projectRawOrdinary_simulateQ_ordinaryHashImpl computation state cache fuel)
  apply relTriple_post_mono hproject
  intro rawResult ordinaryResult hrelation
  cases rawResult with
  | stopped hit => simp [projectRawOrdinary] at hrelation
  | done finalState remaining valueCache =>
      rcases valueCache with ⟨value, finalCache⟩
      change ordinaryResult = (value, ordinaryQueryCache finalCache)
      exact (Option.some.inj hrelation).symm

set_option maxRecDepth 10000 in
theorem relTriple_runRaw_simulateQ_ordinaryHashImpl_at
    [Inhabited alpha]
    (computation : OracleComp HashSpec alpha)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache) (fuel : Nat) :
    RelTriple
      (LazyRevealProbe.runRaw state fuel
        ((simulateQ ordinaryHashImpl computation).run cache))
      ((simulateQ (randomOracle : QueryImpl HashSpec _) computation).run
        (ordinaryQueryCache cache))
      (RawOrdinaryResultRelAt (alpha := alpha) state fuel) := by
  have hbase := relTriple_runRaw_simulateQ_ordinaryHashImpl computation state cache fuel
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun result => match result with
        | .stopped _ => True
        | .done finalState remaining _ => finalState = state ∧ remaining = fuel)
      (by
        intro result hresult
        cases result with
        | stopped hit => trivial
        | done finalState remaining valueCache =>
            rcases valueCache with ⟨value, finalCache⟩
            have hprojection := mem_runRaw_simulateQ_ordinaryHashImpl_projects computation state
              finalState cache finalCache fuel remaining value hresult
            exact ⟨hprojection.1, hprojection.2.1⟩)
  apply relTriple_post_mono hsupported
  intro rawResult ordinaryResult hrelation
  cases rawResult with
  | stopped hit => exact hrelation.1
  | done finalState remaining valueCache =>
      rcases valueCache with ⟨value, finalCache⟩
      exact ⟨hrelation.2.1, hrelation.2.2, hrelation.1⟩

set_option maxRecDepth 10000 in
theorem relTriple_runRaw_simulateQ_ordinaryRomImpl
    [Inhabited alpha]
    (computation : OracleComp OracleWorld alpha)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache) (fuel : Nat) :
    RelTriple
      (LazyRevealProbe.runRaw state fuel
        ((simulateQ ordinaryRomImpl computation).run cache))
      ((simulateQ romImpl computation).run (ordinaryQueryCache cache))
      (RawOrdinaryResultRelAt (alpha := alpha) state fuel) := by
  induction computation using OracleComp.inductionOn generalizing state cache fuel with
  | pure value =>
      simp [LazyRevealProbe.runRaw, RawOrdinaryResultRelAt]
  | query_bind query next ih =>
      rw [simulateQ_query_bind, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        simulateQ_query_bind, StateT.run_bind]
      have hquery : RelTriple
          (LazyRevealProbe.runRaw state fuel ((ordinaryRomImpl query).run cache))
          ((romImpl query).run (ordinaryQueryCache cache))
          (RawOrdinaryResultRelAt state fuel) := by
        cases query with
        | inl n =>
            change RelTriple
              (LazyRevealProbe.runRaw state fuel ((splitUniformImpl n).run cache))
              ((unifFwdImpl HashSpec n).run (ordinaryQueryCache cache))
              (RawOrdinaryResultRelAt state fuel)
            rw [show (unifFwdImpl HashSpec n).run (ordinaryQueryCache cache) =
                (fun output => (output, ordinaryQueryCache cache)) <$>
                  (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) by
              simpa using unifFwdImpl.simulateQ_run
                (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))
                (ordinaryQueryCache cache)]
            simpa [map_eq_bind_pure_comp] using
              relTriple_runRaw_splitUniformImpl n state cache fuel
        | inr input =>
            simpa [ordinaryRomImpl, romImpl] using
              relTriple_runRaw_simulateQ_ordinaryHashImpl_at
                (liftM (HashSpec.query input)) state cache fuel
      apply relTriple_bind hquery
      intro rawResult ordinaryResult hrelation
      cases rawResult with
      | stopped hit => simp [RawOrdinaryResultRelAt] at hrelation
      | done finalState remaining valueCache =>
          rcases valueCache with ⟨value, finalCache⟩
          rcases hrelation with ⟨rfl, rfl, rfl⟩
          exact ih value finalState finalCache remaining

end SphincsSecurity.Concrete.OtsProbeSimulation

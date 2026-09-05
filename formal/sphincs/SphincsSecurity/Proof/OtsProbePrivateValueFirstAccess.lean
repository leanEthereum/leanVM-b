import SphincsSecurity.Proof.OtsProbePrivateValueCut

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def IsPrivatePositionAccess (target : Position) : LazyRevealProbe.Query Coordinate → Prop
  | .reveal coordinate | .publish coordinate | .probe coordinate _ => coordinate = .position target
  | _ => False

noncomputable def privatePositionAccessCut
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    OracleComp (LazyRevealProbe.World Coordinate) (PrivateValueCut α) :=
  OracleComp.construct (fun value => pure (.done value))
    (fun input next recursivelyCut =>
      if IsPrivatePositionAccess target input then pure (.query input next)
      else (liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= recursivelyCut) computation

theorem privatePositionAccessCut_query_bind
    (target : Position) (input : LazyRevealProbe.Query Coordinate)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α) :
    privatePositionAccessCut target ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next) =
      (if IsPrivatePositionAccess target input then pure (.query input next)
      else (liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>=
        fun output => privatePositionAccessCut target (next output)) := rfl

theorem privatePositionAccessCut_resume
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    privatePositionAccessCut target computation >>= PrivateValueCut.resume = computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rw [privatePositionAccessCut_query_bind]
      split_ifs
      · rfl
      · rw [bind_assoc]
        exact bind_congr ih

theorem privatePositionAccessCut_no_access
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    (privatePositionAccessCut target computation).IsQueryBoundP (IsPrivatePositionAccess target) 0 := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [privatePositionAccessCut]
  | query_bind input next ih =>
      rw [privatePositionAccessCut_query_bind]
      split_ifs with hinput
      · simp
      · rw [OracleComp.isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl hinput, fun output => by simpa only [if_neg hinput] using ih output⟩

theorem privatePositionAccessCut_no_exposure
    (target : Position) (before after : HashOutput) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    (privatePositionAccessCut target computation).IsQueryBoundP (IsPrivateValueExposure target before after) 0 := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [privatePositionAccessCut]
  | query_bind input next ih =>
      rw [privatePositionAccessCut_query_bind]
      split_ifs with hinput
      · simp
      · have hsafe : ¬IsPrivateValueExposure target before after input := by
          cases input <;> simp_all [IsPrivatePositionAccess, IsPrivateValueExposure]
        rw [OracleComp.isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl hsafe, fun output => by simpa only [if_neg hsafe] using ih output⟩

def privatePositionAccessCandidate (target : Position) : Option (PrivateValueCut α) → Option Digest
  | some (.query (.probe coordinate digest) _) => if coordinate = .position target then some digest else none
  | _ => none

noncomputable def privatePositionFirstCandidate
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (output : HashOutput) : ProbComp (Option Digest) :=
  (fun result => (privatePositionAccessCandidate target (result.map ResolvedRunResult.value)).filter
      (fun digest => digest ∉ context.state.pendingAt (.position target))) <$>
    runResolvedFromTable (replacePrivatePosition target output context) fuel table (privatePositionAccessCut target computation)

theorem privatePositionFirstCandidate_fresh
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (output : HashOutput) (digest : Digest)
    (hresult : some digest ∈ support (privatePositionFirstCandidate target computation context fuel table output)) :
    digest ∉ context.state.pendingAt (.position target) := by
  unfold privatePositionFirstCandidate at hresult
  rw [support_map, Set.mem_image] at hresult
  obtain ⟨result, _, hresult⟩ := hresult
  cases hcandidate : privatePositionAccessCandidate target (result.map ResolvedRunResult.value) with
  | none => simp [hcandidate] at hresult
  | some candidate =>
      simp [hcandidate] at hresult
      exact hresult.2

theorem evalDist_privatePositionFirstCandidate_eq
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (before after : HashOutput)
    (hstate : context.state.values (.position target) = none)
    (hbefore : ¬context.state.hitAt (.position target) before)
    (hafter : ¬context.state.hitAt (.position target) after) :
    evalDist (privatePositionFirstCandidate target computation context fuel table before) =
      evalDist (privatePositionFirstCandidate target computation context fuel table after) := by
  have hreplaceable : PrivatePositionReplaceable target before after (replacePrivatePosition target before context) :=
    ⟨hstate, by simp [replacePrivatePosition, DeferredStructuralValues.install], hbefore, hafter⟩
  have hreplace := evalDist_runResolved_replacePrivatePosition target before after
    (privatePositionAccessCut target computation) (replacePrivatePosition target before context) fuel table hreplaceable
    (privatePositionAccessCut_no_exposure target before after computation)
  have hdist : evalDist (runResolvedFromTable (replacePrivatePosition target after context) fuel table
      (privatePositionAccessCut target computation)) =
      evalDist (Option.map (replacePrivateRunResult target after) <$>
        runResolvedFromTable (replacePrivatePosition target before context) fuel table
          (privatePositionAccessCut target computation)) := by
    simpa [replacePrivatePosition, DeferredStructuralValues.install] using hreplace
  unfold privatePositionFirstCandidate
  rw [evalDist_map, evalDist_map, hdist, evalDist_map, Functor.map_map]
  congr 1
  funext result
  cases result <;> rfl

noncomputable def sampledPrivatePositionFirstCandidate
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) : ProbComp (HashOutput × Option Digest) := do
  let output ← LazyRevealProbe.sampleHashOutput
  if context.state.hitAt (.position target) output then pure (output, none)
  else
    let candidate ← privatePositionFirstCandidate target computation context fuel table output
    pure (output, candidate)

end SphincsSecurity.Concrete.OtsProbeSimulation

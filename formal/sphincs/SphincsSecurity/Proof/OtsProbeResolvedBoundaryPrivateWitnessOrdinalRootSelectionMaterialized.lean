import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootSelectionMaterialize

/-!
# Materialized root-avoiding ordinal prefix

The auxiliary prefix executes against the already materialized shadow but derives every planned
candidate from its canonical public view. Before the selected ordinal it stops if a candidate
guesses either distinguished root. On the surviving branch every direct query satisfies the cache
quotient's safe-input premise.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

noncomputable def materializedCanonicalContext
    (table : OtsSecretIndex → HashOutput)
    (state : LazyRevealProbe.State Coordinate) : DeferredContext :=
  canonicalizeMaterializedValues table (directDeferredContext state)

theorem materializedCanonicalContext_state_eq_of_rootHidden
    {target : Position} {leftOutput rightOutput : HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hrel : RootHiddenStateRel target leftOutput rightOutput left right)
    (table : OtsSecretIndex → HashOutput) :
    (materializedCanonicalContext table left).state =
      (materializedCanonicalContext table right).state := by
  exact (hrel.directContext.canonicalize table).state

noncomputable def finishMaterializedPrivateOrdinalSelection
    (observe : LazyRevealProbe.State Coordinate → Nat → α → SplitHashCache →
      List Probe → ProbComp (Option Probe))
    (candidates : List Probe) :
    Option (CleanRunResult (α × SplitHashCache)) → ProbComp (Option Probe)
  | none => pure none
  | some result =>
      observe result.state result.remaining result.value.1 result.value.2 candidates

noncomputable def continueMaterializedPrivateOrdinalSelection
    (target : Position)
    (observe : LazyRevealProbe.State Coordinate → Nat → α → SplitHashCache →
      List Probe → ProbComp (Option Probe))
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (value : α) (cache : SplitHashCache) (candidates : List Probe) :
    ProbComp (Option Probe) :=
  if Coordinate.position target ∈ state.revealed then pure none
  else observe state fuel value cache candidates

noncomputable def materializedRootAvoidingOrdinalSelection
    (ordinal : Nat) (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest)
    (signer : Message → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) (Option Signature))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ProbComp (Option Probe) := by
  classical
  exact OracleComp.construct
    (C := fun _ : OracleComp (OracleWorld + SigningSpec) α =>
      List Probe → LazyRevealProbe.State Coordinate → Nat →
        (OtsSecretIndex → HashOutput) → SplitHashCache → ProbComp (Option Probe))
    (fun _value candidates state _fuel _table _cache =>
      if hselected : ordinal < candidates.length then
        pure (some (candidates.get ⟨ordinal, hselected⟩))
      else pure none)
    (fun query _next recursivelyRun candidates state fuel table cache =>
      if hselected : ordinal < candidates.length then
        pure (some (candidates.get ⟨ordinal, hselected⟩))
      else
        match query with
        | .inl (.inl n) =>
            runCleanFromTable state fuel table ((splitUniformImpl n).run cache) >>=
              finishMaterializedPrivateOrdinalSelection
                (continueMaterializedPrivateOrdinalSelection target
                  (fun nextState remaining value nextCache laterCandidates =>
                    recursivelyRun value laterCandidates nextState remaining table nextCache))
                candidates
        | .inl (.inr input) =>
            let publicContext := materializedCanonicalContext table state
            let plan := purePlanProbingHashQuery parameter input publicContext.state
            let candidate? := rootAwareCandidateForPlan? parameter input plan
            let nextCandidates := appendPlannedCandidate candidates candidate?
            if hnextSelected : ordinal < nextCandidates.length then
              pure (some (nextCandidates.get ⟨ordinal, hnextSelected⟩))
            else if RootAwareCandidateAvoidsRoots target leftRoot rightRoot candidate? then
              runCleanFromTable state fuel table
                  ((probingHashQueryAfterPlan parameter input plan).run cache) >>=
                finishMaterializedPrivateOrdinalSelection
                  (continueMaterializedPrivateOrdinalSelection target
                    (fun nextState remaining value nextCache laterCandidates =>
                      recursivelyRun value laterCandidates nextState remaining table nextCache))
                  nextCandidates
            else pure none
        | .inr message =>
            runCleanFromTable state fuel table ((signer message).run cache) >>=
              finishMaterializedPrivateOrdinalSelection
                (continueMaterializedPrivateOrdinalSelection target
                  (fun nextState remaining value nextCache laterCandidates =>
                    recursivelyRun value laterCandidates nextState remaining table nextCache))
                candidates)
    computation candidates state fuel table cache

noncomputable def materializedActualRootAvoidingOrdinalSelection
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ProbComp (Option Probe) :=
  materializedRootAvoidingOrdinalSelection ordinal parameter target leftRoot rightRoot
    (maskedSign parameter publicRoot ftsSecret) computation candidates state fuel table cache

noncomputable def materializedComparisonRootAvoidingOrdinalSelection
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (leftOutput rightOutput : HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ProbComp (Option Probe) :=
  materializedRootAvoidingOrdinalSelection ordinal parameter target
    (truncateHash leftOutput) (truncateHash rightOutput)
    (maskedSignWithTargetComparison parameter publicRoot target (truncateHash rightOutput)
      ftsSecret)
    computation candidates state fuel table cache

end SphincsSecurity.Concrete.OtsProbeSimulation

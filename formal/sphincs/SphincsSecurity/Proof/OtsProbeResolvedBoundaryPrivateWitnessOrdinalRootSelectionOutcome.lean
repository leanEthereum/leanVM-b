import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootSelectionDeferred
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryOrdinaryAdaptive

/-!
# Materialized selection outcome

The materialized prefix retains stopped and non-completable executions as one explicit failure
marker. Clean executions return the selected candidate, if the fixed ordinal was reached. This is
the codomain used by the one-sided adaptive bridge.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

inductive MaterializedSelectionOutcome where
  | failed
  | finished (selection : Option Probe)
deriving DecidableEq

def MaterializedSelectionOutcome.toOption : MaterializedSelectionOutcome → Option Probe
  | .failed => none
  | .finished selection => selection

def MaterializedSelectionOutcome.isFailure : MaterializedSelectionOutcome → Prop
  | .failed => True
  | .finished _ => False

def MaterializedSelectionOutcome.Matches
    (target : Position) (root : Digest) : MaterializedSelectionOutcome → Prop
  | .failed => False
  | .finished selection => materializedOrdinalSelectionMatches target root selection

def RootSelectionBridgeRel
    (target : Position) (leftOutput : HashOutput)
    (rightRoot : Digest) (ordinal : Nat) :
    Option PrivateOrdinalSelection → MaterializedSelectionOutcome → Prop :=
  fun left right =>
    privateOrdinalSelectionGoodForRoots target leftOutput rightRoot ordinal left →
      right.isFailure ∨ right.Matches target (truncateHash leftOutput)

theorem rootSelectionBridgeRel_none_left
    (target : Position) (leftOutput : HashOutput)
    (rightRoot : Digest) (ordinal : Nat)
    (right : MaterializedSelectionOutcome) :
    RootSelectionBridgeRel target leftOutput rightRoot ordinal none right := by
  intro hgood
  exact False.elim hgood

theorem rootSelectionBridgeRel_failed_right
    (target : Position) (leftOutput : HashOutput)
    (rightRoot : Digest) (ordinal : Nat)
    (left : Option PrivateOrdinalSelection) :
    RootSelectionBridgeRel target leftOutput rightRoot ordinal left .failed := by
  intro _hgood
  exact Or.inl trivial

theorem relTriple_pure_none_rootSelectionBridge
    (target : Position) (leftOutput : HashOutput)
    (rightRoot : Digest) (ordinal : Nat)
    (right : ProbComp MaterializedSelectionOutcome) :
    RelTriple (pure none : ProbComp (Option PrivateOrdinalSelection)) right
      (RootSelectionBridgeRel target leftOutput rightRoot ordinal) := by
  have hbase := relTriple_true
    (pure none : ProbComp (Option PrivateOrdinalSelection)) right
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun value => value = none) (by
        intro value hvalue
        simpa using hvalue)
  apply relTriple_post_mono hsupported
  intro leftValue rightValue hrelation
  rw [hrelation.2]
  exact rootSelectionBridgeRel_none_left target leftOutput rightRoot ordinal rightValue

theorem relTriple_any_failed_rootSelectionBridge
    (target : Position) (leftOutput : HashOutput)
    (rightRoot : Digest) (ordinal : Nat)
    (left : ProbComp (Option PrivateOrdinalSelection)) :
    RelTriple left (pure .failed : ProbComp MaterializedSelectionOutcome)
      (RootSelectionBridgeRel target leftOutput rightRoot ordinal) := by
  have hbase := relTriple_true left
    (pure .failed : ProbComp MaterializedSelectionOutcome)
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hbase
  apply relTriple_post_mono hsupported
  intro leftValue rightValue hrelation
  have hright : rightValue = .failed := by simpa using hrelation.2
  subst rightValue
  exact rootSelectionBridgeRel_failed_right target leftOutput rightRoot ordinal leftValue

noncomputable def guardPrivateOrdinalSelection
    (target : Position)
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp (Option PrivateOrdinalSelection))
    (context : DeferredContext) (fuel : Nat) (value : α) (candidates : List Probe) :
    ProbComp (Option PrivateOrdinalSelection) :=
  if Coordinate.position target ∈ context.state.revealed then pure none
  else observe context fuel value candidates

noncomputable def finishMaterializedSelectionOutcome
    (target : Position) (table : OtsSecretIndex → HashOutput)
    (observe : LazyRevealProbe.State Coordinate → Nat → α → SplitHashCache →
      List Probe → ProbComp MaterializedSelectionOutcome)
    (candidates : List Probe) :
    DirectDetailedResult (α × SplitHashCache) → ProbComp MaterializedSelectionOutcome := by
  classical
  exact fun result => match result with
    | .stopped _ => pure .failed
    | .done result =>
        if DeferredCompletable table (directDeferredContext result.context.state) then
          if Coordinate.position target ∈ result.context.state.revealed then
            pure .failed
          else observe result.context.state result.remaining result.value.1 result.value.2 candidates
        else pure .failed

set_option maxRecDepth 100000 in
theorem relTriple_finishRootSelectionBridge
    (target : Position) (leftOutput : HashOutput) (rightRoot : Digest)
    (ordinal : Nat) (table : OtsSecretIndex → HashOutput)
    (leftObserve : DeferredContext → Nat → (α × SplitHashCache) → List Probe →
      ProbComp (Option PrivateOrdinalSelection))
    (rightObserve : LazyRevealProbe.State Coordinate → Nat → α → SplitHashCache →
      List Probe → ProbComp MaterializedSelectionOutcome)
    (candidates : List Probe)
    (leftResult rightResult : DirectDetailedResult (α × SplitHashCache))
    (hrelation : DirectDetailedOrdinaryStableRunEq table leftResult rightResult)
    (hrecursive : ∀ left right,
      OrdinaryMaterializedRunEq table left right →
      RelTriple
        (leftObserve left.context left.remaining left.value candidates)
        (rightObserve right.context.state right.remaining right.value.1 right.value.2 candidates)
        (RootSelectionBridgeRel target leftOutput rightRoot ordinal)) :
    RelTriple
      (finishDirectDetailedPrivateOrdinalSelection
        (canonicalizeDirectPrivateOrdinalSelection table leftObserve) candidates leftResult)
      (finishMaterializedSelectionOutcome target table rightObserve candidates rightResult)
      (RootSelectionBridgeRel target leftOutput rightRoot ordinal) := by
  cases leftResult with
  | stopped leftReason =>
      exact relTriple_pure_none_rootSelectionBridge target leftOutput rightRoot ordinal _
  | done left =>
      cases rightResult with
      | stopped rightReason =>
          exact relTriple_any_failed_rootSelectionBridge target leftOutput rightRoot ordinal _
      | done right =>
          rcases hrelation with hclean | hdoomed
          · have hcanonical := hclean.canonicalize_left
            let canonical := canonicalizeMaterializedValues table left.context
            have hleftCompletable : DeferredCompletable table canonical :=
              hcanonical.context_le.leftCompletable
            have hnotPrivate : ¬PrivateStructuralHit canonical :=
              not_privateStructuralHit_of_deferredCompletable hleftCompletable
            have hrightCompletable :
                DeferredCompletable table (directDeferredContext right.context.state) := by
              rw [← hclean.right_materialized]
              exact hclean.context_le.rightCompletable
            unfold finishDirectDetailedPrivateOrdinalSelection
              finishMaterializedSelectionOutcome
            unfold canonicalizeDirectPrivateOrdinalSelection
            simp only [canonical, hnotPrivate, ↓reduceIte, hclean.left_published, ↓reduceIte,
              hleftCompletable, hrightCompletable]
            have hrevealed : canonical.state.revealed = right.context.state.revealed := by
              exact hcanonical.revealed_eq
            by_cases htargetRevealed : Coordinate.position target ∈ canonical.state.revealed
            · have hrightRevealed :
                  Coordinate.position target ∈ right.context.state.revealed := by
                rw [← hrevealed]
                exact htargetRevealed
              simp only [hrightRevealed, ↓reduceIte]
              exact relTriple_any_failed_rootSelectionBridge target leftOutput rightRoot ordinal _
            · have hrightRevealed :
                  Coordinate.position target ∉ right.context.state.revealed := by
                intro hmem
                exact htargetRevealed (by rwa [hrevealed])
              simp only [hrightRevealed, ↓reduceIte]
              exact hrecursive
                { left with context := canonical } right hcanonical
          · unfold finishMaterializedSelectionOutcome
            have hnotCompletable :
                ¬DeferredCompletable table (directDeferredContext right.context.state) := by
              rw [← hdoomed.2]
              exact hdoomed.1.2.2.2
            simp only [hnotCompletable, ↓reduceIte]
            exact relTriple_any_failed_rootSelectionBridge target leftOutput rightRoot ordinal _

noncomputable def materializedRootAvoidingOrdinalSelectionOutcome
    (ordinal : Nat) (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest)
    (signer : Message → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) (Option Signature))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ProbComp MaterializedSelectionOutcome := by
  classical
  exact OracleComp.construct
    (C := fun _ : OracleComp (OracleWorld + SigningSpec) α =>
      List Probe → LazyRevealProbe.State Coordinate → Nat →
        (OtsSecretIndex → HashOutput) → SplitHashCache →
          ProbComp MaterializedSelectionOutcome)
    (fun _value candidates _state _fuel _table _cache =>
      if hselected : ordinal < candidates.length then
        pure (.finished (some (candidates.get ⟨ordinal, hselected⟩)))
      else pure (.finished none))
    (fun query _next recursivelyRun candidates state fuel table cache =>
      if hselected : ordinal < candidates.length then
        pure (.finished (some (candidates.get ⟨ordinal, hselected⟩)))
      else
        match query with
        | .inl (.inl n) =>
            runDirectResolvedDetailedFromTable (directDeferredContext state) fuel table
                ((splitUniformImpl n).run cache) >>=
              finishMaterializedSelectionOutcome target table
                (fun nextState remaining value nextCache laterCandidates =>
                  recursivelyRun value laterCandidates nextState remaining table nextCache)
                candidates
        | .inl (.inr input) =>
            let publicContext := materializedCanonicalContext table state
            let plan := purePlanProbingHashQuery parameter input publicContext.state
            let candidate? := rootAwareCandidateForPlan? parameter input plan
            let nextCandidates := appendPlannedCandidate candidates candidate?
            if hnextSelected : ordinal < nextCandidates.length then
              pure (.finished (some (nextCandidates.get ⟨ordinal, hnextSelected⟩)))
            else if RootSafePlannedHash target leftRoot rightRoot plan candidate? then
              runDirectResolvedDetailedFromTable (directDeferredContext state) fuel table
                  ((probingHashQueryAfterPublicPlan parameter input publicContext.state plan).run
                    cache) >>=
                finishMaterializedSelectionOutcome target table
                  (fun nextState remaining value nextCache laterCandidates =>
                    recursivelyRun value laterCandidates nextState remaining table nextCache)
                  nextCandidates
            else pure (.finished none)
        | .inr message =>
            runDirectResolvedDetailedFromTable (directDeferredContext state) fuel table
                ((signer message).run cache) >>=
              finishMaterializedSelectionOutcome target table
                (fun nextState remaining value nextCache laterCandidates =>
                  recursivelyRun value laterCandidates nextState remaining table nextCache)
                candidates)
    computation candidates state fuel table cache

noncomputable def materializedActualRootAvoidingOrdinalSelectionOutcome
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ProbComp MaterializedSelectionOutcome :=
  materializedRootAvoidingOrdinalSelectionOutcome ordinal parameter target leftRoot rightRoot
    (maskedSign parameter publicRoot ftsSecret) computation candidates state fuel table cache

end SphincsSecurity.Concrete.OtsProbeSimulation

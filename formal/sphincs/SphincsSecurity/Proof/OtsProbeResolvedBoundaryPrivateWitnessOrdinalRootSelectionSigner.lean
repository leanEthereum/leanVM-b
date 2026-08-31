import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootSelection

/-!
# Swapped-root signer continuations

The concrete signer comparison is a two-stage coupling through the target-aware signer. This
module retains an arbitrary continuation after each stage, so the normalized ordinal prefix can
continue with its related canonical deferred contexts instead of projecting the signer state away.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

theorem evalDist_bind_eq_of_relTriple_next
    (left : ProbComp α) (right : ProbComp β) (relation : α → β → Prop)
    (leftNext : α → ProbComp γ) (rightNext : β → ProbComp γ)
    (hrel : RelTriple left right relation)
    (hnext : ∀ leftValue rightValue, relation leftValue rightValue →
      evalDist (leftNext leftValue) = evalDist (rightNext rightValue)) :
    evalDist (left >>= leftNext) = evalDist (right >>= rightNext) := by
  apply evalDist_eq_of_relTriple_eqRel
  apply relTriple_bind hrel
  intro leftValue rightValue hvalue
  exact relTriple_eqRel_of_evalDist_eq (hnext leftValue rightValue hvalue)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem evalDist_swappedRoot_maskedSign_bind_eq
    (parameter : PublicParameter) (publicRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (leftOutput rightOutput : HashOutput)
    (leftContext rightContext : DeferredContext)
    (hcontext : RootMaterializedContextRel target leftOutput rightOutput
      leftContext rightContext)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (leftCache rightCache : SplitHashCache)
    (hcache : RootDeferredCacheRel parameter target leftOutput rightOutput
      leftCache rightCache)
    (message : Message)
    (leftObserve middleObserve rightObserve :
      Option (CleanRunResult (Option Signature × SplitHashCache)) → ProbComp α)
    (hleftMiddle : ∀ leftResult middleResult,
      RootEncodingStoredCleanSameRel parameter target (truncateHash leftOutput)
          (truncateHash rightOutput) leftResult middleResult →
        evalDist (leftObserve leftResult) = evalDist (middleObserve middleResult))
    (hmiddleRight : ∀ middleResult rightResult,
      RootHiddenCleanSameRel target leftOutput rightOutput middleResult rightResult →
        evalDist (middleObserve middleResult) = evalDist (rightObserve rightResult)) :
    evalDist
        (runCleanFromTable leftContext.state fuel table
            ((maskedSign parameter publicRoot ftsSecret message).run leftCache) >>=
          leftObserve) =
      evalDist
        (runCleanFromTable rightContext.state fuel table
            ((maskedSign parameter publicRoot ftsSecret message).run rightCache) >>=
          rightObserve) := by
  obtain ⟨middleCache, hencoding, hhidden⟩ := hcache
  have hstored : StoredLayerRoot leftContext.state target (truncateHash leftOutput) :=
    ⟨leftOutput, hcontext.state.left_target, rfl⟩
  let middleRun := runCleanFromTable leftContext.state fuel table
    ((maskedSignWithTargetComparison parameter publicRoot target (truncateHash rightOutput)
      ftsSecret message).run middleCache)
  have hab := rootEncodingCacheRelatesStored_maskedSign_targetComparison parameter publicRoot
    target hroot (truncateHash leftOutput) (truncateHash rightOutput) ftsSecret message
    leftCache middleCache hencoding leftContext.state fuel table hstored
  have hbc := rootHiddenRelates_maskedSignWithTargetComparison_actual parameter publicRoot
    ftsSecret target hroot leftOutput rightOutput message leftContext.state rightContext.state
    hcontext.state fuel table middleCache rightCache hhidden
  calc
    _ = evalDist (middleRun >>= middleObserve) :=
      evalDist_bind_eq_of_relTriple_next _ _ _ leftObserve middleObserve hab hleftMiddle
    _ = _ :=
      evalDist_bind_eq_of_relTriple_next _ _ _ middleObserve rightObserve hbc hmiddleRight

end SphincsSecurity.Concrete.OtsProbeSimulation

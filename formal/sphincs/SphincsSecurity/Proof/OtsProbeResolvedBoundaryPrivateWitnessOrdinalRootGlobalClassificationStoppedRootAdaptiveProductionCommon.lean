import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveProductionNormalizeLift

/-!
# Common root production observer

The common selector keeps the selected structural position observable while a distinguished
position remains lazily sampled. Its split cache is completed at that position exactly when the
deferred context already contains the corresponding output.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable

noncomputable def installDeferredPositionCache
    (target : Position) (context : DeferredContext) (cache : SplitHashCache) : SplitHashCache :=
  match context.positionValue target with
  | none => cache
  | some output => replaceHiddenRootCache target output cache

noncomputable def permissiveRootAwarePositionComplement
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (target : Position)
    (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) : ProbComp Bool := do
  let selection ← permissiveRootAwareOrdinalSelection ordinal parameter root ftsSecret
    computation candidates (materializedDeferredState context) fuel table
    (installDeferredPositionCache target context cache)
  pure (decide (¬materializedOrdinalSelectionAt target selection))

theorem installDeferredPositionCache_eq_of_positionValue_eq
    (target : Position) (left right : DeferredContext) (cache : SplitHashCache)
    (hvalue : left.positionValue target = right.positionValue target) :
    installDeferredPositionCache target left cache =
      installDeferredPositionCache target right cache := by
  unfold installDeferredPositionCache
  rw [hvalue]

theorem permissiveStateRel_materializedDeferredState_of_finalizationContextEq
    (table : OtsSecretIndex → HashOutput) (left right : DeferredContext)
    (hcontext : FinalizationContextEq table (some left) (some right))
    (hvalues : left.state.values = right.state.values)
    (hrevealed : left.state.revealed = right.state.revealed) :
    PermissiveStateRel (materializedDeferredState left)
      (materializedDeferredState right) := by
  exact ⟨materializedDeferredState_values_eq_of_finalizationContextEq table left right
    hcontext hvalues, by simpa using hrevealed⟩

theorem positionValue_eq_of_finalizationContextEq
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (left right : DeferredContext)
    (hcontext : FinalizationContextEq table (some left) (some right)) :
    left.positionValue target = right.positionValue target := by
  have hvalue := congrFun hcontext.1.valueEq (Coordinate.position target)
  simpa [resolvedCompletionValue] using hvalue

instance permissiveRootAwarePositionComplement_observerSynchronized
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (target : Position)
    (table : OtsSecretIndex → HashOutput) :
    ObserverSynchronized table
      (permissiveRootAwarePositionComplement ordinal parameter root ftsSecret computation
        candidates target table) where
  eq_of_synchronized left right fuel cache hcontext hvalues hrevealed := by
    have hstate :=
      permissiveStateRel_materializedDeferredState_of_finalizationContextEq table left right
        hcontext hvalues hrevealed
    have hcache := installDeferredPositionCache_eq_of_positionValue_eq target left right cache
      (positionValue_eq_of_finalizationContextEq table target left right hcontext)
    unfold permissiveRootAwarePositionComplement
    rw [hcache]
    apply evalDist_bind_eq_of_evalDist_eq
    exact evalDist_eq_of_relTriple_eqRel
      (relTriple_permissiveRootAwareOrdinalSelection_of_stateRel_aux ordinal parameter root
        ftsSecret computation candidates candidates (materializedDeferredState left)
        (materializedDeferredState right) fuel table
        (installDeferredPositionCache target right cache) rfl hstate)

end SphincsSecurity.Concrete.OtsProbeSimulation

import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalSourceDelayedRootSwapProbability

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

noncomputable def delayedRootGuessAfterInitialResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    Option (CleanRunResult (Digest × SplitHashCache)) →
      ProbComp (Option PermissivePrivateOrdinalSelection × Digest)
  | none => do
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      pure (none, rightRoot)
  | some rootResult => do
      let selection ← delayedPermissiveDetailedSelectionAfterRootResult ordinal adversary
        parameter ftsSecret rootResult
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      pure (selection, rightRoot)

noncomputable def installedDelayedSelectionAfterInitialResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (target : Position) :
    Option (CleanRunResult (Digest × SplitHashCache)) →
      ProbComp (Option PermissivePrivateOrdinalSelection)
  | none => pure none
  | some rootResult =>
      installedDelayedPermissiveDetailedSelectionAfterRootResult ordinal adversary parameter
        ftsSecret target rootResult

set_option maxRecDepth 100000 in
theorem probEvent_delayedRootGuess_afterInitialResult_le_installed_mul
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (result : Option (CleanRunResult (Digest × SplitHashCache)))
    (habsent : InitialRootOptionFacts target result)
    (hswap : InitialRootSwapFacts parameter target result) :
    Pr[fun result : Option PermissivePrivateOrdinalSelection × Digest =>
        PermissiveDelayedRootGuess target result.2 ordinal result.1 |
      delayedRootGuessAfterInitialResult ordinal adversary parameter ftsSecret result] ≤
      Pr[fun selection =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target |
        installedDelayedSelectionAfterInitialResult ordinal adversary parameter ftsSecret target
          result] * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  cases result with
  | none =>
      simp [delayedRootGuessAfterInitialResult, installedDelayedSelectionAfterInitialResult,
        PermissiveDelayedRootGuess, PermissiveDelayedRootGuessAt,
        permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition?]
  | some rootResult =>
      change rootResult.state.values (.position target) = none ∧
          Coordinate.position target ∉ rootResult.state.revealed ∧
          rootResult.state.pending = ∅ at habsent
      change ∀ leftRoot rightRoot,
          swapCanonicalRootEncodingCache parameter target leftRoot rightRoot rootResult.value.2 =
            rootResult.value.2 at hswap
      exact probEvent_delayedRootGuess_afterRootResult_le_installed_mul ordinal adversary parameter
        ftsSecret target hroot rootResult habsent.1 habsent.2.1 hswap

set_option maxRecDepth 100000 in
theorem evalDist_delayedRootGuess_afterTable_eq_initial_bind
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    evalDist (do
      let selection ← delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary
        parameter ftsSecret fuel table
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      pure (selection, rightRoot)) =
      evalDist (rootAwareProductionInitialRun fuel table >>=
        delayedRootGuessAfterInitialResult ordinal adversary parameter ftsSecret) := by
  unfold delayedPermissiveDetailedSelectionExperimentAfterTable
    delayedRootGuessAfterInitialResult delayedPermissiveDetailedSelectionAfterRootResult
  simp only [bind_assoc]
  apply evalDist_bind_congr
  intro result
  cases result <;> intro _ <;> rfl

theorem probEvent_bind_le_bind_mul_of_forall_of_invariant
    (first : ProbComp ι) (left : ι → ProbComp α) (right : ι → ProbComp β)
    (event : α → Prop) (gate : β → Prop) (epsilon : ENNReal)
    (invariant : ι → Prop)
    (hinvariant : ∀ index ∈ support first, invariant index)
    (hbound : ∀ index, invariant index →
      Pr[event | left index] ≤ Pr[gate | right index] * epsilon) :
    Pr[event | first >>= left] ≤ Pr[gate | first >>= right] * epsilon :=
  probEvent_bind_le_bind_mul_of_forall first left right event gate epsilon
    (fun index hindex => hbound index (hinvariant index hindex))

set_option maxRecDepth 100000 in
theorem probEvent_initial_bind_delayedRootGuess_le_installed_mul
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    Pr[fun result : Option PermissivePrivateOrdinalSelection × Digest =>
        PermissiveDelayedRootGuess target result.2 ordinal result.1 |
      rootAwareProductionInitialRun fuel table >>=
        delayedRootGuessAfterInitialResult ordinal adversary parameter ftsSecret] ≤
      Pr[fun selection =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target |
        rootAwareProductionInitialRun fuel table >>=
          installedDelayedSelectionAfterInitialResult ordinal adversary parameter ftsSecret target] *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  exact probEvent_bind_le_bind_mul_of_forall_of_invariant
    (first := rootAwareProductionInitialRun fuel table)
    (left := delayedRootGuessAfterInitialResult ordinal adversary parameter ftsSecret)
    (right := installedDelayedSelectionAfterInitialResult ordinal adversary parameter ftsSecret
      target)
    (event := fun result : Option PermissivePrivateOrdinalSelection × Digest =>
      PermissiveDelayedRootGuess target result.2 ordinal result.1)
    (gate := fun selection =>
      permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target)
    (epsilon := ((2 ^ digestBits : Nat) : ENNReal)⁻¹)
    (invariant := InitialRootAllFacts parameter target)
    (initialRootAllFacts_of_mem parameter target hroot hparent fuel table)
    (fun result hfacts =>
      probEvent_delayedRootGuess_afterInitialResult_le_installed_mul ordinal adversary parameter
        ftsSecret target hroot result hfacts.1 hfacts.2)

set_option maxRecDepth 100000 in
theorem probEvent_delayedRootGuess_afterTable_le_installed_mul
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    Pr[fun result : Option PermissivePrivateOrdinalSelection × Digest =>
        PermissiveDelayedRootGuess target result.2 ordinal result.1 | do
      let selection ← delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary
        parameter ftsSecret fuel table
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      pure (selection, rightRoot)] ≤
      Pr[fun selection =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target |
        installedDelayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
          ftsSecret target fuel table] * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  calc
    _ = Pr[fun result : Option PermissivePrivateOrdinalSelection × Digest =>
          PermissiveDelayedRootGuess target result.2 ordinal result.1 |
        rootAwareProductionInitialRun fuel table >>=
          delayedRootGuessAfterInitialResult ordinal adversary parameter ftsSecret] := by
      apply OracleComp.probEvent_congr' (fun _ _ => Iff.rfl)
      exact evalDist_delayedRootGuess_afterTable_eq_initial_bind ordinal adversary parameter
        ftsSecret fuel table
    _ ≤ Pr[fun selection =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target |
        rootAwareProductionInitialRun fuel table >>=
          installedDelayedSelectionAfterInitialResult ordinal adversary parameter ftsSecret target] *
          ((2 ^ digestBits : Nat) : ENNReal)⁻¹ :=
      probEvent_initial_bind_delayedRootGuess_le_installed_mul ordinal adversary parameter
        ftsSecret target hroot hparent fuel table
    _ = _ := by
      rfl

set_option maxRecDepth 100000 in
theorem probEvent_delayedRootGuess_afterTable_le_common_mul
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    Pr[fun result : Option PermissivePrivateOrdinalSelection × Digest =>
        PermissiveDelayedRootGuess target result.2 ordinal result.1 | do
      let selection ← delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary
        parameter ftsSecret fuel table
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      pure (selection, rightRoot)] ≤
      Pr[fun selection =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target |
        delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
          ftsSecret fuel table] * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  calc
    _ ≤ Pr[fun selection =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target |
        installedDelayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
          ftsSecret target fuel table] * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ :=
      probEvent_delayedRootGuess_afterTable_le_installed_mul ordinal adversary parameter ftsSecret
        target hroot hparent fuel table
    _ ≤ _ := by
      gcongr
      exact probEvent_installedDelayedSelection_fiber_le_common ordinal adversary parameter
        ftsSecret target hroot hparent fuel table

end SphincsSecurity.Concrete.OtsProbeSimulation

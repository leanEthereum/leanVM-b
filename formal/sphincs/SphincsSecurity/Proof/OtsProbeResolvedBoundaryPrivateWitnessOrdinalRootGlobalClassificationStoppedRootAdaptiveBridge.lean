import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootLazyEagerBridge
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootLazyEagerSelected

/-!
# Adaptive selected-root bridge

The comparison root is independent of both executions. This file conditions on it before the
remaining adaptive coupling, leaving the hard prefix theorem with one fewer sampler and no product
wrapper.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

noncomputable def fixedComparisonRootIndicator
    (table : OtsSecretIndex → HashOutput) (ordinal : Nat) (target : Position)
    (root rightRoot : Digest) :
    Option (ObservedCleanRunResult (RetainedRestResult × SplitHashCache)) → Bool :=
  fun observed => successfulObservedRootComparisonIndicator table ordinal target
    (retainObservedRoot root observed, rightRoot)

noncomputable def resolvedEagerObservedRootComparisonAtRoot
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache)) :
    ProbComp (Option (ObservedCleanRunResult (RetainedRestResult × SplitHashCache))) := do
  let resolved ← resolveDeferredPositionValue target (directDeferredContext rootResult.state)
  match resolved with
  | none => pure none
  | some resolved =>
      observedMaterializedBoundary parameter rootResult.value.1 ftsSecret
        (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
        (materializedDeferredState resolved.toDeferredContext) rootResult.remaining rootResult.table
        (replaceHiddenRootCache target resolved.output rootResult.value.2)

set_option maxRecDepth 100000 in
theorem relTriple_indicator_afterRootResult_of_fixedComparisonRoot
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache))
    (hfixed : ∀ rightRoot,
      RelTriple
        (fixedComparisonRootIndicator table ordinal target rootResult.value.1 rightRoot <$>
          observedMaterializedBoundary parameter rootResult.value.1 ftsSecret
            (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
            rootResult.state rootResult.remaining table rootResult.value.2)
        (fixedComparisonRootIndicator table ordinal target rootResult.value.1 rightRoot <$>
          resolvedEagerObservedRootComparisonAtRoot adversary parameter ftsSecret target
            rootResult)
        SuccessfulObservedIndicatorRel) :
    RelTriple
      (successfulObservedRootComparisonIndicator table ordinal target <$> (do
        let observed ← observedMaterializedBoundary parameter rootResult.value.1 ftsSecret
          (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
          rootResult.state rootResult.remaining table rootResult.value.2
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (retainObservedRoot rootResult.value.1 observed, rightRoot)))
      (successfulObservedRootComparisonIndicator table ordinal target <$>
        resolvedEagerObservedRootComparisonAfterRootResult adversary parameter ftsSecret target
          rootResult)
      SuccessfulObservedIndicatorRel := by
  let observed := observedMaterializedBoundary parameter rootResult.value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
    rootResult.state rootResult.remaining table rootResult.value.2
  let comparison := ($ᵗ Digest : ProbComp Digest)
  let leftAtRoot := fun rightRoot =>
    fixedComparisonRootIndicator table ordinal target rootResult.value.1 rightRoot <$> observed
  let rightAtRoot := fun rightRoot =>
    fixedComparisonRootIndicator table ordinal target rootResult.value.1 rightRoot <$>
      resolvedEagerObservedRootComparisonAtRoot adversary parameter ftsSecret target rootResult
  have hconditioned : RelTriple
      (comparison >>= leftAtRoot) (comparison >>= rightAtRoot)
      SuccessfulObservedIndicatorRel := by
    apply relTriple_bind (relTriple_refl comparison)
    intro leftRoot rightRoot hroot
    subst rightRoot
    exact hfixed leftRoot
  have hleft : evalDist
      (successfulObservedRootComparisonIndicator table ordinal target <$> (do
        let observed ← observedMaterializedBoundary parameter rootResult.value.1 ftsSecret
          (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
          rootResult.state rootResult.remaining table rootResult.value.2
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (retainObservedRoot rootResult.value.1 observed, rightRoot))) =
      evalDist (comparison >>= leftAtRoot) := by
    unfold comparison leftAtRoot fixedComparisonRootIndicator
    simp only [map_eq_bind_pure_comp, bind_assoc]
    rw [OracleComp.DeferredSampling.evalDist_bind_comm observed
      ($ᵗ Digest : ProbComp Digest)]
    apply evalDist_bind_congr
    intro rightRoot _hrightRoot
    apply evalDist_bind_congr
    intro result _hresult
    cases result <;> rfl
  have hright : evalDist (comparison >>= rightAtRoot) = evalDist
      (successfulObservedRootComparisonIndicator table ordinal target <$>
        resolvedEagerObservedRootComparisonAfterRootResult adversary parameter ftsSecret target
          rootResult) := by
    let resolver :=
      resolveDeferredPositionValue target (directDeferredContext rootResult.state)
    let continuation : Digest → Option DeferredResolution → ProbComp Bool :=
      fun rightRoot resolved =>
      match resolved with
      | none => pure (fixedComparisonRootIndicator table ordinal target rootResult.value.1
          rightRoot (none : Option
            (ObservedCleanRunResult (RetainedRestResult × SplitHashCache))))
      | some resolved =>
          fixedComparisonRootIndicator table ordinal target rootResult.value.1 rightRoot <$>
            observedMaterializedBoundary parameter rootResult.value.1 ftsSecret
              (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
              (materializedDeferredState resolved.toDeferredContext) rootResult.remaining
              rootResult.table
              (replaceHiddenRootCache target resolved.output rootResult.value.2)
    have hswap := OracleComp.DeferredSampling.evalDist_bind_comm comparison resolver continuation
    have hconditionedRight : evalDist (comparison >>= rightAtRoot) =
        evalDist (comparison >>= fun rightRoot =>
          resolver >>= continuation rightRoot) := by
      apply evalDist_bind_congr
      intro rightRoot _hrightRoot
      unfold rightAtRoot resolvedEagerObservedRootComparisonAtRoot
      simp only [map_eq_bind_pure_comp, bind_assoc]
      apply evalDist_bind_congr
      intro resolved _hresolved
      cases resolved with
      | none => rfl
      | some resolved => rfl
    have horiginalRight :
        evalDist (resolver >>= fun resolved =>
          comparison >>= fun rightRoot => continuation rightRoot resolved) =
        evalDist
          (successfulObservedRootComparisonIndicator table ordinal target <$>
            resolvedEagerObservedRootComparisonAfterRootResult adversary parameter ftsSecret
              target rootResult) := by
      unfold resolver comparison continuation
        resolvedEagerObservedRootComparisonAfterRootResult fixedComparisonRootIndicator
      simp only [map_eq_bind_pure_comp, bind_assoc]
      apply evalDist_bind_congr
      intro resolved _hresolved
      cases resolved with
      | none =>
          apply evalDist_bind_congr
          intro rightRoot _hrightRoot
          rfl
      | some resolved =>
          apply evalDist_bind_congr
          intro rightRoot _hrightRoot
          simp only
          rw [bind_assoc]
          apply evalDist_bind_congr
          intro observed _hobserved
          cases observed <;> rfl
    exact hconditionedRight.trans (hswap.trans horiginalRight)
  exact relTriple_of_evalDist_eq_left hleft
    (relTriple_of_evalDist_eq_right hright hconditioned)

end SphincsSecurity.Concrete.OtsProbeSimulation

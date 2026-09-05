import SphincsSecurity.Proof.OtsProbeCanonicalQueryTrace
import SphincsSecurity.Proof.OtsProbeResolvedAdaptiveProbability

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local instance] Classical.propDecidable
attribute [local irreducible] maskedPublishedTreeRoot

set_option maxRecDepth 100000 in
theorem runCanonicalQueryTrace_synchronized_projection
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    evalDist (Prod.fst <$> runCanonicalQueryTrace parameter root ftsSecret computation context fuel table cache) =
      evalDist (runSynchronizedResolved (canonicalChronologicalAdversaryImpl parameter root table ftsSecret)
        computation context fuel table cache) := by
  induction computation using OracleComp.inductionOn generalizing context fuel cache with
  | pure value =>
      simp only [runCanonicalQueryTrace, runSynchronizedResolved, OracleComp.construct_pure]
      split_ifs <;> simp
  | query_bind input next ih =>
      rw [runCanonicalQueryTrace_query_bind, runSynchronizedResolved, OracleComp.construct_query_bind]
      by_cases hcomplete : DeferredCompletable table context
      · simp only [hcomplete, ↓reduceIte, map_bind]
        apply evalDist_bind_congr
        intro result hresult
        cases result with
        | none => simp
        | some result =>
            have hcore := resolvedCore_of_mem_canonicalChronologicalAdversaryImpl parameter root table
              ftsSecret input context fuel cache result hconsistent hstarts hresult
            simp only [map_bind, map_pure]
            change evalDist (Prod.fst <$> runCanonicalQueryTrace parameter root ftsSecret
                (next result.value.1) result.context result.remaining result.table result.value.2) =
              evalDist (runSynchronizedResolved (canonicalChronologicalAdversaryImpl parameter root table ftsSecret)
                (next result.value.1) result.context result.remaining result.table result.value.2)
            rw [hcore.1]
            exact ih result.value.1 result.context result.remaining result.value.2 hcore.2.1 hcore.2.2
      · simp [hcomplete]

theorem runCanonicalQueryTrace_observer_projection
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (observer : Option (ResolvedRunResult (α × SplitHashCache)) → ProbComp β)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    evalDist (runCanonicalQueryTrace parameter root ftsSecret computation context fuel table cache >>=
      fun result => observer result.1) =
      evalDist (runSynchronizedResolved (canonicalChronologicalAdversaryImpl parameter root table ftsSecret)
        computation context fuel table cache >>= observer) := by
  have hprojection := runCanonicalQueryTrace_synchronized_projection parameter root ftsSecret
    computation context fuel table cache hconsistent hstarts
  rw [← bind_map_left]
  rw [evalDist_bind, evalDist_bind, hprojection]

noncomputable def canonicalRetainedSigningQueryTrace
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp (Option (ResolvedRunResult (RetainedGameResult × SplitHashCache)) × List CanonicalQuerySelection) := do
  let rootResult ← runResolvedFromTable
    { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
    fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)
  match rootResult with
  | none => pure (none, [])
  | some rootResult => do
      let result ← runCanonicalQueryTrace parameter rootResult.value.1 ftsSecret
        (signingTraceComputation (adversary.main ⟨rootResult.value.1, parameter⟩))
        rootResult.context rootResult.remaining rootResult.table rootResult.value.2
      let verified ← canonicalVerifierContinuation parameter rootResult.value.1 result.1
      pure (verified, result.2)

theorem canonicalRetainedSigningQueryTrace_projection
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (Prod.fst <$> canonicalRetainedSigningQueryTrace adversary parameter table ftsSecret fuel) =
      evalDist (canonicalChronologicalRetainedRunAfterFtsSecrets adversary parameter table ftsSecret fuel) := by
  unfold canonicalRetainedSigningQueryTrace canonicalChronologicalRetainedRunAfterFtsSecrets
  rw [map_bind]
  apply evalDist_bind_congr
  intro rootOption hroot
  cases rootOption with
  | none => simp
  | some rootResult =>
      have hcore := resolvedCore_of_mem_runResolved_maskedPublishedTreeRoot parameter table fuel rootResult hroot
      dsimp only
      rw [hcore.1]
      simp only [map_bind, map_pure, bind_pure]
      exact runCanonicalQueryTrace_observer_projection parameter rootResult.value.1 ftsSecret
        (signingTraceComputation (adversary.main ⟨rootResult.value.1, parameter⟩))
        rootResult.context rootResult.remaining table rootResult.value.2
        (canonicalVerifierContinuation parameter rootResult.value.1) hcore.2.1 hcore.2.2

theorem probEvent_winningRetainedVerifyProbe_le_signingQueryTrace_failure
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[WinningRetainedVerifyProbeWitness parameter (extendStartTable table) ftsSecret |
      actualRetainedGameAfterTable adversary parameter ftsSecret (extendStartTable table)] ≤
      Pr[fun result => result = none |
        canonicalRetainedSigningQueryTrace adversary parameter table ftsSecret fuel >>=
          fun result => finishResolvedRun result.1] := by
  have hprojection := canonicalRetainedSigningQueryTrace_projection adversary parameter table ftsSecret fuel
  have hfinish : evalDist (canonicalRetainedSigningQueryTrace adversary parameter table ftsSecret fuel >>=
      fun result => finishResolvedRun result.1) =
      evalDist (canonicalChronologicalRetainedRunAfterFtsSecrets adversary parameter table ftsSecret fuel >>=
        finishResolvedRun) := by
    rw [← bind_map_left, evalDist_bind, evalDist_bind, hprojection]
  rw [probEvent_eq_eq_probOutput, _root_.OracleComp.probOutput_congr rfl hfinish]
  simpa only [probEvent_eq_eq_probOutput] using
    probEvent_winningRetainedVerifyProbe_le_canonicalFinishedResolvedRun_none adversary parameter table ftsSecret fuel

end SphincsSecurity.Concrete.OtsProbeSimulation

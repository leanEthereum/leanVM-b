import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveProductionCommonCache

/-!
# Hidden-cache quotient through the detailed selector

Equal ordinary cache projections give exactly coupled detailed permissive selections. This removes
the proof-only hidden target entry before the lazy sampler is commuted through the selector.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

theorem relTriple_permissiveDetailedRootAwareOrdinalSelection_of_ordinaryCacheEq
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (leftCache rightCache : SplitHashCache)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache) :
    RelTriple
      (permissiveDetailedRootAwareOrdinalSelection ordinal parameter root ftsSecret computation
        candidates state fuel table leftCache)
      (permissiveDetailedRootAwareOrdinalSelection ordinal parameter root ftsSecret computation
        candidates state fuel table rightCache)
      (fun left right => left = right) := by
  induction computation using OracleComp.inductionOn generalizing
      candidates state fuel leftCache rightCache with
  | pure value =>
      simp only [permissiveDetailedRootAwareOrdinalSelection, OracleComp.construct_pure]
      by_cases hselected : ordinal < candidates.length <;>
        simp [hselected]
  | query_bind query next ih =>
      rw [permissiveDetailedRootAwareOrdinalSelection, OracleComp.construct_query_bind,
        permissiveDetailedRootAwareOrdinalSelection, OracleComp.construct_query_bind]
      by_cases hselected : ordinal < candidates.length
      · simp [hselected]
      · simp only [hselected, ↓reduceDIte]
        cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                apply relTriple_bind
                  (permissiveOrdinaryCacheCouples_splitUniformImpl n leftCache rightCache hcache
                    state fuel table)
                intro leftResult rightResult hresult
                cases leftResult with
                | none =>
                    cases rightResult with
                    | none => simp [finishPermissiveDetailedPrivateOrdinalSelection]
                    | some rightResult => exact False.elim hresult
                | some leftResult =>
                    cases rightResult with
                    | none => exact False.elim hresult
                    | some rightResult =>
                        rcases hresult with
                          ⟨hstate, hremaining, htable, hvalue, hnextCache⟩
                        simp only [finishPermissiveDetailedPrivateOrdinalSelection]
                        simpa only [hstate, hremaining, hvalue,
                          permissiveDetailedRootAwareOrdinalSelection] using
                          ih leftResult.value.1 candidates leftResult.state
                            leftResult.remaining leftResult.value.2 rightResult.value.2
                            hnextCache
            | inr input =>
                let nextCandidates :=
                  permissiveRootAwareCandidates parameter input table state candidates
                by_cases hnextSelected : ordinal < nextCandidates.length
                · simp [nextCandidates, hnextSelected]
                · simp only [nextCandidates, hnextSelected, ↓reduceDIte]
                  have haction :=
                    permissiveOrdinaryCacheCouples_rootAwarePublicPlan parameter input
                      (materializedCanonicalContext table state).state
                      (permissiveRootAwarePlan parameter input table state)
                      leftCache rightCache hcache state fuel table
                  apply relTriple_bind (by
                    simpa only [permissiveRootAwarePublicAction,
                      permissiveRootAwarePublicActionWithPlan] using haction)
                  intro leftResult rightResult hresult
                  cases leftResult with
                  | none =>
                      cases rightResult with
                      | none => simp [finishPermissiveDetailedPrivateOrdinalSelection]
                      | some rightResult => exact False.elim hresult
                  | some leftResult =>
                      cases rightResult with
                      | none => exact False.elim hresult
                      | some rightResult =>
                          rcases hresult with
                            ⟨hstate, hremaining, htable, hvalue, hnextCache⟩
                          simp only [finishPermissiveDetailedPrivateOrdinalSelection]
                          simpa only [hstate, hremaining, hvalue,
                            permissiveDetailedRootAwareOrdinalSelection] using
                            ih leftResult.value.1 nextCandidates leftResult.state
                              leftResult.remaining leftResult.value.2 rightResult.value.2
                              hnextCache
        | inr message =>
            apply relTriple_bind
              (permissiveOrdinaryCacheCouples_maskedSign parameter root ftsSecret message
                leftCache rightCache hcache state fuel table)
            intro leftResult rightResult hresult
            cases leftResult with
            | none =>
                cases rightResult with
                | none => simp [finishPermissiveDetailedPrivateOrdinalSelection]
                | some rightResult => exact False.elim hresult
            | some leftResult =>
                cases rightResult with
                | none => exact False.elim hresult
                | some rightResult =>
                    rcases hresult with ⟨hstate, hremaining, htable, hvalue, hnextCache⟩
                    simp only [finishPermissiveDetailedPrivateOrdinalSelection]
                    simpa only [hstate, hremaining, hvalue,
                      permissiveDetailedRootAwareOrdinalSelection] using
                      ih leftResult.value.1 candidates leftResult.state leftResult.remaining
                        leftResult.value.2 rightResult.value.2 hnextCache

theorem evalDist_permissiveDetailedRootAwareOrdinalSelection_eq_of_ordinaryCacheEq
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (leftCache rightCache : SplitHashCache)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache) :
    evalDist
        (permissiveDetailedRootAwareOrdinalSelection ordinal parameter root ftsSecret computation
          candidates state fuel table leftCache) =
      evalDist
        (permissiveDetailedRootAwareOrdinalSelection ordinal parameter root ftsSecret computation
          candidates state fuel table rightCache) :=
  evalDist_eq_of_relTriple_eqRel
    (relTriple_permissiveDetailedRootAwareOrdinalSelection_of_ordinaryCacheEq ordinal parameter
      root ftsSecret computation candidates state fuel table leftCache rightCache hcache)

theorem ordinaryQueryCache_replaceHiddenRootCache
    (target : Position) (output : HashOutput) (cache : SplitHashCache) :
    ordinaryQueryCache (replaceHiddenRootCache target output cache) = ordinaryQueryCache cache := by
  funext input
  simp [ordinaryQueryCache, replaceHiddenRootCache]

end SphincsSecurity.Concrete.OtsProbeSimulation

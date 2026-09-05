import SphincsSecurity.Proof.OtsProbeCanonicalReserve

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

theorem purePlan_candidate_none_of_not_atOtsPosition
    (parameter : PublicParameter) (input : HashInput) (state : LazyRevealProbe.State Coordinate)
    (hnot : ¬∃ position : Position, IsOtsPosition position ∧ AtPosition parameter input position) :
    (purePlanProbingHashQuery parameter input state).candidate? = none := by
  have hprobe : decodeProbe? parameter input = none := by
    cases hdecode : decodeProbe? parameter input with
    | none => rfl
    | some candidate =>
        exfalso
        rcases decodePosition?_chain_or_leaf_of_decodeProbe? parameter input candidate hdecode with hchain | hleaf
        · obtain ⟨lay, tree, leafIdx, chainIdx, step, hposition⟩ := hchain
          exact hnot ⟨.chain lay tree leafIdx chainIdx step, trivial,
            (decodePosition?_eq_some_iff parameter input _).mp hposition⟩
        · obtain ⟨lay, tree, leafIdx, hposition⟩ := hleaf
          exact hnot ⟨.leaf lay tree leafIdx, trivial,
            (decodePosition?_eq_some_iff parameter input _).mp hposition⟩
  apply purePlan_candidate_none_of_probe_none_nonnode parameter input state hprobe
  rintro ⟨lay, tree, level, nodeIdx, hposition⟩
  exact hnot ⟨.node lay tree level nodeIdx, trivial,
    (decodePosition?_eq_some_iff parameter input _).mp hposition⟩

theorem probingHashQueryAfterPublicPlan_ordinaryCharge_eq_executeCandidate
    (parameter : PublicParameter) (input : HashInput) (publicState : LazyRevealProbe.State Coordinate)
    (plan : PlannedHashQuery) (cache : SplitHashCache) (context : DeferredContext) (fuel : Nat) :
    ordinaryContinuationCharge (fun _ _ _ => 0)
        ((probingHashQueryAfterPublicPlan parameter input publicState plan).run cache) context fuel =
      ordinaryContinuationCharge (fun _ _ _ => 0) ((executeCandidate? plan.candidate?).run cache) context fuel := by
  unfold probingHashQueryAfterPublicPlan
  rw [StateT.run_bind]
  apply ordinaryContinuationCharge_zero_bind_of_tail_probeFree
  intro result
  exact probingHashQueryPublicAction_probeFree parameter input publicState plan.action result.2

theorem probingHashQueryAfterPublicPlan_ordinaryCharge_le_rootAware
    (parameter : PublicParameter) (input : HashInput) (publicState : LazyRevealProbe.State Coordinate)
    (plan : PlannedHashQuery) (cache : SplitHashCache) (context : DeferredContext) (fuel : Nat) :
    ordinaryContinuationCharge (fun _ _ _ => 0)
        ((probingHashQueryAfterPublicPlan parameter input publicState plan).run cache) context fuel ≤
      ordinaryContinuationCharge (fun _ _ _ => 0)
        ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run cache) context fuel := by
  cases hcandidate : plan.candidate? with
  | none =>
      rw [probingHashQueryAfterPublicPlan_ordinaryCharge_eq_executeCandidate, hcandidate]
      simp [executeCandidate?, ordinaryContinuationCharge]
  | some candidate =>
      have heq : probingHashQueryAfterPublicPlan parameter input publicState plan =
          probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan := by
        unfold probingHashQueryAfterPublicPlan probingHashQueryAfterRootAwarePublicPlan
        simp only [rootAwareCandidateForPlan?, hcandidate]
        rfl
      rw [heq]

noncomputable def canonicalJointHashCharge
    (parameter : PublicParameter) (input : HashInput) (context : DeferredContext)
    (fuel : Nat) (cache : SplitHashCache) : ℝ≥0∞ :=
  ordinaryContinuationCharge (fun _ _ _ => 0)
      ((probingHashQueryAfterPublicPlan parameter input context.state
        (purePlanProbingHashQuery parameter input context.state)).run cache)
      (materializedDeferredContext context) fuel +
    (materializedCandidateCharge (materializedDeferredState context)
      (rootAwarePlannedCandidate? parameter input context.state) : ℝ≥0∞) * (4 / 3)

set_option maxRecDepth 100000 in
theorem canonicalJointHashCharge_le_canonicalOtsHashCharge
    (parameter : PublicParameter) (input : HashInput) (context : DeferredContext)
    (fuel : Nat) (cache : SplitHashCache) :
    canonicalJointHashCharge parameter input context fuel cache ≤ canonicalOtsHashCharge parameter input context := by
  classical
  unfold canonicalOtsHashCharge canonicalJointHashCharge
  split_ifs with hots
  · apply le_trans (add_le_add
      (probingHashQueryAfterPublicPlan_ordinaryCharge_le_rootAware parameter input context.state
        (purePlanProbingHashQuery parameter input context.state) cache (materializedDeferredContext context) fuel) le_rfl)
    simpa only [rootAwareCandidateForPlan?_purePlan, materializedDeferredContext, directDeferredContext] using
      probingHashQueryAfterRootAwarePublicPlan_weightedCharge_le_four_thirds parameter input context.state
        (purePlanProbingHashQuery parameter input context.state) cache (materializedDeferredContext context) fuel
  · have hnone := purePlan_candidate_none_of_not_atOtsPosition parameter input context.state hots
    rw [probingHashQueryAfterPublicPlan_ordinaryCharge_eq_executeCandidate, hnone]
    simp [executeCandidate?, ordinaryContinuationCharge, rootAwarePlannedCandidate?, hnone]

noncomputable def canonicalJointOuterCharge (parameter : PublicParameter) :
    (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ℝ≥0∞
  | .inl (.inr input), context, fuel, cache => canonicalJointHashCharge parameter input context fuel cache
  | _, _, _, _ => 0

set_option maxRecDepth 100000 in
theorem expectedCanonicalJointCharge_le_actualReserve
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (actualCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) actualCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context actualCache)
    (hpublished : PublishedValues context.state) (hcomputed : DeferredComputationsClosed context) :
    expectedCanonicalQueryCharge parameter root ftsSecret (canonicalJointOuterCharge parameter)
        computation context fuel table cache ≤
      expectedQueryCharge
        (otsOpeningRefinedQueryReserve
          (⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
            ftsSecret⟩ : SecretKey))
        (simulateQ (expandedAdversaryImpl
          (⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
            ftsSecret⟩ : SecretKey)) computation) actualCache := by
  apply le_trans ?_ (expectedOuterQueryCharge_le_expanded _ _ computation actualCache)
  apply expectedCanonicalQueryCharge_le_outerQueryCharge parameter root table ftsSecret
    (canonicalJointOuterCharge parameter) _ ?_ computation context fuel cache actualCache
    hinvariant hvisible hpublished hcomputed
  intro input nextContext remaining nextCache concreteCache hcontext _hvisible _hpublished hcomputed
  cases input with
  | inl query =>
      cases query with
      | inl n => exact le_rfl
      | inr input =>
          change canonicalJointHashCharge parameter input nextContext remaining nextCache ≤
            otsOpeningRefinedQueryReserve
              (⟨parameter, root, fun lay tree leafIdx chainIdx =>
                truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩ : SecretKey) concreteCache input
          exact (canonicalJointHashCharge_le_canonicalOtsHashCharge parameter input nextContext remaining nextCache).trans
            (canonicalOtsHashCharge_le_refinedReserve
              (secretKey := ⟨parameter, root, fun lay tree leafIdx chainIdx =>
                truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩) hcontext hcomputed rfl input)
  | inr message => exact le_rfl

end SphincsSecurity.Concrete.OtsProbeSimulation

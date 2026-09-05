import SphincsSecurity.Proof.OtsProbeHashCutCharge
import SphincsSecurity.Proof.OtsProbeCanonicalChargeSampled

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def unresolvedPositionCandidateCharge (context : DeferredContext) : Option Probe → ENNReal
  | some candidate@⟨.position _, _⟩ =>
      (unmaterializedCandidateCharge (materializedDeferredState context) (some candidate) : ENNReal)
  | _ => 0

theorem unresolvedCandidateCharges_sum
    (context : DeferredContext) (candidate : Option Probe) :
    unresolvedStartCandidateCharge context candidate + unresolvedPositionCandidateCharge context candidate =
      (unmaterializedCandidateCharge (materializedDeferredState context) candidate : ENNReal) := by
  cases candidate with
  | none => simp [unresolvedStartCandidateCharge, unresolvedPositionCandidateCharge, unmaterializedCandidateCharge]
  | some candidate =>
      rcases candidate with ⟨coordinate, digest⟩
      cases coordinate with
      | position position => simp [unresolvedStartCandidateCharge, unresolvedPositionCandidateCharge]
      | chainStart lay tree leafIdx chainIdx =>
          by_cases hmissing : context.state.values (.chainStart lay tree leafIdx chainIdx) = none
          · simp [unresolvedStartCandidateCharge, unresolvedPositionCandidateCharge, hmissing]
          · simp [unresolvedStartCandidateCharge, unresolvedPositionCandidateCharge, hmissing,
              unmaterializedCandidateCharge, LazyRevealProbe.pendingProbeCharge, materializedDeferredState]

noncomputable def canonicalWeightedHashCharge
    (parameter : PublicParameter) (input : HashInput) (context : DeferredContext) : ENNReal :=
  (unmaterializedCandidateCharge (materializedDeferredState context)
      (purePlanProbingHashQuery parameter input context.state).candidate? : ENNReal) * (4 / 3) +
    (materializedCandidateCharge (materializedDeferredState context)
      (rootAwarePlannedCandidate? parameter input context.state) : ENNReal) * (4 / 3)

noncomputable def canonicalWeightedOuterCharge (parameter : PublicParameter) :
    (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ENNReal
  | .inl (.inr input), context, _, _ => canonicalWeightedHashCharge parameter input context
  | _, _, _, _ => 0

theorem weighted_candidate_components_le
    (parameter : PublicParameter) (input : HashInput) (context : DeferredContext) :
    unresolvedStartCandidateCharge context (purePlanProbingHashQuery parameter input context.state).candidate? * (4 / 3) +
      unresolvedPositionCandidateCharge context (purePlanProbingHashQuery parameter input context.state).candidate? +
      (materializedCandidateCharge (materializedDeferredState context)
        (rootAwarePlannedCandidate? parameter input context.state) : ENNReal) * (4 / 3) ≤
      canonicalWeightedHashCharge parameter input context := by
  unfold canonicalWeightedHashCharge
  rw [← unresolvedCandidateCharges_sum, add_mul]
  apply add_le_add _ le_rfl
  apply add_le_add le_rfl
  apply le_mul_of_one_le_right'
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num

theorem canonicalWeightedHashCharge_le_canonicalOtsHashCharge
    (parameter : PublicParameter) (input : HashInput) (context : DeferredContext) :
    canonicalWeightedHashCharge parameter input context ≤ canonicalOtsHashCharge parameter input context := by
  unfold canonicalWeightedHashCharge canonicalOtsHashCharge
  split_ifs with hots
  · have hsum :
        unmaterializedCandidateCharge (materializedDeferredState context)
            (purePlanProbingHashQuery parameter input context.state).candidate? +
          materializedCandidateCharge (materializedDeferredState context)
            (rootAwarePlannedCandidate? parameter input context.state) ≤ 1 := by
      cases hcandidate : (purePlanProbingHashQuery parameter input context.state).candidate? with
      | none =>
          have h := candidateCharge_sum_le_one (materializedDeferredState context) (rootAwarePlannedCandidate? parameter input context.state)
          simpa only [unmaterializedCandidateCharge, Nat.zero_add] using (Nat.le_add_left _ _).trans h
      | some candidate =>
          rw [rootAwarePlannedCandidate?_eq_of_plan_some hcandidate]
          exact candidateCharge_sum_le_one _ _
    rw [← add_mul, ← Nat.cast_add]
    simpa only [Nat.cast_one, one_mul] using mul_le_mul' (Nat.cast_le.mpr hsum :
      ((unmaterializedCandidateCharge (materializedDeferredState context)
        (purePlanProbingHashQuery parameter input context.state).candidate? +
        materializedCandidateCharge (materializedDeferredState context)
          (rootAwarePlannedCandidate? parameter input context.state) : Nat) : ENNReal) ≤ (1 : Nat))
      (le_refl (4 / 3 : ENNReal))
  · have hnone := purePlan_candidate_none_of_not_atOtsPosition parameter input context.state hots
    simp [hnone, unmaterializedCandidateCharge, rootAwarePlannedCandidate?]

theorem canonicalWeightedOuterCharge_le_ots (parameter : PublicParameter)
    (input : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) :
    canonicalWeightedOuterCharge parameter input context fuel cache ≤ canonicalOtsOuterCharge parameter input context fuel cache := by
  cases input with
  | inl input =>
      cases input with
      | inl n => exact le_rfl
      | inr input => exact canonicalWeightedHashCharge_le_canonicalOtsHashCharge parameter input context
  | inr message => exact le_rfl

theorem expectedCanonicalQueryCharge_mono
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (left right : (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ENNReal)
    (hle : ∀ input context fuel cache, left input context fuel cache ≤ right input context fuel cache)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    expectedCanonicalQueryCharge parameter root ftsSecret left computation context fuel table cache ≤
      expectedCanonicalQueryCharge parameter root ftsSecret right computation context fuel table cache := by
  induction computation using OracleComp.inductionOn generalizing context fuel table cache with
  | pure value => rfl
  | query_bind input next ih =>
      rw [expectedCanonicalQueryCharge_query_bind, expectedCanonicalQueryCharge_query_bind]
      split_ifs
      · apply add_le_add (hle input context fuel cache)
        apply ENNReal.tsum_le_tsum
        intro option
        cases option with
        | none => exact le_rfl
        | some result =>
            exact mul_le_mul' le_rfl (ih result.value.1 result.context result.remaining result.table result.value.2)
      · exact le_rfl

theorem expectedCanonicalWeightedCharge_le_actualReserve
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (actualCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) actualCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context actualCache)
    (hpublished : PublishedValues context.state) (hcomputed : DeferredComputationsClosed context) :
    expectedCanonicalQueryCharge parameter root ftsSecret (canonicalWeightedOuterCharge parameter)
        computation context fuel table cache ≤
      expectedQueryCharge
        (otsOpeningRefinedQueryReserve
          (⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
            ftsSecret⟩ : SecretKey))
        (simulateQ (expandedAdversaryImpl
          (⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
            ftsSecret⟩ : SecretKey)) computation) actualCache := by
  exact (expectedCanonicalQueryCharge_mono parameter root ftsSecret (canonicalWeightedOuterCharge parameter)
    (canonicalOtsOuterCharge parameter) (canonicalWeightedOuterCharge_le_ots parameter)
    computation context fuel table cache).trans
      (expectedCanonicalOtsCharge_le_actualReserve parameter root table ftsSecret computation context fuel cache actualCache
        hinvariant hvisible hpublished hcomputed)

noncomputable def unresolvedPositionOuterCharge (parameter : PublicParameter) :
    (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ENNReal
  | .inl (.inr input), context, _, _ =>
      unresolvedPositionCandidateCharge context (purePlanProbingHashQuery parameter input context.state).candidate?
  | _, _, _, _ => 0

noncomputable def materializedOuterCandidateCharge (parameter : PublicParameter) :
    (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ENNReal
  | .inl (.inr input), context, _, _ =>
      (materializedCandidateCharge (materializedDeferredState context)
        (rootAwarePlannedCandidate? parameter input context.state) : ENNReal)
  | _, _, _, _ => 0

noncomputable def canonicalComponentOuterCharge (parameter : PublicParameter)
    (input : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) : ENNReal :=
  unresolvedStartOuterCharge parameter input context fuel cache * (4 / 3) +
    unresolvedPositionOuterCharge parameter input context fuel cache +
    materializedOuterCandidateCharge parameter input context fuel cache * (4 / 3)

theorem canonicalComponentOuterCharge_le_weighted (parameter : PublicParameter)
    (input : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) :
    canonicalComponentOuterCharge parameter input context fuel cache ≤ canonicalWeightedOuterCharge parameter input context fuel cache := by
  cases input with
  | inl input =>
      cases input with
      | inl n => simp [canonicalComponentOuterCharge, unresolvedStartOuterCharge, unresolvedPositionOuterCharge,
          materializedOuterCandidateCharge, canonicalWeightedOuterCharge]
      | inr input => exact weighted_candidate_components_le parameter input context
  | inr message => simp [canonicalComponentOuterCharge, unresolvedStartOuterCharge, unresolvedPositionOuterCharge,
      materializedOuterCandidateCharge, canonicalWeightedOuterCharge]

theorem expectedCanonicalQueryCharge_add
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (left right : (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ENNReal)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    expectedCanonicalQueryCharge parameter root ftsSecret
        (fun input context fuel cache => left input context fuel cache + right input context fuel cache)
        computation context fuel table cache =
      expectedCanonicalQueryCharge parameter root ftsSecret left computation context fuel table cache +
        expectedCanonicalQueryCharge parameter root ftsSecret right computation context fuel table cache := by
  induction computation using OracleComp.inductionOn generalizing context fuel table cache with
  | pure value => simp [expectedCanonicalQueryCharge]
  | query_bind input next ih =>
      rw [expectedCanonicalQueryCharge_query_bind, expectedCanonicalQueryCharge_query_bind, expectedCanonicalQueryCharge_query_bind]
      split_ifs with hcomplete
      · conv_rhs => rw [add_add_add_comm]
        congr 1
        rw [← ENNReal.tsum_add]
        apply tsum_congr
        intro option
        cases option with
        | none => simp
        | some result =>
            dsimp only
            rw [ih result.value.1 result.context result.remaining result.table result.value.2, mul_add]
      · simp

theorem expectedCanonicalQueryCharge_mul
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (charge : (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ENNReal) (factor : ENNReal)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    expectedCanonicalQueryCharge parameter root ftsSecret
        (fun input context fuel cache => charge input context fuel cache * factor) computation context fuel table cache =
      expectedCanonicalQueryCharge parameter root ftsSecret charge computation context fuel table cache * factor := by
  induction computation using OracleComp.inductionOn generalizing context fuel table cache with
  | pure value => simp [expectedCanonicalQueryCharge]
  | query_bind input next ih =>
      rw [expectedCanonicalQueryCharge_query_bind, expectedCanonicalQueryCharge_query_bind]
      split_ifs
      · rw [add_mul, ← ENNReal.tsum_mul_right]
        congr 1
        apply tsum_congr
        intro option
        cases option with
        | none => simp
        | some result =>
            dsimp only
            rw [ih result.value.1 result.context result.remaining result.table result.value.2, mul_assoc]
      · simp

end SphincsSecurity.Concrete.OtsProbeSimulation

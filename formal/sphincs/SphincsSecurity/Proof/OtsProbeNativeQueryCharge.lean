import SphincsSecurity.Proof.OtsProbePrivateValueProbeCounting

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def resolvedContinuationCharge
    (charge : LazyRevealProbe.Query Coordinate → ENNReal)
    (next : α → OracleComp (LazyRevealProbe.World Coordinate) β) : Option (ResolvedRunResult α) → ENNReal
  | none => 0
  | some result => expectedResolvedQueryCharge charge (next result.value) result.context result.remaining result.table

theorem expectedResolvedQueryCharge_bind
    (charge : LazyRevealProbe.Query Coordinate → ENNReal)
    (left : OracleComp (LazyRevealProbe.World Coordinate) α) (next : α → OracleComp (LazyRevealProbe.World Coordinate) β)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    expectedResolvedQueryCharge charge (left >>= next) context fuel table =
      expectedResolvedQueryCharge charge left context fuel table +
        ∑' result, Pr[= result | runResolvedFromTable context fuel table left] * resolvedContinuationCharge charge next result := by
  induction left using OracleComp.inductionOn generalizing context fuel table with
  | pure value => simp [expectedResolvedQueryCharge, runResolvedFromTable, resolvedContinuationCharge]
  | query_bind input continuation ih =>
      rw [bind_assoc, expectedResolvedQueryCharge_query_bind, expectedResolvedQueryCharge_query_bind,
        runResolvedFromTable_bind, tsum_probOutput_bind_mul, add_assoc, ← ENNReal.tsum_add]
      congr 1
      apply tsum_congr
      intro result
      cases result with
      | none => simp [resolvedContinuationCharge]
      | some result =>
          dsimp only
          rw [ih, mul_add, ← ENNReal.tsum_mul_left]

theorem expectedResolvedStructuralCharge_eq_zero_of_probeFree
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hfree : computation.IsQueryBoundP LazyRevealProbe.IsProbe 0) :
    expectedResolvedQueryCharge structuralProbeQueryCharge computation context fuel table = 0 := by
  have hle : expectedResolvedQueryCharge structuralProbeQueryCharge computation context fuel table ≤ (0 : ENNReal) := by
    simpa only [Nat.cast_zero] using expectedResolvedStructuralCharge_le_probeBound computation 0 context fuel table hfree
  exact le_antisymm hle zero_le

theorem probingHashQuery_expectedResolvedStructuralCharge_le
    (parameter : PublicParameter) (input : HashInput) (cache : SplitHashCache)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    expectedResolvedQueryCharge structuralProbeQueryCharge ((probingHashQuery parameter input).run cache) context fuel table ≤
      otsHashInputCharge parameter input := by
  unfold otsHashInputCharge
  split_ifs with hots
  · simpa only [Nat.cast_one] using expectedResolvedStructuralCharge_le_probeBound _ 1 context fuel table (probingHashQuery_run_isProbeBound parameter input cache)
  · rw [probingHashQuery_eq_split_of_not_atOtsPosition parameter input hots,
      expectedResolvedStructuralCharge_eq_zero_of_probeFree _ context fuel table (splitHashQuery_probeFree _ cache)]

theorem maskedExpandedAdversaryImpl_expectedResolvedStructuralCharge_le
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (cache : SplitHashCache)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    expectedResolvedQueryCharge structuralProbeQueryCharge ((maskedExpandedAdversaryImpl parameter root ftsSecret input).run cache)
      context fuel table ≤ otsOuterQueryCharge parameter input := by
  cases input with
  | inl input =>
      cases input with
      | inl n =>
          change expectedResolvedQueryCharge structuralProbeQueryCharge ((splitUniformImpl n).run cache) context fuel table ≤ 0
          rw [expectedResolvedStructuralCharge_eq_zero_of_probeFree _ context fuel table (splitUniformImpl_probeFree n cache)]
      | inr input => exact probingHashQuery_expectedResolvedStructuralCharge_le parameter input cache context fuel table
  | inr message =>
      change expectedResolvedQueryCharge structuralProbeQueryCharge ((maskedSign parameter root ftsSecret message).run cache) context fuel table ≤ 0
      rw [expectedResolvedStructuralCharge_eq_zero_of_probeFree _ context fuel table (maskedSign_probeFree parameter root ftsSecret message cache)]


noncomputable def expectedNativeOuterQueryCharge
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (charge : (OracleWorld + SigningSpec).Domain → ENNReal)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    DeferredContext → Nat → (OtsSecretIndex → HashOutput) → SplitHashCache → ENNReal :=
  OracleComp.construct (fun _ _ _ _ _ => 0)
    (fun input _ next context fuel table cache =>
      charge input + ∑' result,
        Pr[= result | runResolvedFromTable context fuel table ((maskedExpandedAdversaryImpl parameter root ftsSecret input).run cache)] *
          match result with
          | none => 0
          | some result => next result.value.1 result.context result.remaining result.table result.value.2) computation

theorem expectedNativeOuterQueryCharge_query_bind
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (charge : (OracleWorld + SigningSpec).Domain → ENNReal) (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    expectedNativeOuterQueryCharge parameter root ftsSecret charge (OracleSpec.query input >>= next) context fuel table cache =
      charge input + ∑' result,
        Pr[= result | runResolvedFromTable context fuel table ((maskedExpandedAdversaryImpl parameter root ftsSecret input).run cache)] *
          match result with
          | none => 0
          | some result => expectedNativeOuterQueryCharge parameter root ftsSecret charge (next result.value.1)
              result.context result.remaining result.table result.value.2 := rfl

theorem simulateQ_maskedExpanded_expectedResolvedStructuralCharge_le
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    expectedResolvedQueryCharge structuralProbeQueryCharge
      ((simulateQ (maskedExpandedAdversaryImpl parameter root ftsSecret) computation).run cache) context fuel table ≤
      expectedNativeOuterQueryCharge parameter root ftsSecret (otsOuterQueryCharge parameter) computation context fuel table cache := by
  induction computation using OracleComp.inductionOn generalizing context fuel table cache with
  | pure value => simp [expectedResolvedQueryCharge, expectedNativeOuterQueryCharge]
  | query_bind input next ih =>
      rw [simulateQ_query_bind, StateT.run_bind, expectedResolvedQueryCharge_bind, expectedNativeOuterQueryCharge_query_bind]
      apply add_le_add (maskedExpandedAdversaryImpl_expectedResolvedStructuralCharge_le parameter root ftsSecret input cache context fuel table)
      apply ENNReal.tsum_le_tsum
      intro result
      cases result with
      | none => rfl
      | some result => exact mul_le_mul' le_rfl (ih result.value.1 result.context result.remaining result.table result.value.2)

theorem sum_targets_privateResolvedRawCandidate_hit_le_nativeOtsQueryCharge
    (targets : Finset Position) (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (q : Nat) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hensured : ∀ target ∈ targets, .position target ∈ context.state.ensured)
    (hstate : ∀ target ∈ targets, context.state.values (.position target) = none)
    (hvalue : ∀ target ∈ targets, context.values target = none)
    (hhidden : ∀ target ∈ targets, .position target ∉ context.state.revealed)
    (hcard : ∀ target ∈ targets, (context.state.pendingAt (.position target)).card + q ≤ 2 ^ 126) :
    (∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
      Pr[PrivateCandidatePairHit | privateResolvedSelectedCandidate target (privateRawCutCandidate target) <$>
        runPrivateResolvedView target table context fuel (privatePositionProbeCutAt target
          ((simulateQ (maskedExpandedAdversaryImpl parameter root ftsSecret) computation).run cache) ordinal)]) ≤
      expectedNativeOuterQueryCharge parameter root ftsSecret (otsOuterQueryCharge parameter) computation context fuel table cache *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  apply (sum_targets_privateResolvedRawCandidate_hit_le_expectedStructuralCharge targets _ q context fuel table
    hvalid hcomplete hensured hstate hvalue hhidden hcard).trans
  exact mul_le_mul' (simulateQ_maskedExpanded_expectedResolvedStructuralCharge_le parameter root ftsSecret computation context fuel table cache) le_rfl

end SphincsSecurity.Concrete.OtsProbeSimulation

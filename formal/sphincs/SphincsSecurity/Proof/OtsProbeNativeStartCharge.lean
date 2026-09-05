import SphincsSecurity.Proof.OtsProbeStartAllowanceHash
import SphincsSecurity.Proof.OtsProbeStartAllowanceCounting

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def nativeStartCharge
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (input : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) (_fuel : Nat) (_cache : SplitHashCache) : ENNReal :=
  match input with
  | .inl (.inr input) => unresolvedStartCandidateAllowance table context
      (purePlanProbingHashQuery parameter input context.state).candidate?
  | _ => 0

theorem startAllowance_chronologicalQuery
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (input : (OracleWorld + SigningSpec).Domain)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    liveStartProbeAllowance ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache)
        context fuel table =
      if DeferredCompletable table context then nativeStartCharge parameter table input context fuel cache else 0 := by
  cases input with
  | inl input =>
      cases input with
      | inl n =>
          simpa [nativeStartCharge, maskedChronologicalExpandedAdversaryImpl, probingRomImpl, maskedChronologicalSigningImpl] using
            (liveStartProbeAllowance_eq_zero_of_probeFree _ context fuel table (splitUniformImpl_probeFree n cache))
      | inr hashInput => exact startAllowance_probingHashQuery parameter hashInput cache context fuel table hconsistent hstarts
  | inr message =>
      simpa [nativeStartCharge, maskedChronologicalExpandedAdversaryImpl, probingRomImpl, maskedChronologicalSigningImpl] using
        (liveStartProbeAllowance_eq_zero_of_probeFree _ context fuel table
          (maskedPublishedChronologicalSign_probeFree parameter root ftsSecret message cache))

theorem startAllowance_chronological_eq_nativeCharge
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    liveStartProbeAllowance
      ((simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) computation).run cache) context fuel table =
      expectedLiveNativeContextCharge (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
        (nativeStartCharge parameter table) computation context fuel table cache := by
  induction computation using OracleComp.inductionOn generalizing context fuel table cache with
  | pure value => simp [liveStartProbeAllowance, expectedLiveNativeContextCharge]
  | query_bind input next ih =>
      by_cases hcomplete : DeferredCompletable table context
      · rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
          liveStartProbeAllowance_bind _ _ context fuel table hconsistent hstarts,
          startAllowance_chronologicalQuery parameter root ftsSecret input context fuel table cache hconsistent hstarts,
          if_pos hcomplete, expectedLiveNativeContextCharge_query_bind, if_pos hcomplete]
        congr 1
        apply tsum_congr
        intro option
        by_cases hoption : option ∈ support (runResolvedFromTable context fuel table
            ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache))
        · cases option with
          | none => simp [startContinuationAllowance]
          | some result =>
              have hcore := resolvedCore_of_mem_runResolvedFromTable _ context fuel table result hconsistent hstarts hoption
              dsimp only [startContinuationAllowance]
              rw [hcore.1, ih result.value.1 result.context result.remaining table result.value.2 hcore.2.1 hcore.2.2]
        · simp [probOutput_eq_zero_of_not_mem_support hoption]
      · rw [liveStartProbeAllowance_eq_zero_of_not_completable _ context fuel table hcomplete,
          expectedLiveNativeContextCharge_eq_zero_of_not_completable _ _ _ context fuel table cache hcomplete]

theorem sampled_nativeStartCharge_ensuredInitial_le_chainStartCharge
    (targets : Finset Position) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (q fuel : Nat) (cache : SplitHashCache) (hq : q ≤ 2 ^ 126)
    (hbound : ((simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) computation).run cache).IsQueryBoundP
      LazyRevealProbe.IsProbe q) :
    (∑' table, Pr[= table | sampleOtsHashTable] *
      expectedLiveNativeContextCharge (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
        (nativeStartCharge parameter table) computation (ensuredInitialContext targets) fuel table cache) ≤
      (∑' table, Pr[= table | sampleOtsHashTable] * expectedLiveResolvedQueryCharge chainStartProbeQueryCharge
        ((simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) computation).run cache)
        (ensuredInitialContext targets) fuel table) * ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  calc
    _ = ∑' table, Pr[= table | sampleOtsHashTable] * liveStartProbeAllowance
        ((simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) computation).run cache)
        (ensuredInitialContext targets) fuel table := by
      apply tsum_congr
      intro table
      rw [startAllowance_chronological_eq_nativeCharge parameter root ftsSecret computation
        (ensuredInitialContext targets) fuel table cache (ensuredInitialContext_valid targets).valuesConsistent
        (startTableAgrees_of_deferredCompletable (ensuredInitialContext_completable targets table))]
    _ ≤ _ := sampledEnsuredLiveStartAllowance_le_chainStartCharge targets _ fuel q hq hbound

theorem initializedNativeDirectRisk_eq_startAllowance_add_privateAllowance
    (targets : Finset Position) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel q : Nat)
    (hbound : (nativeChronologicalRetainedComputation adversary parameter ftsSecret).IsQueryBoundP
      LazyRevealProbe.IsProbe q) :
    initializedNativeDirectRisk targets adversary parameter ftsSecret fuel q =
      ∑' table, Pr[= table | sampleOtsHashTable] *
        (liveStartProbeAllowance (nativeChronologicalRetainedComputation adversary parameter ftsSecret)
          (ensuredInitialContext targets) fuel table +
          ∑ target ∈ targets, privateLiveProbeAllowance target
            (nativeChronologicalRetainedComputation adversary parameter ftsSecret) (ensuredInitialContext targets) fuel table) := by
  have hprivate : ∀ target ∈ targets,
      (nativeChronologicalRetainedComputation adversary parameter ftsSecret).IsQueryBoundP
        (IsPrivatePositionProbe target) q := by
    intro target _
    apply OracleComp.IsQueryBoundP.of_imp _ hbound
    intro input hinput
    cases input <;> simp_all [IsPrivatePositionProbe, LazyRevealProbe.IsProbe]
  rw [initializedNativeDirectRisk_eq_startHits_add_privateAllowance targets adversary parameter ftsSecret fuel q hprivate,
    sum_sampledEnsuredNativeProbeCut_startHits_eq_liveAllowance targets _ fuel q hbound]
  simp only [mul_add, ENNReal.tsum_add]

theorem sampled_nativeMissingAllowances_le_initializedNativeDirectRisk
    (targets : Finset Position) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel q : Nat)
    (hbound : (nativeChronologicalRetainedComputation adversary parameter ftsSecret).IsQueryBoundP
      LazyRevealProbe.IsProbe q) :
    (∑' table, Pr[= table | sampleOtsHashTable] *
      (liveStartProbeAllowance (nativeChronologicalRetainedComputation adversary parameter ftsSecret)
        (ensuredInitialContext targets) fuel table +
        ∑ target ∈ targets, privateLiveMissingProbeAllowance target
          (nativeChronologicalRetainedComputation adversary parameter ftsSecret) (ensuredInitialContext targets) fuel table)) ≤
      initializedNativeDirectRisk targets adversary parameter ftsSecret fuel q := by
  rw [initializedNativeDirectRisk_eq_startAllowance_add_privateAllowance targets adversary parameter ftsSecret fuel q hbound]
  apply ENNReal.tsum_le_tsum
  intro table
  apply mul_le_mul_right
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro target _
  exact privateLiveMissingProbeAllowance_le_stoppedAllowance target _ (ensuredInitialContext targets) fuel table

end SphincsSecurity.Concrete.OtsProbeSimulation

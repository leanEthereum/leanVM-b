import SphincsSecurity.Proof.SigningCoverageProjection
import SphincsSecurity.Proof.FirstParentSettlementSigning
import SphincsSecurity.Proof.CollisionCoverageMessage

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem signDigestLoop_collisionStructuralRecordPotential_le (key : SecretKey) (message : Message) (attempts : Nat)
    (before after : QueryCache HashSpec) (hfinite : Finite before)
    (selected : Option (Randomness × Index × (DigestTree → FtsLeaf)))
    (hr : (selected, after) ∈ support ((simulateQ romImpl (signDigestLoop attempts key message)).run before)) :
    collisionStructuralRecordPotential key after none ≤ collisionStructuralRecordPotential key before none := by
  induction attempts generalizing before after selected with
  | zero =>
      have heq : (selected, after) = (none, before) := by simpa [signDigestLoop] using hr
      have hcache : after = before := congrArg Prod.snd heq
      rw [hcache]
  | succ attempts ih =>
      rw [signDigestLoop_run_succ_eq, mem_support_bind_iff] at hr
      obtain ⟨randomness, _, hrest⟩ := hr
      rw [mem_support_bind_iff] at hrest
      obtain ⟨⟨attempt, attemptCache⟩, hattempt, hfinish⟩ := hrest
      rw [simulateQ_signAttempt_run_eq, mem_support_bind_iff] at hattempt
      obtain ⟨answer, hquery, heq⟩ := hattempt
      rw [mem_support_pure_iff] at heq
      have hcache : attemptCache = answer.2 := congrArg Prod.snd heq
      have hc := collisionStructuralRecordPotential_message_query_le key before hfinite
        (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) ⟨_, rfl⟩ answer hquery
      have hf : Finite attemptCache := by
        rw [hcache]
        exact finite_of_mem_support_romImpl (query := .inr _) hfinite hquery
      rw [← hcache] at hc
      cases attempt with
      | none =>
          have htail : (selected, after) ∈ support ((simulateQ romImpl (signDigestLoop attempts key message)).run attemptCache) := by
            simpa only [signDigestLoopContinuation] using hfinish
          exact (ih attemptCache after hf selected htail).trans hc
      | some data =>
          have heq : (selected, after) = (some (randomness, data), attemptCache) := by
            simpa only [signDigestLoopContinuation, mem_support_pure_iff] using hfinish
          have hcache : after = attemptCache := congrArg Prod.snd heq
          rw [hcache]
          exact hc

noncomputable def jointCollisionCoverageRecordPotential (key : SecretKey) (cap budget : Nat)
    (state : CoverLogState) (saved : Option ExceptionRecord) : ENNReal :=
  boundedUnionPotential (collisionStructuralRecordPotential key state.1 saved)
    (remainingCoveragePotential key cap budget state ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹)

theorem jointCollisionCoverageRecordPotential_none (key : SecretKey) (cap budget : Nat) (state : CoverLogState) :
    jointCollisionCoverageRecordPotential key cap budget state none =
      FtsProbeSimulation.JointOriginal.jointCollisionCoveragePotential key cap budget state false false := rfl

theorem expected_signAfterDigest_jointRecordPotential_le (key : SecretKey) (cap budget : Nat)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (saved : Option ExceptionRecord) (message : Message) (log : QueryLog SigningSpec)
    (representative : Signature) (hrandomness : representative.randomness = randomness) :
    (∑' result, Pr[= result | runFirstException (CleanParentSettlement key.parameter key.otsSecret key.ftsSecret)
      (liftM (signAfterDigest key randomness index leaves)) cache saved] *
        jointCollisionCoverageRecordPotential key cap budget (result.1.2, log ++ [⟨message, result.1.1⟩]) result.2) ≤
      jointCollisionCoverageRecordPotential key cap budget (cache, log ++ [⟨message, some representative⟩]) saved +
        (1 - boundedRemainingCoveragePotential key cap budget (cache, log ++ [⟨message, some representative⟩])) *
          (expectedPreExceptionCharge (CleanParentSettlement key.parameter key.otsSecret key.ftsSecret) (collisionSigningStructuralCharge key)
            (liftM (signAfterDigest key randomness index leaves)) cache saved.isSome * (Fintype.card Digest : ENNReal)⁻¹) := by
  apply expected_boundedUnionPotential_le_of_right_le
  · exact expected_collisionStructuralRecordPotential_le_preCharge key _ cache hfinite saved
  · intro result hr
    have hfinish : result.1 ∈ support ((simulateQ romImpl
        (liftM (signAfterDigest key randomness index leaves) : OracleComp OracleWorld (Option Signature))).run cache) := by
      rw [← runFirstException_project (CleanParentSettlement key.parameter key.otsSecret key.ftsSecret) _ cache saved, support_map]
      refine ⟨result, ?_, rfl⟩
      rw [mem_support_iff] at hr ⊢
      exact hr
    rw [simulateQ_romImpl_liftM] at hfinish
    exact mul_le_mul' (signAfterDigest_remainingCoveragePotential_le key cap budget randomness index leaves cache result.1.2
      result.1.1 hfinish message log representative hrandomness ∅ Finset.univ (by constructor <;> simp)) le_rfl

noncomputable def digestSelectionCollisionCharge (key : SecretKey) (cap budget : Nat)
    (message : Message) (log : QueryLog SigningSpec)
    (result : Option (Randomness × Index × (DigestTree → FtsLeaf)) × QueryCache HashSpec) : ENNReal :=
  match result.1 with
  | none => 0
  | some (randomness, index, leaves) =>
      (1 - boundedRemainingCoveragePotential key cap budget (digestSelectionCoverageState message log result)) *
        (expectedPreExceptionCharge (CleanParentSettlement key.parameter key.otsSecret key.ftsSecret) (collisionSigningStructuralCharge key)
          (liftM (signAfterDigest key randomness index leaves)) result.2 false * (Fintype.card Digest : ENNReal)⁻¹)

theorem expected_sign_jointRecordPotential_le_digestSelection (key : SecretKey) (cap budget : Nat)
    (message : Message) (cache : QueryCache HashSpec) (hfinite : Finite cache) (log : QueryLog SigningSpec) :
    (∑' result, Pr[= result | runFirstException (CleanParentSettlement key.parameter key.otsSecret key.ftsSecret)
      (sign key message) cache none] *
        jointCollisionCoverageRecordPotential key cap budget (result.1.2, log ++ [⟨message, result.1.1⟩]) result.2) ≤
      ∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache] *
        (jointCollisionCoverageRecordPotential key cap budget (digestSelectionCoverageState message log result) none +
          digestSelectionCollisionCharge key cap budget message log result) := by
  let exception := CleanParentSettlement key.parameter key.otsSecret key.ftsSecret
  rw [sign_eq_digestLoop_afterDigest, runFirstException_bind,
    preservesExceptionRecord_signDigestLoop key exception (fun _ _ _ h => h.2) message digestAttemptLimit cache none,
    bind_map_left, tsum_probOutput_bind_mul]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache)
  · apply mul_le_mul' le_rfl
    have hf := finite_cache_of_mem_support (signDigestLoop digestAttemptLimit key message) cache result.1 result.2 hr hfinite
    rcases result with ⟨selected, after⟩
    cases selected with
    | none =>
        simp only [runFirstException, OracleComp.construct_pure, tsum_probOutput_pure_mul,
          digestSelectionCoverageState, Option.map_none, digestSelectionCollisionCharge, add_zero, le_refl]
    | some data =>
        rcases data with ⟨randomness, index, leaves⟩
        exact expected_signAfterDigest_jointRecordPotential_le key cap budget randomness index leaves after hf none message log
          (coverageSignature randomness) rfl
  · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]

noncomputable def digestSelectionCoverageRisk (key : SecretKey) (cap budget : Nat)
    (message : Message) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec) : ENNReal :=
  ∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache] *
    boundedRemainingCoveragePotential key cap budget (digestSelectionCoverageState message log result)

noncomputable def digestSelectionCollisionRisk (key : SecretKey) (cap budget : Nat)
    (message : Message) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec) : ENNReal :=
  ∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache] *
    digestSelectionCollisionCharge key cap budget message log result

private theorem probOutput_evalDist_eq (computation : ProbComp α) (result : α) :
    Pr[= result | evalDist computation] = Pr[= result | computation] := rfl

private theorem expected_boundedUnionPotential_probComp_le (computation : ProbComp α)
    (left right : α → ENNReal) (beforeLeft beforeRight : ENNReal)
    (hleft : ∀ result ∈ support computation, left result ≤ beforeLeft)
    (hright : (∑' result, Pr[= result | computation] * right result) ≤ beforeRight) :
    (∑' result, Pr[= result | computation] * boundedUnionPotential (left result) (right result)) ≤
      boundedUnionPotential beforeLeft beforeRight := by
  have h := expected_boundedUnionPotential_le_of_left_le (evalDist computation) left right beforeLeft beforeRight
    (fun result hr => hleft result (by rw [mem_support_iff] at hr ⊢; exact hr)) hright
  simpa only [probOutput_evalDist_eq] using h

theorem expected_sign_jointRecordPotential_le_risks (key : SecretKey) (cap budget : Nat)
    (message : Message) (cache : QueryCache HashSpec) (hfinite : Finite cache) (log : QueryLog SigningSpec) :
    (∑' result, Pr[= result | runFirstException (CleanParentSettlement key.parameter key.otsSecret key.ftsSecret)
      (sign key message) cache none] *
        jointCollisionCoverageRecordPotential key cap budget (result.1.2, log ++ [⟨message, result.1.1⟩]) result.2) ≤
      boundedUnionPotential (collisionStructuralRecordPotential key cache none) (digestSelectionCoverageRisk key cap budget message cache log) +
        digestSelectionCollisionRisk key cap budget message cache log := by
  have h := expected_sign_jointRecordPotential_le_digestSelection key cap budget message cache hfinite log
  simp only [mul_add, ENNReal.tsum_add] at h
  apply h.trans
  apply add_le_add ?_ le_rfl
  let computation := (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache
  have hbound := expected_boundedUnionPotential_probComp_le computation
    (fun result => collisionStructuralRecordPotential key result.2 none)
    (fun result => boundedRemainingCoveragePotential key cap budget (digestSelectionCoverageState message log result))
    (collisionStructuralRecordPotential key cache none) (digestSelectionCoverageRisk key cap budget message cache log)
    (fun result hr => signDigestLoop_collisionStructuralRecordPotential_le key message digestAttemptLimit cache result.2 hfinite result.1 hr) (le_refl _)
  apply le_trans ?_ hbound
  apply le_of_eq
  apply tsum_congr
  intro result
  congr 1
  exact (boundedUnionPotential_min_right _ _).symm

end SphincsSecurity.Concrete

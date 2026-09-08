import SphincsSecurity.Proof.SigningFreshEncodingBudget
import SphincsSecurity.Proof.SelectedSigningReserve
import SphincsSecurity.Proof.JointProbeOriginalParentFailure
import SphincsSecurity.Proof.SigningEncodingPairPayment
import SphincsSecurity.Proof.FreshSignerCacheView

namespace SphincsSecurity

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem expectedPreExceptionCharge_bind_add_survival_le
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (left right : QueryCache HashSpec → HashInput → ENNReal)
    (first : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β) (cost : Nat)
    (hcost : PreExceptionSurvivalCost exception right first cost)
    (hnext : ∀ value current currentHit,
      expectedPreExceptionCharge exception left (next value) current currentHit ≤
        expectedPreExceptionCharge exception right (next value) current currentHit)
    (cache : QueryCache HashSpec) (hit : Bool)
    (hzero : expectedPreExceptionCharge exception left first cache hit = 0) :
    expectedPreExceptionCharge exception left (first >>= next) cache hit +
        (cost : ENNReal) * Pr[fun result => result.2 = false | runExceptionMonitor exception (first >>= next) cache hit] ≤
      expectedPreExceptionCharge exception right (first >>= next) cache hit := by
  have hs := (mul_le_mul' le_rfl (probEvent_survival_bind_le exception first next cache hit)).trans (hcost cache hit)
  rw [expectedPreExceptionCharge_bind, expectedPreExceptionCharge_bind, hzero, zero_add, add_comm]
  apply add_le_add hs
  exact ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (hnext result.1.1 result.1.2 result.2)

namespace Concrete.FtsProbeSimulation

attribute [local irreducible] freshEncodingHashCharge

theorem expected_freshEncoding_add_survival_signAfterDigest_le_reserved
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (key : SecretKey) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionCharge exception (freshEncodingHashCharge key.parameter)
        (liftM (signAfterDigest key randomness index leaves)) cache hit +
      (28504 : ENNReal) * Pr[fun result => result.2 = false |
        runExceptionMonitor exception (liftM (signAfterDigest key randomness index leaves)) cache hit] ≤
      expectedPreExceptionCharge exception (nonMessageNonEncodingHashCharge key.parameter)
        (liftM (signAfterDigest key randomness index leaves)) cache hit := by
  rw [signAfterDigest, liftM_bind]
  apply expectedPreExceptionCharge_bind_add_survival_le _ _ _ _ _ 28504
  · intro current currentHit
    exact expected_reserved_ftsOpen_ge_survival exception key.parameter index leaves (key.ftsSecret index) current currentHit
  · intro path current currentHit
    rw [liftM_bind]
    apply expectedPreExceptionCharge_bind_le_bind
    · apply expectedPreExceptionCharge_lift_sequenceFin_le
      intro lay before beforeHit
      exact expectedPreException_freshEncoding_signLayer_le_reserved exception key index lay before beforeHit
    · intro layers _
      split <;> simp
  · exact expectedPreException_freshEncoding_eq_zero_of_avoidsEncoding exception key.parameter _
      (fun f => avoidsEncodingQueries_ftsOpen _ f _ _ _) cache hit

theorem expected_freshEncoding_add_selected_survival_sign_le_reserved
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) (hit : Bool) :
    expectedPreExceptionCharge exception (freshEncodingHashCharge key.parameter) (sign key message) cache hit +
      (28504 : ENNReal) * Pr[fun result => result.1.1.2.isSome ∧ result.2 = false |
        runExceptionMonitor exception (signWithView key message) cache hit] ≤
      expectedPreExceptionCharge exception (nonMessageNonEncodingHashCharge key.parameter) (sign key message) cache hit := by
  rw [← expectedPreExceptionCharge_signWithView_eq_sign exception (freshEncodingHashCharge key.parameter),
    ← expectedPreExceptionCharge_signWithView_eq_sign exception (nonMessageNonEncodingHashCharge key.parameter),
    signWithView, expectedPreExceptionCharge_bind, expectedPreExceptionCharge_bind,
    expectedPreExceptionCharge_eq_zero_of_queryCharge_eq_zero exception _ _ _ _
      (expected_freshEncoding_signDigestLoop_eq_zero key message _ cache), zero_add, runExceptionMonitor_bind]
  apply le_trans ?_ le_add_self
  rw [probEvent_bind_eq_tsum, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro result
  rw [mul_left_comm, ← mul_add]
  apply mul_le_mul' le_rfl
  cases result.1.1 with
  | none => simp [runExceptionMonitor]
  | some data =>
      obtain ⟨randomness, index, leaves⟩ := data
      simp only [bind_pure_comp, expectedPreExceptionCharge_map, runExceptionMonitor_map, probEvent_map,
        Function.comp_def, Option.isSome_some, true_and]
      exact expected_freshEncoding_add_survival_signAfterDigest_le_reserved exception key randomness index leaves result.1.2 result.2

noncomputable def signingSurvivalCredit
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) (hit : Bool) : ENNReal :=
  28504 * Pr[fun result => result.1.1.2.isSome ∧ result.2 = false |
    runExceptionMonitor exception (signWithView key message) cache hit]

theorem expected_encodingPairs_add_survival_sign_le_reserved
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (key : SecretKey) (message : Message) (cap : Nat) (hcapMax : cap ≤ 2 ^ 127)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (hit : Bool)
    (hcap : ∀ result ∈ support ((simulateQ romImpl (sign key message)).run cache), QueryCache.enncard result.2 ≤ cap) :
    expectedPreExceptionCharge exception (encodingPairIncrementCharge key) (sign key message) cache hit +
        signingSurvivalCredit exception key message cache hit ≤
      expectedPreExceptionCharge exception (nonMessageNonEncodingHashCharge key.parameter) (sign key message) cache hit := by
  apply (add_le_add (expectedPreExceptionCharge_mono_of_cache_cap exception _ _ cap
    (fun current hf hc input => encodingPairIncrementCharge_le_freshEncoding key current hf cap hc hcapMax input)
    (sign key message) cache hfinite hit hcap) le_rfl).trans
  exact expected_freshEncoding_add_selected_survival_sign_le_reserved exception key message cache hit

theorem newAdmissible_survival_le_signingSurvivalCredit
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) (hit : Bool) (P : FewTimeView → Prop) :
    (28504 : ENNReal) * Pr[fun result => NewAdmissibleSignerView cache key P result.1 ∧ result.2 = false |
      runExceptionMonitor exception (signWithView key message) cache hit] ≤ signingSurvivalCredit exception key message cache hit := by
  apply mul_le_mul' le_rfl
  apply probEvent_mono
  intro result hr hevent
  obtain ⟨payload, output, hbefore, hafter, hadmissible, _⟩ := hevent.1
  obtain ⟨randomness, index, leaves, loopCache, hloop, hpayload, hview, hselected⟩ :=
    signWithView_new_admissible_selected key message cache result.1.2 result.1.1.1 result.1.1.2
      (runExceptionMonitor_support_project exception (signWithView key message) cache hit hr)
      payload output hbefore hafter hadmissible
  exact ⟨by simp [hview], hevent.2⟩

theorem expected_encodingPairs_add_newAdmissible_survival_sign_le_reserved
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (key : SecretKey) (message : Message) (cap : Nat) (hcapMax : cap ≤ 2 ^ 127)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (hit : Bool) (P : FewTimeView → Prop)
    (hcap : ∀ result ∈ support ((simulateQ romImpl (sign key message)).run cache), QueryCache.enncard result.2 ≤ cap) :
    expectedPreExceptionCharge exception (encodingPairIncrementCharge key) (sign key message) cache hit +
      (28504 : ENNReal) * Pr[fun result => NewAdmissibleSignerView cache key P result.1 ∧ result.2 = false |
        runExceptionMonitor exception (signWithView key message) cache hit] ≤
      expectedPreExceptionCharge exception (nonMessageNonEncodingHashCharge key.parameter) (sign key message) cache hit :=
  (add_le_add le_rfl (newAdmissible_survival_le_signingSurvivalCredit exception key message cache hit P)).trans
    (expected_encodingPairs_add_survival_sign_le_reserved exception key message cap hcapMax cache hfinite hit hcap)

end Concrete.FtsProbeSimulation
end SphincsSecurity

import SphincsSecurity.Proof.JointFailureCacheCap
import SphincsSecurity.Proof.BeforeFailureSigningCharge

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem simulateQ_romImpl_bind_head_cache_cap
    (first : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β)
    (cache : QueryCache HashSpec) (cap : Nat)
    (hcap : ∀ result ∈ support ((simulateQ romImpl (first >>= next)).run cache), QueryCache.enncard result.2 ≤ cap) :
    ∀ middle ∈ support ((simulateQ romImpl first).run cache), QueryCache.enncard middle.2 ≤ cap := by
  intro middle hm
  apply simulateQ_romImpl_initial_cache_bound cap (next middle.1) middle.2
  intro result hr
  apply hcap result
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
  exact ⟨middle, hm, hr⟩

namespace FtsProbeSimulation.JointOriginal

theorem expectedBeforeFailureSigningCharge_mul
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (charge : QueryCache HashSpec → HashInput → ENNReal) (rate : ENNReal)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsProbeSimulation.OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) :
    expectedBeforeFailureSigningCharge exception (fun current input => charge current input * rate)
        parameter root otsTable ftsTable computation frame cache hit failed =
      expectedBeforeFailureSigningCharge exception charge parameter root otsTable ftsTable computation frame cache hit failed * rate := by
  induction computation using OracleComp.inductionOn generalizing frame cache hit failed with
  | pure value => simp
  | query_bind input next ih =>
      rw [expectedBeforeFailureSigningCharge_query_bind, expectedBeforeFailureSigningCharge_query_bind,
        add_mul, ← ENNReal.tsum_mul_right]
      congr 1
      · cases input with
        | inl query => simp only [beforeFailureSigningStepCharge, zero_mul]
        | inr message =>
            cases failed <;> simp only [beforeFailureSigningStepCharge, Bool.false_eq_true, if_false,
              if_true, zero_mul, expectedPreExceptionCharge_mul]
      · apply tsum_congr
        intro result
        rw [ih, mul_assoc]

theorem runWithFailure_original_cache_cap
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsProbeSimulation.OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool)
    (cap : Nat) (hcap : ∀ result ∈ support (runWithFailure exception parameter root otsTable ftsTable computation frame cache hit failed),
      QueryCache.enncard result.1.2.1.2 ≤ cap) :
    ∀ result ∈ support ((simulateQ romImpl (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation)).run cache),
      QueryCache.enncard result.2 ≤ cap := by
  intro actual ha
  have hm : actual ∈ support (evalDist ((simulateQ romImpl
      (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation)).run cache)) :=
    (SPMF.mem_support_iff _ _).2 ((mem_support_iff_evalDist_apply_ne_zero _ _).1 ha)
  rw [← runWithFailure_original_cache_projection exception parameter root otsTable ftsTable computation frame cache hit failed, support_map] at hm
  obtain ⟨result, hr, heq⟩ := hm
  simpa only [← heq] using hcap result hr

theorem runWithFailure_expanded_head_cache_cap
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsProbeSimulation.OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (cache : QueryCache HashSpec) (hit failed : Bool) (cap : Nat)
    (hcap : ∀ result ∈ support (runWithFailure exception parameter root otsTable ftsTable (OracleSpec.query input >>= next) frame cache hit failed),
      QueryCache.enncard result.1.2.1.2 ≤ cap) :
    ∀ result ∈ support ((simulateQ romImpl (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input)).run cache),
      QueryCache.enncard result.2 ≤ cap := by
  have hraw := runWithFailure_original_cache_cap exception parameter root otsTable ftsTable
    (OracleSpec.query input >>= next) frame cache hit failed cap hcap
  have hcomp : simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) (OracleSpec.query input >>= next) =
      expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input >>=
        fun answer => simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) (next answer) := by
    rw [simulateQ_bind, simulateQ_spec_query]
  rw [hcomp] at hraw
  exact simulateQ_romImpl_bind_head_cache_cap _ _ cache cap hraw

private theorem beforeFailureSigningStepCharge_le_of_cache_cap
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (left right : QueryCache HashSpec → HashInput → ENNReal) (cap : Nat)
    (key : SecretKey)
    (hsign : ∀ message current, Finite current → ∀ hit,
      (∀ result ∈ support ((simulateQ romImpl (sign key message)).run current), QueryCache.enncard result.2 ≤ cap) →
      expectedPreExceptionCharge exception left (sign key message) current hit ≤
        expectedPreExceptionCharge exception right (sign key message) current hit)
    (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec) (hfinite : Finite cache) (hit failed : Bool)
    (hcap : ∀ result ∈ support ((simulateQ romImpl (expandedAdversaryImpl key input)).run cache), QueryCache.enncard result.2 ≤ cap) :
    beforeFailureSigningStepCharge exception left key cache hit failed input ≤
      beforeFailureSigningStepCharge exception right key cache hit failed input := by
  cases input with
  | inl query => simp only [beforeFailureSigningStepCharge, le_refl]
  | inr message =>
      simp only [beforeFailureSigningStepCharge]
      cases failed with
      | true => simp
      | false =>
          simp only [Bool.false_eq_true, if_false]
          apply hsign message cache hfinite hit
          simpa only [OracleSpec.Range, OracleSpec.add_apply_inr, expandedAdversaryImpl, scheme] using hcap

theorem expectedBeforeFailureSigningCharge_le_of_cache_cap
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (left right : QueryCache HashSpec → HashInput → ENNReal) (cap : Nat)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsProbeSimulation.OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hsign : ∀ message current, Finite current → ∀ hit,
      (∀ result ∈ support ((simulateQ romImpl (sign (secretKey parameter root otsTable ftsTable) message)).run current),
        QueryCache.enncard result.2 ≤ cap) →
      expectedPreExceptionCharge exception left (sign (secretKey parameter root otsTable ftsTable) message) current hit ≤
        expectedPreExceptionCharge exception right (sign (secretKey parameter root otsTable ftsTable) message) current hit)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (frame : Option Frame) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (hit failed : Bool)
    (hcap : ∀ result ∈ support (runWithFailure exception parameter root otsTable ftsTable computation frame cache hit failed),
      QueryCache.enncard result.1.2.1.2 ≤ cap) :
    expectedBeforeFailureSigningCharge exception left parameter root otsTable ftsTable computation frame cache hit failed ≤
      expectedBeforeFailureSigningCharge exception right parameter root otsTable ftsTable computation frame cache hit failed := by
  induction computation using OracleComp.inductionOn generalizing frame cache hit failed with
  | pure value => simp
  | query_bind input next ih =>
      rw [expectedBeforeFailureSigningCharge_query_bind, expectedBeforeFailureSigningCharge_query_bind]
      apply add_le_add
      · exact beforeFailureSigningStepCharge_le_of_cache_cap exception left right cap
          (secretKey parameter root otsTable ftsTable) hsign input cache hfinite hit failed
          (runWithFailure_expanded_head_cache_cap exception parameter root otsTable ftsTable input next frame cache hit failed cap hcap)
      · apply ENNReal.tsum_le_tsum
        intro result
        by_cases hr : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame cache hit failed)
        · have hm := stepWithFailure_original_support exception parameter root otsTable ftsTable input frame cache hit failed result hr
          have hf := finite_cache_of_mem_support _ cache result.1.2.1.1 result.1.2.1.2
            (runExceptionMonitor_support_project exception _ cache hit hm) hfinite
          exact mul_le_mul' le_rfl (ih result.1.2.1.1 result.1.1 result.1.2.1.2 hf result.1.2.2 result.2
            (runWithFailure_tail_cache_cap exception parameter root otsTable ftsTable input next frame cache hit failed cap hcap result hr))
        · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]

end FtsProbeSimulation.JointOriginal
end SphincsSecurity.Concrete

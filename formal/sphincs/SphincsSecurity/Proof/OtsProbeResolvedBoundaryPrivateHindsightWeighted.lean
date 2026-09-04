import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateHindsightOuter

/-!
# Weight-preserving private hindsight

The fixed-list hindsight theorem is useful only after retaining the probability of producing that
list. This file packages the required fiberwise interface. It deliberately does not permit an
unweighted sum of fixed-list preparation bounds.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp ENNReal

attribute [local instance] Classical.propDecidable

theorem probEvent_eq_tsum_classify_fibers
    {α ι : Type}
    (run : ProbComp α) (event : α → Prop) (classify : α → ι) :
    Pr[event | run] =
      ∑' index, Pr[fun output => event output ∧ classify output = index | run] := by
  classical
  letI : DecidablePred event := Classical.decPred event
  letI : DecidableEq ι := Classical.decEq ι
  rw [probEvent_eq_tsum_ite]
  simp_rw [probEvent_eq_tsum_ite]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro output
  by_cases hevent : event output
  · simp only [hevent, true_and, if_true]
    rw [tsum_eq_single (classify output)]
    · simp
    · intro index hne
      simp [Ne.symm hne]
  · simp [hevent]

theorem probEvent_le_tsum_weighted_fibers
    {α ι : Type}
    (run : ProbComp α) (event : α → Prop) (classify : α → ι)
    (risk : ι → ℝ≥0∞)
    (hfiber : ∀ index,
      Pr[fun output => event output ∧ classify output = index | run] ≤
        Pr[fun output => classify output = index | run] * risk index) :
    Pr[event | run] ≤
      ∑' index, Pr[fun output => classify output = index | run] * risk index := by
  rw [probEvent_eq_tsum_classify_fibers run event classify]
  exact ENNReal.tsum_le_tsum hfiber

theorem probEvent_bind_risk_eq_tsum_weighted_fibers
    {α ι : Type}
    (run : ProbComp α) (classify : α → ι) (risk : ι → ProbComp Bool) :
    Pr[= true | run >>= fun output => risk (classify output)] =
      ∑' index, Pr[fun output => classify output = index | run] *
        Pr[= true | risk index] := by
  classical
  letI : DecidableEq ι := Classical.decEq ι
  rw [← probEvent_eq_eq_probOutput]
  rw [probEvent_bind_eq_tsum]
  have hfiber : ∀ index,
      Pr[fun output => classify output = index | run] =
        ∑' output, if classify output = index then Pr[= output | run] else 0 :=
    fun index => probEvent_eq_tsum_ite run (fun output => classify output = index)
  simp_rw [hfiber, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro output
  rw [tsum_eq_single (classify output)]
  · simp
  · intro index hne
    simp [Ne.symm hne]

theorem probEvent_le_bind_risk_of_weighted_fibers
    {α ι : Type}
    (run : ProbComp α) (event : α → Prop) (classify : α → ι)
    (risk : ι → ProbComp Bool)
    (hfiber : ∀ index,
      Pr[fun output => event output ∧ classify output = index | run] ≤
        Pr[fun output => classify output = index | run] *
          Pr[= true | risk index]) :
    Pr[event | run] ≤
      Pr[= true | run >>= fun output => risk (classify output)] := by
  rw [probEvent_eq_tsum_classify_fibers run event classify]
  calc
    (∑' index,
        Pr[fun output => event output ∧ classify output = index | run]) ≤
        ∑' index, Pr[fun output => classify output = index | run] *
          Pr[= true | risk index] :=
      ENNReal.tsum_le_tsum hfiber
    _ = _ := (probEvent_bind_risk_eq_tsum_weighted_fibers run classify risk).symm

theorem probEvent_privatePlan_le_of_weighted_hindsight
    (run : ProbComp (Bool × List Probe)) (q : Nat)
    (hfiber : ∀ candidates,
      Pr[PlanHitAt candidates | run] ≤
        Pr[fun output => output.2 = candidates | run] *
          Pr[= true | plannedCandidateListFire candidates])
    (hlength : ∀ result ∈ support run, result.2.length ≤ q) :
    Pr[fun result => result.1 = true | run] ≤
      (q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  apply probEvent_privatePlan_le_of_candidate_game run q
  · have hweighted := probEvent_le_bind_risk_of_weighted_fibers run
        (fun result => result.1 = true) Prod.snd plannedCandidateListFire (by
          intro candidates
          change Pr[PlanHitAt candidates | run] ≤ _
          exact hfiber candidates)
    have hcomp :
        (Prod.snd <$> run) >>= plannedCandidateListFire =
          run >>= fun output => plannedCandidateListFire output.2 := by
      simp [map_eq_bind_pure_comp, bind_assoc]
    rw [hcomp]
    exact hweighted
  · exact hlength

end SphincsSecurity.Concrete.OtsProbeSimulation

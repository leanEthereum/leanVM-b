import SphincsSecurity.Proof.CertificateCacheMonitor

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (RetainedRestResult retainedGameRestComputation)
set_option backward.isDefEq.respectTransparency false

private theorem probEvent_pmf_bind_le {α β : Type} (law : PMF α) (next : α → PMF β)
    (event : β → Prop) (bound : ENNReal)
    (hbound : ∀ value ∈ law.support, Pr[event | next value] ≤ bound) :
    Pr[event | law >>= next] ≤ bound := by
  rw [probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' value, Pr[= value | law] * bound := by
      apply ENNReal.tsum_le_tsum
      intro value
      by_cases hv : value ∈ law.support
      · exact mul_le_mul' le_rfl (hbound value hv)
      · have hz : Pr[= value | law] = 0 := by
          rw [PMF.probOutput_eq_apply]
          exact (PMF.apply_eq_zero_iff _ _).mpr hv
        rw [hz, zero_mul, zero_mul]
    _ = bound := by simp only [ENNReal.tsum_mul_right, PMF.probOutput_eq_apply, PMF.tsum_coe, one_mul]

abbrev CertificateCacheGameResult := RetainedRestResult × (List Index × CertificateCacheMonitorState)

def certificateCacheGameProject (result : CertificateCacheGameResult) : CertificateGameResult :=
  (result.1, result.2.1, certificateCacheMonitorProject result.2.2)

noncomputable def certificateCacheGame (adversary : Adversary) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) : PMF CertificateCacheGameResult := do
  let generated ← (liftM (boundaryRun 0 scheme.keygen ∅) : PMF _)
  let key := generated.1.1.2
  (simulateQ (certificateCacheProposalImpl key budget required (stopAfter key))
    (retainedGameRestComputation adversary generated.1.1.1)).run
      ([], generated.2, initialCertificateMonitor generated.1.2.hashCalls stopped, false)

theorem certificateCacheGame_project (adversary : Adversary) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) :
    certificateCacheGameProject <$> certificateCacheGame adversary budget required stopAfter stopped =
      certificateGame adversary budget required stopAfter stopped := by
  rw [certificateCacheGame, map_bind]
  change ((liftM (boundaryRun 0 scheme.keygen ∅) : PMF _) >>= fun generated =>
    Prod.map id (Prod.map id certificateCacheMonitorProject) <$>
      (simulateQ (certificateCacheProposalImpl generated.1.1.2 budget required (stopAfter generated.1.1.2))
        (retainedGameRestComputation adversary generated.1.1.1)).run
        ([], generated.2, initialCertificateMonitor generated.1.2.hashCalls stopped, false)) = _
  simp_rw [simulateQ_certificateCacheProposalImpl_project]
  rfl

theorem certificateCacheGame_original (adversary : Adversary) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) :
    (fun result : CertificateCacheGameResult => (certificateGameVerdict result.1, result.2.2.1)) <$>
      certificateCacheGame adversary budget required stopAfter stopped =
        (liftM ((simulateQ romImpl (gameCore scheme adversary)).run ∅) : PMF _) := by
  calc
    _ = (fun result : CertificateGameResult => (certificateGameVerdict result.1, result.2.2.1)) <$>
        (certificateCacheGameProject <$> certificateCacheGame adversary budget required stopAfter stopped) := by
      rw [Functor.map_map]
      rfl
    _ = _ := by rw [certificateCacheGame_project, certificateGame_original]

theorem probEvent_certificateCacheGame_hit_le (adversary : Adversary) (q : Nat)
    (required : Finset FtsTree) (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool)
    (hbound : HasHashQueryBound scheme adversary q) (hq : q ≤ 2 ^ 127) :
    Pr[fun result => result.2.2.2.2 = true | certificateCacheGame adversary q required stopAfter stopped] ≤
      (q : ENNReal) / 2 ^ 223 + (q : ENNReal) / 2 ^ 170 := by
  rw [certificateCacheGame]
  apply probEvent_pmf_bind_le
  intro generated hg
  change generated ∈ (liftM (boundaryRun 0 scheme.keygen ∅) : PMF _).support at hg
  rw [probCompLift_support] at hg
  have hwhole : (scheme.keygen >>= fun keys => gameRest scheme adversary keys.1 keys.2).IsQueryBoundP
      (· matches .inr _) q := hbound
  have hkeygen := boundaryRun_bind_query_bound 0 scheme.keygen
    (fun keys => gameRest scheme adversary keys.1 keys.2) q hwhole ∅ generated hg
  have hrest := hkeygen.2
  rw [OtsProbeSimulation.gameRest_eq_map_retained, isQueryBoundP_map_iff] at hrest
  have hrestBudget :
      (simulateQ (expandedAdversaryImpl generated.1.1.2)
        (retainedGameRestComputation adversary generated.1.1.1)).IsQueryBoundP (· matches .inr _) q :=
    OracleComp.IsQueryBoundP.mono hrest (Nat.sub_le _ _)
  have hfinite := boundaryRun_cache_finite 0 scheme.keygen ∅ finite_empty generated hg
  have hgenerated : (generated.1.1, generated.2) ∈ support ((simulateQ romImpl scheme.keygen).run ∅) := by
    rw [← boundaryRun_forget 0 scheme.keygen ∅, support_map]
    exact ⟨generated, hg, rfl⟩
  have hnone := keygen_cache_message_none (generated.1.1, generated.2) hgenerated
  exact (probEvent_certificateCacheProposal_hit_le generated.1.1.2 q required (stopAfter generated.1.1.2)
    (retainedGameRestComputation adversary generated.1.1.1) q hrestBudget
    ([], generated.2, initialCertificateMonitor generated.1.2.hashCalls stopped, false) hfinite).trans
      (certificateCacheExceptionPotential_initial_le generated.1.1.2 q hq generated.2 hnone)

end SphincsSecurity.Concrete

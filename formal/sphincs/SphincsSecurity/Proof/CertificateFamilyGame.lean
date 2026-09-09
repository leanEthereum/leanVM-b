import SphincsSecurity.Proof.CertificateMonitorCore

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (RetainedRestResult retainedGameRestComputation)
set_option backward.isDefEq.respectTransparency false

noncomputable def certificateFamilyImpl (key : SecretKey) (budget : Nat)
    (stopAfter : CertificateCoreStopRule) :
    QueryImpl (OracleWorld + SigningSpec) (StateT (List Index × CertificateFamilyState) PMF) :=
  originalProposalImpl key (fun state => state.2.core.spent)
    (fun message state => certificateMonitorEnabled key budget message
      (certificateCacheMonitorProject (certificateFamilyProject none state)))
    (certificateFamilyUpdate key budget stopAfter)

theorem certificateFamilyImpl_project (key : SecretKey) (budget : Nat)
    (stopAfter : CertificateCoreStopRule) (input : (OracleWorld + SigningSpec).Domain)
    (state : List Index × CertificateFamilyState) (index : Option FtsTree) :
    Prod.map id (Prod.map id (certificateFamilyProject index)) <$>
      (certificateFamilyImpl key budget stopAfter input).run state =
        (certificateCacheProposalImpl key budget (certificateRequiredTrees index)
          (certificateCoreStop stopAfter) input).run (state.1, certificateFamilyProject index state.2) := by
  change PMF.map _ _ = _
  cases input with
  | inl world =>
      simp only [certificateFamilyImpl, certificateCacheProposalImpl, originalProposalImpl, proposalRecordImpl,
        StateT.run_mk, originalProposalActive, Bool.false_eq_true, if_false, PMF.map_comp]
      congr 1
      funext record
      exact congrArg (fun after => (record.output, state.1, after))
        (certificateFamilyUpdate_project key budget stopAfter (.inl world) state.2 0 record index)
  | inr message =>
      simp only [certificateFamilyImpl, certificateCacheProposalImpl, originalProposalImpl, proposalRecordImpl,
        StateT.run_mk, originalProposalActive, originalRejectedProposal,
        certificateFamilyProject, certificateCacheMonitorProject, CertificateCore.attach,
        certificateMonitorEnabled, CertificateMonitorActive, CertificateMonitorReady]
      split <;> simp only [PMF.map_comp]
      · congr 1
        funext source
        exact congrArg (fun after => (source.2.output, state.1 ++ source.1 ++ [source.2.index], after))
          (certificateFamilyUpdate_project key budget stopAfter (.inr message) state.2
            (source.1.length + 1) source.2 index)
      · congr 1
        funext record
        exact congrArg (fun after => (record.output, state.1, after))
          (certificateFamilyUpdate_project key budget stopAfter (.inr message) state.2 0 record index)

theorem simulateQ_certificateFamilyImpl_project {α : Type} (key : SecretKey) (budget : Nat)
    (stopAfter : CertificateCoreStopRule) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : List Index × CertificateFamilyState) (index : Option FtsTree) :
    Prod.map id (Prod.map id (certificateFamilyProject index)) <$>
      (simulateQ (certificateFamilyImpl key budget stopAfter) computation).run state =
        (simulateQ (certificateCacheProposalImpl key budget (certificateRequiredTrees index)
          (certificateCoreStop stopAfter)) computation).run (state.1, certificateFamilyProject index state.2) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ (Prod.map id (certificateFamilyProject index))
    (fun input state => certificateFamilyImpl_project key budget stopAfter input state index) computation state

abbrev CertificateFamilyGameResult := RetainedRestResult × (List Index × CertificateFamilyState)

def certificateFamilyGameProject (index : Option FtsTree) (result : CertificateFamilyGameResult) :
    CertificateCacheGameResult :=
  (result.1, result.2.1, certificateFamilyProject index result.2.2)

noncomputable def certificateFamilyGame (adversary : Adversary) (budget : Nat)
    (stopAfter : SecretKey → CertificateCoreStopRule) (stopped : Bool) : PMF CertificateFamilyGameResult := do
  let generated ← (liftM (boundaryRun 0 scheme.keygen ∅) : PMF _)
  (simulateQ (certificateFamilyImpl generated.1.1.2 budget (stopAfter generated.1.1.2))
    (retainedGameRestComputation adversary generated.1.1.1)).run
      ([], generated.2, initialCertificateFamilyMonitor generated.1.2.hashCalls stopped)

theorem certificateFamilyGame_project (adversary : Adversary) (budget : Nat)
    (stopAfter : SecretKey → CertificateCoreStopRule) (stopped : Bool) (index : Option FtsTree) :
    certificateFamilyGameProject index <$> certificateFamilyGame adversary budget stopAfter stopped =
      certificateCacheGame adversary budget (certificateRequiredTrees index)
        (fun key => certificateCoreStop (stopAfter key)) stopped := by
  rw [certificateFamilyGame, map_bind]
  change ((liftM (boundaryRun 0 scheme.keygen ∅) : PMF _) >>= fun generated =>
    Prod.map id (Prod.map id (certificateFamilyProject index)) <$>
      (simulateQ (certificateFamilyImpl generated.1.1.2 budget (stopAfter generated.1.1.2))
        (retainedGameRestComputation adversary generated.1.1.1)).run
        ([], generated.2, initialCertificateFamilyMonitor generated.1.2.hashCalls stopped)) = _
  simp_rw [simulateQ_certificateFamilyImpl_project, certificateFamilyProject_initial]
  rfl

theorem certificateFamilyGame_original (adversary : Adversary) (budget : Nat)
    (stopAfter : SecretKey → CertificateCoreStopRule) (stopped : Bool) :
    (fun result : CertificateFamilyGameResult => (certificateGameVerdict result.1, result.2.2.1)) <$>
      certificateFamilyGame adversary budget stopAfter stopped =
        (liftM ((simulateQ romImpl (gameCore scheme adversary)).run ∅) : PMF _) := by
  calc
    _ = (fun result : CertificateCacheGameResult => (certificateGameVerdict result.1, result.2.2.1)) <$>
        (certificateFamilyGameProject none <$> certificateFamilyGame adversary budget stopAfter stopped) := by
      rw [Functor.map_map]
      rfl
    _ = _ := by rw [certificateFamilyGame_project, certificateCacheGame_original]

theorem expected_certificateFamilyGame_project (adversary : Adversary) (budget : Nat)
    (stopAfter : SecretKey → CertificateCoreStopRule) (stopped : Bool) (index : Option FtsTree)
    (weight : CertificateCacheGameResult → ENNReal) :
    (∑' result, Pr[= result | certificateFamilyGame adversary budget stopAfter stopped] *
      weight (certificateFamilyGameProject index result)) =
        ∑' result, Pr[= result | certificateCacheGame adversary budget (certificateRequiredTrees index)
          (fun key => certificateCoreStop (stopAfter key)) stopped] * weight result := by
  have h := congrArg (fun law : PMF CertificateCacheGameResult => ∑' result, Pr[= result | law] * weight result)
    (certificateFamilyGame_project adversary budget stopAfter stopped index)
  rw [tsum_probOutput_map_mul] at h
  exact h

end SphincsSecurity.Concrete

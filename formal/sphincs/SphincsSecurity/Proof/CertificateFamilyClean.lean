import SphincsSecurity.Proof.CertificateFamilyCoverage

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (retainedGameRestComputation)
set_option backward.isDefEq.respectTransparency false

def CertificateFamilyExceptional (result : CertificateFamilyGameResult) : Prop :=
  result.2.2.2.cacheHit = true ∨
    ProposalPrefixExceptional result.2.2.2.core.proposals result.2.2.2.core.log.length

theorem certificateFamilyExceptional_project (index : Option FtsTree) (result : CertificateFamilyGameResult) :
    CertificateGameExceptional (certificateFamilyGameProject index result) ↔ CertificateFamilyExceptional result := Iff.rfl

theorem probEvent_certificateFamilyExceptional_le (adversary : Adversary) (q : Nat)
    (stopAfter : SecretKey → CertificateCoreStopRule) (stopped : Bool)
    (hbound : HasHashQueryBound scheme adversary q) (hq : q ≤ 2 ^ 127) :
    Pr[CertificateFamilyExceptional | certificateFamilyGame adversary q stopAfter stopped] ≤
      (q : ENNReal) / 2 ^ 223 + (q : ENNReal) / 2 ^ 170 + (2 ^ 704 : ENNReal)⁻¹ := by
  have h := congrArg (fun law : PMF CertificateCacheGameResult => Pr[CertificateGameExceptional | law])
    (certificateFamilyGame_project adversary q stopAfter stopped none)
  rw [probEvent_map] at h
  exact h.trans_le (probEvent_certificateGameExceptional_le adversary q (certificateRequiredTrees none)
    (fun key => certificateCoreStop (stopAfter key)) stopped hbound hq)

theorem certificateCoreStop_guard_false :
    certificateCoreStop (certificateCoreGuard (fun _ _ _ _ => false)) = proposalPrefixStop := by
  rw [certificateCoreStop_guard]
  funext input state length record
  simp only [certificateCoreStop, Bool.or_false]

theorem certificateFamilyGame_clean (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (hq : q ≤ 2 ^ 127)
    (result : CertificateFamilyGameResult)
    (hr : result ∈ (certificateFamilyGame adversary q
      (fun _ => certificateCoreGuard (fun _ _ _ _ => false)) false).support)
    (hvalid : SigningTranscript.Valid result.1.1.2) (hclean : ¬ CertificateFamilyExceptional result) :
    result.2.2.2.core.stopped = false ∧ result.2.2.2.core.log = result.1.1.2 := by
  have hm := (PMF.mem_support_map_iff (certificateFamilyGameProject none) _ _).mpr ⟨result, hr, rfl⟩
  rw [← PMF.monad_map_eq_map, certificateFamilyGame_project, certificateCoreStop_guard_false] at hm
  exact certificateCacheGame_clean adversary q (certificateRequiredTrees none) hbound hq
    (certificateFamilyGameProject none result) hm hvalid hclean

theorem forgeAdvantage_le_certificateFamilyGame_live_add (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (hq : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary ≤
      Pr[fun result => certificateGameVerdict result.1 = true ∧ result.2.2.2.core.stopped = false ∧
        result.2.2.2.core.log = result.1.1.2 ∧ ¬ CertificateFamilyExceptional result |
          certificateFamilyGame adversary q (fun _ => certificateCoreGuard (fun _ _ _ _ => false)) false] +
        ((q : ENNReal) / 2 ^ 223 + (q : ENNReal) / 2 ^ 170 + (2 ^ 704 : ENNReal)⁻¹) := by
  have h := congrArg (fun law : PMF CertificateCacheGameResult =>
    Pr[fun result => certificateGameVerdict result.1 = true ∧ result.2.2.2.1.stopped = false ∧
      result.2.2.2.1.log = result.1.1.2 ∧ ¬ CertificateGameExceptional result | law])
      (certificateFamilyGame_project adversary q
        (fun _ => certificateCoreGuard (fun _ _ _ _ => false)) false none)
  rw [probEvent_map, certificateCoreStop_guard_false] at h
  change Pr[fun result => certificateGameVerdict result.1 = true ∧ result.2.2.2.core.stopped = false ∧
    result.2.2.2.core.log = result.1.1.2 ∧ ¬ CertificateFamilyExceptional result |
      certificateFamilyGame adversary q (fun _ => certificateCoreGuard (fun _ _ _ _ => false)) false] = _ at h
  rw [h]
  exact forgeAdvantage_le_certificateCacheGame_live_add adversary q (certificateRequiredTrees none) hbound hq

theorem certificateFamily_rest_clean_certificate (adversary : Adversary) (publicKey : PublicKey)
    (key : SecretKey) (budget q spent : Nat) (index : Option FtsTree) (hbudget : budget ≤ 2 ^ 127)
    (hbound : (simulateQ (expandedAdversaryImpl key)
      (retainedGameRestComputation adversary publicKey)).IsQueryBoundP (· matches .inr _) q)
    (cache : QueryCache HashSpec) (hroom : spent + q ≤ budget)
    (hcache : QueryCache.enncard cache ≤ spent)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none)
    (result : CertificateFamilyGameResult)
    (hr : result ∈ ((simulateQ (certificateFamilyImpl key budget
      (certificateCoreGuard (fun _ _ _ _ => false))) (retainedGameRestComputation adversary publicKey)).run
        ([], cache, initialCertificateFamilyMonitor spent false)).support)
    (hvalid : SigningTranscript.Valid result.1.1.2) (hclean : ¬ CertificateFamilyExceptional result)
    (input : HashInput)
    (hcertificate : TargetCertificateAt key (certificateRequiredTrees index) (result.2.2.1, result.1.1.2) input) :
    1 ≤ certificateBankCount (result.2.2.2.ledger index).bank := by
  have hm := (PMF.mem_support_map_iff (Prod.map id (Prod.map id (certificateFamilyProject index))) _ _).mpr
    ⟨result, hr, rfl⟩
  rw [← PMF.monad_map_eq_map, simulateQ_certificateFamilyImpl_project,
    certificateCoreStop_guard_false, certificateFamilyProject_initial] at hm
  exact certificateCacheProposal_rest_clean_certificate adversary publicKey key budget q spent
    (certificateRequiredTrees index) hbudget hbound cache hroom hcache hnone
    (certificateFamilyGameProject index result) hm hvalid hclean input hcertificate

end SphincsSecurity.Concrete

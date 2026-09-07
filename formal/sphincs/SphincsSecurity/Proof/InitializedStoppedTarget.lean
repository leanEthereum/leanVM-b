import SphincsSecurity.Proof.StoppedRetainedCoverage
import SphincsSecurity.Proof.SecuritySigningReserve

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
set_option backward.isDefEq.respectTransparency false

theorem initialized_stoppedTarget_conditions
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hp : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat)
    (initial : Option Frame × (Digest × QueryCache HashSpec))
    (hi : initial ∈ support (initializeRoot parameter otsTable ftsTable q fuel)) :
    (∀ input, MessageHashInput parameter input → initial.2.2 input = none) ∧
      (∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl (secretKey parameter initial.2.1 otsTable ftsTable))
        (unloggedRetainedRestComputation adversary ⟨initial.2.1, parameter⟩)).run (initial.2.2, [])), QueryCache.enncard result.2.1 ≤ q) := by
  let key := secretKey parameter initial.2.1 otsTable ftsTable
  have hroot := initializeRoot_original_support parameter otsTable ftsTable q fuel initial hi
  rw [originalRoot, simulateQ_romImpl_liftM] at hroot
  have hgame := isQueryBoundP_gameAfterSecrets adversary q hq hp
    (OtsProbeSimulation.mem_support_sampleOtsSecrets_all key.otsSecret) hfts
  constructor
  · intro input hmessage
    obtain ⟨payload, rfl⟩ := hmessage
    exact treeRoot_cache_message_none parameter topLayer rootTree (key.otsSecret topLayer rootTree)
      initial.2.1 initial.2.2 hroot payload
  · exact retainedRoot_rest_cache_bound adversary parameter key.otsSecret ftsTable q hgame initial.2 hroot

noncomputable def initializedStoppedTargetCharge (adversary : Adversary) (parameter : PublicParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q fuel : Nat) : ENNReal :=
  ∑' initial, Pr[= initial | initializeRoot parameter otsTable ftsTable q fuel] *
    (expectedStoppedIndexCharge (parentException parameter otsTable ftsTable) parameter initial.2.1 otsTable ftsTable q
      (targetArrivalHashCost parameter) ∅ Finset.univ (unloggedRetainedRestComputation adversary ⟨initial.2.1, parameter⟩)
      initial.1 (initial.2.2, []) false initial.1.isNone * ((2 ^ 176 : Nat) : ENNReal)⁻¹)

theorem probEvent_liveNonSecretResidual_le_initialized_stopped_arrival
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127)
    (parameter : PublicParameter) (hp : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    Pr[LiveNonSecretResidual parameter otsTable ftsTable |
      runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] ≤
      initializedStoppedTargetCharge adversary parameter otsTable ftsTable q fuel := by
  apply le_trans (probEvent_mono (q := fun result => result.1.2.2 = false ∧ result.2 = false ∧
    ∃ value, result.1.2.1.1 = some value ∧ ObservedRetainedCover value (messageAnswers parameter result.1.2.1.2))
    (fun result hr hres => ⟨hres.2.1, hres.1,
      liveNonSecretResidual_observed adversary q hq parameter hp otsTable ftsTable hfts fuel result hr hres⟩))
  rw [runRetainedWithFailure, probEvent_bind_eq_tsum, initializedStoppedTargetCharge]
  apply ENNReal.tsum_le_tsum
  intro initial
  by_cases hi : initial ∈ support (initializeRoot parameter otsTable ftsTable q fuel)
  · have hconditions := initialized_stoppedTarget_conditions adversary q hq parameter hp otsTable ftsTable hfts fuel initial hi
    have hbound := OtsProbeSimulation.isQueryBoundP_expandedRetained_all_tables_roots adversary q hq parameter hp otsTable
      (fun index tree leaf => ftsTable (index, tree, leaf)) hfts initial.2.1
    exact mul_le_mul' le_rfl (probEvent_retained_liveObservedCover_le_stopped_arrival (parentException parameter otsTable ftsTable)
      adversary parameter initial.2.1 otsTable ftsTable q hqMax hbound initial.1 initial.2.2 false initial.1.isNone hconditions.1 hconditions.2)
  · rw [probOutput_eq_zero_of_not_mem_support hi, zero_mul, zero_mul]

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

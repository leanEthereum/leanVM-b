import SphincsSecurity.Proof.OtsProbeDiagnosticClassification125
import SphincsSecurity.Proof.OtsProbeFinalization125

namespace SphincsSecurity.Concrete.OtsProbeSimulation.Range125

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedPublishedTreeRoot

set_option linter.constructorNameAsVariable false

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem probEvent_sampledDiagnostic_successfulDoomed_firstHit_eq_zero_of_q_le_ordinal
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q ordinal : Nat)
    (hexpanded : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
            SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ 125)
    (hordinal : q ≤ ordinal) :
    Pr[fun outcome => outcome.SuccessfulDoomed ∧
          outcome.FirstExistingHiddenHitAt ordinal |
        sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] = 0 := by
  apply le_antisymm
  · calc
      _ ≤ Pr[ObservedCleanRunOption.SuccessfulFirstExistingHiddenHitAt ordinal | do
            let table ← sampleOtsHashTable
            observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q)
              table] :=
        probEvent_sampledDiagnostic_successfulDoomed_firstExistingHiddenHitAt_le_raw adversary
          parameter ftsSecret (2 * q) ordinal
      _ ≤ Pr[fun source => SelectedPrivateSnapshotHitAt source ordinal |
            sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] :=
        probEvent_sampledSuccessfulFirstHit_le_selectedSnapshot adversary parameter ftsSecret q
          ordinal hexpanded hq
      _ = 0 := probEvent_selectedPrivateSnapshotHitAt_eq_zero_of_q_le_ordinal adversary
        parameter ftsSecret q ordinal hexpanded hordinal
  · exact zero_le

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem probEvent_sampledDiagnostic_successfulDoomed_firstRoot_eq_zero_of_q_le_ordinal
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q ordinal : Nat)
    (hexpanded : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
            SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ 125)
    (hordinal : q ≤ ordinal) :
    Pr[fun outcome => outcome.SuccessfulDoomed ∧
          outcome.FirstExistingHiddenRootHitAt ordinal |
        sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] = 0 := by
  apply le_antisymm
  · calc
      _ ≤ Pr[fun outcome => outcome.SuccessfulDoomed ∧
            outcome.FirstExistingHiddenHitAt ordinal |
          sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] := by
        apply probEvent_mono
        intro outcome _houtcome hevent
        exact ⟨hevent.1, outcome.firstExistingHiddenHitAt_of_root hevent.2⟩
      _ = 0 :=
        probEvent_sampledDiagnostic_successfulDoomed_firstHit_eq_zero_of_q_le_ordinal
          adversary parameter ftsSecret q ordinal hexpanded hq hordinal
  · exact zero_le

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem probEvent_sampledDiagnostic_successfulDoomed_firstNonRoot_eq_zero_of_q_le_ordinal
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q ordinal : Nat)
    (hexpanded : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
            SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ 125)
    (hordinal : q ≤ ordinal) :
    Pr[fun outcome => outcome.SuccessfulDoomed ∧
          outcome.FirstExistingHiddenNonRootHitAt ordinal |
        sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] = 0 := by
  apply le_antisymm
  · calc
      _ ≤ Pr[fun outcome => outcome.SuccessfulDoomed ∧
            outcome.FirstExistingHiddenHitAt ordinal |
          sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] := by
        apply probEvent_mono
        intro outcome _houtcome hevent
        exact ⟨hevent.1, outcome.firstExistingHiddenHitAt_of_nonRoot hevent.2⟩
      _ = 0 :=
        probEvent_sampledDiagnostic_successfulDoomed_firstHit_eq_zero_of_q_le_ordinal
          adversary parameter ftsSecret q ordinal hexpanded hq hordinal
  · exact zero_le

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem probEvent_sampledDiagnostic_successfulDoomed_le_fifteen_sevenths_mul
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hfuel : 2 * q < Fintype.card Digest)
    (hexpanded : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
            SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ 125) :
    Pr[ObservedMaterializedDiagnostic.SuccessfulDoomed |
        sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] ≤
      ((15 / 7 : ENNReal) * q) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  classical
  let diagnostic :=
    sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)
  let epsilon := ((2 ^ digestBits : Nat) : ENNReal)⁻¹
  calc
    _ ≤ ∑ ordinal : Fin (2 * q),
        (Pr[fun outcome => outcome.SuccessfulDoomed ∧
              outcome.FirstExistingHiddenRootHitAt ordinal.val | diagnostic] +
          Pr[fun outcome => outcome.SuccessfulDoomed ∧
              outcome.FirstExistingHiddenNonRootHitAt ordinal.val | diagnostic]) :=
      probEvent_sampledDiagnostic_successfulDoomed_le_sum_successfulFirstOrdinals adversary
        parameter ftsSecret q hq
    _ ≤ ∑ _ordinal : Fin q, (15 / 7) * epsilon := by
      simp only [Finset.sum_fin_eq_sum_range]
      rw [show 2 * q = q + q by omega, Finset.sum_range_add]
      have hfirst :
          (∑ ordinal ∈ Finset.range q, if h : ordinal < q + q then
              (Pr[fun outcome => outcome.SuccessfulDoomed ∧
                    outcome.FirstExistingHiddenRootHitAt ordinal | diagnostic] +
                Pr[fun outcome => outcome.SuccessfulDoomed ∧
                    outcome.FirstExistingHiddenNonRootHitAt ordinal | diagnostic])
            else 0) ≤
            ∑ _ordinal ∈ Finset.range q, (15 / 7) * epsilon := by
        apply Finset.sum_le_sum
        intro ordinal hordinalMem
        have hordinal : ordinal < q := Finset.mem_range.1 hordinalMem
        have hordinal' : ordinal < q + q := hordinal.trans_le (Nat.le_add_right q q)
        simp only [hordinal', ↓reduceDIte]
        calc
          _ ≤ (8 / 7) * epsilon + epsilon := add_le_add
            (probEvent_sampledDiagnostic_successfulDoomed_firstRoot_le ordinal adversary
              parameter ftsSecret q hordinal hfuel hexpanded hq)
            (probEvent_sampledDiagnostic_successfulDoomed_firstNonRoot_le adversary parameter
              ftsSecret q ordinal hexpanded hq)
          _ = (15 / 7) * epsilon := by
            rw [← add_one_mul]
            have hcoeff : (8 / 7 : ENNReal) + 1 = 15 / 7 := by
              apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
              rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
              norm_num
            rw [hcoeff]
      have hzero :
          (∑ ordinal ∈ Finset.range q, if h : q + ordinal < q + q then
              (Pr[fun outcome => outcome.SuccessfulDoomed ∧
                    outcome.FirstExistingHiddenRootHitAt (q + ordinal) | diagnostic] +
                Pr[fun outcome => outcome.SuccessfulDoomed ∧
                    outcome.FirstExistingHiddenNonRootHitAt (q + ordinal) | diagnostic])
            else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro ordinal hordinalMem
        have hordinal : ordinal < q := Finset.mem_range.1 hordinalMem
        simp only [show q + ordinal < q + q by omega, ↓reduceDIte]
        rw [probEvent_sampledDiagnostic_successfulDoomed_firstRoot_eq_zero_of_q_le_ordinal
          adversary parameter ftsSecret q (q + ordinal) hexpanded hq (by omega)]
        rw [probEvent_sampledDiagnostic_successfulDoomed_firstNonRoot_eq_zero_of_q_le_ordinal
          adversary parameter ftsSecret q (q + ordinal) hexpanded hq (by omega)]
        simp
      calc
        _ ≤ (∑ _ordinal ∈ Finset.range q, (15 / 7) * epsilon) +
              (∑ ordinal ∈ Finset.range q, if h : q + ordinal < q + q then
                (Pr[fun outcome => outcome.SuccessfulDoomed ∧
                      outcome.FirstExistingHiddenRootHitAt (q + ordinal) | diagnostic] +
                  Pr[fun outcome => outcome.SuccessfulDoomed ∧
                      outcome.FirstExistingHiddenNonRootHitAt (q + ordinal) | diagnostic])
              else 0) := add_le_add hfirst le_rfl
        _ = ∑ _ordinal ∈ Finset.range q, (15 / 7) * epsilon := by rw [hzero, add_zero]
        _ = ∑ ordinal ∈ Finset.range q, if h : ordinal < q then (15 / 7) * epsilon else 0 := by
          apply Finset.sum_congr rfl
          intro ordinal hordinalMem
          simp [Finset.mem_range.1 hordinalMem]
    _ = (q : ENNReal) * ((15 / 7) * epsilon) := by simp
    _ = _ := by
      simp only [epsilon]
      push_cast
      ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem probEvent_sampledDiagnostic_bad_le_twenty_two_sevenths_mul
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hfuel : 2 * q < Fintype.card Digest)
    (hexpanded : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
            SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ 125) :
    Pr[ObservedMaterializedDiagnostic.Bad |
        sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] ≤
      ((22 / 7 : ENNReal) * q) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  let diagnostic :=
    sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)
  calc
    _ ≤ Pr[fun outcome => outcome.final = none | diagnostic] +
          Pr[ObservedMaterializedDiagnostic.SuccessfulDoomed | diagnostic] :=
      probEvent_diagnosticBad_le_finalNone_add_successfulDoomed diagnostic
    _ ≤ (q : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
          ((15 / 7 : ENNReal) * q) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
      apply add_le_add
      · exact probEvent_sampledDiagnostic_final_none_le_queryBound adversary parameter
          ftsSecret (2 * q) q hexpanded (by omega)
      · exact probEvent_sampledDiagnostic_successfulDoomed_le_fifteen_sevenths_mul adversary parameter
          ftsSecret q hfuel hexpanded hq
    _ = _ := by
      rw [← add_mul, ← one_add_mul]
      have hcoeff : (1 : ENNReal) + 15 / 7 = 22 / 7 := by
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
        norm_num
      rw [hcoeff]

end SphincsSecurity.Concrete.OtsProbeSimulation.Range125

import SphincsSecurity.Proof.OtsProbeSelectionSchedule125

namespace SphincsSecurity.Concrete.OtsProbeSimulation.Range125

open OracleComp OracleSpec ENNReal

attribute [local irreducible] maskedPublishedTreeRoot

set_option maxRecDepth 100000 in
theorem probEvent_diagnosticNonRoot_le_common_mass
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hordinal : ordinal < q)
    (hbound : ∀ root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ 125) :
    Pr[ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenNonRootHitAt table ordinal |
      observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table] ≤
    Pr[PermissiveSelectionNonRoot |
      permissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter ftsSecret
        (2 * q) table] * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  apply (probEvent_observedMaterialized_successfulDoomed_firstNonRoot_le_selectedNonRoot
    adversary parameter ftsSecret q ordinal table hbound hq).trans
  apply (probEvent_granularAllCanonical_nonRoot_le_selectionFire ordinal adversary parameter
    table ftsSecret q).trans
  apply (probEvent_selectionNonRootFire_le_selected_mass _
    (privateOrdinalSelectionFresh_of_mem_granularAllCanonical ordinal adversary parameter
      table ftsSecret q)).trans
  apply mul_le_mul' _ le_rfl
  exact (probEvent_canonicalNonRootSelection_le_delayedCommon ordinal adversary parameter
    table ftsSecret q).trans
    (probEvent_delayedCommon_nonRoot_le_rootAwareCommon ordinal adversary parameter ftsSecret
      q (2 * q) table hordinal (by omega))

set_option maxRecDepth 100000 in
theorem probEvent_diagnosticRawOrdinal_pair_le_eight_sevenths
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hordinal : ordinal < q)
    (hfuel : 2 * q < Fintype.card Digest)
    (hbound : ∀ root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ 125) :
    Pr[ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt table ordinal |
      observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table] +
    Pr[ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenNonRootHitAt table ordinal |
      observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table] ≤
    (8 / 7 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  let common := permissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
    ftsSecret (2 * q) table
  let rootMass := Pr[fun selection =>
    (permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection).isSome = true | common]
  let nonRootMass := Pr[PermissiveSelectionNonRoot | common]
  let epsilon := ((2 ^ digestBits : Nat) : ENNReal)⁻¹
  have hroot := probEvent_successfulDoomedFirstRoot_le_selected_mass ordinal adversary parameter
    table ftsSecret q hordinal hfuel hbound hq
  have hnonRoot := probEvent_diagnosticNonRoot_le_common_mass ordinal adversary parameter
    table ftsSecret q hordinal hbound hq
  have hcoefficient : epsilon ≤ (8 / 7 : ENNReal) * epsilon := by
    calc
      epsilon = 1 * epsilon := (one_mul _).symm
      _ ≤ _ := mul_le_mul' (by
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        norm_num) le_rfl
  calc
    _ ≤ rootMass * ((8 / 7) * epsilon) + nonRootMass * epsilon :=
      add_le_add hroot hnonRoot
    _ ≤ rootMass * ((8 / 7) * epsilon) + nonRootMass * ((8 / 7) * epsilon) :=
      add_le_add le_rfl (mul_le_mul' le_rfl hcoefficient)
    _ = (rootMass + nonRootMass) * ((8 / 7) * epsilon) := (add_mul ..).symm
    _ ≤ 1 * ((8 / 7) * epsilon) :=
      mul_le_mul' (rootSelection_nonRootSelection_mass_le_one common) le_rfl
    _ = _ := one_mul _

set_option maxRecDepth 100000 in
theorem probEvent_sampledDiagnosticOrdinal_pair_le_eight_sevenths
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hordinal : ordinal < q) (hfuel : 2 * q < Fintype.card Digest)
    (hbound : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ 125) :
    Pr[fun outcome => outcome.SuccessfulDoomed ∧ outcome.FirstExistingHiddenRootHitAt ordinal |
      sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] +
    Pr[fun outcome => outcome.SuccessfulDoomed ∧ outcome.FirstExistingHiddenNonRootHitAt ordinal |
      sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] ≤
    (8 / 7 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  let epsilon := (8 / 7 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹
  unfold sampledObservedMaterializedDiagnostic
  simp only [probEvent_bind_eq_tsum sampleOtsHashTable, ← ENNReal.tsum_add, ← mul_add]
  calc
    _ ≤ ∑' table, Pr[= table | sampleOtsHashTable] * epsilon := by
      apply ENNReal.tsum_le_tsum
      intro table
      apply mul_le_mul' le_rfl
      apply (add_le_add
        (probEvent_finishDiagnostic_successfulDoomed_firstExistingHiddenRootHitAt_le table
          (observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table)
          ordinal)
        (probEvent_finishDiagnostic_successfulDoomed_firstExistingHiddenNonRootHitAt_le table
          (observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table)
          ordinal)).trans
      exact probEvent_diagnosticRawOrdinal_pair_le_eight_sevenths ordinal adversary parameter
        table ftsSecret q hordinal hfuel (hbound table) hq
    _ = (∑' table, Pr[= table | sampleOtsHashTable]) * epsilon := ENNReal.tsum_mul_right
    _ ≤ 1 * epsilon := mul_le_mul' tsum_probOutput_le_one le_rfl
    _ = _ := one_mul _

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem probEvent_sampledDiagnostic_successfulDoomed_le_eight_sevenths_mul
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
      ((8 / 7 : ENNReal) * q) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
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
    _ ≤ ∑ _ordinal : Fin q, (8 / 7) * epsilon := by
      simp only [Finset.sum_fin_eq_sum_range]
      rw [show 2 * q = q + q by omega, Finset.sum_range_add]
      have hfirst :
          (∑ ordinal ∈ Finset.range q, if h : ordinal < q + q then
              (Pr[fun outcome => outcome.SuccessfulDoomed ∧
                    outcome.FirstExistingHiddenRootHitAt ordinal | diagnostic] +
                Pr[fun outcome => outcome.SuccessfulDoomed ∧
                    outcome.FirstExistingHiddenNonRootHitAt ordinal | diagnostic])
            else 0) ≤
            ∑ _ordinal ∈ Finset.range q, (8 / 7) * epsilon := by
        apply Finset.sum_le_sum
        intro ordinal hordinalMem
        have hordinal : ordinal < q := Finset.mem_range.1 hordinalMem
        have hordinal' : ordinal < q + q := hordinal.trans_le (Nat.le_add_right q q)
        simp only [hordinal', ↓reduceDIte]
        exact probEvent_sampledDiagnosticOrdinal_pair_le_eight_sevenths ordinal adversary
          parameter ftsSecret q hordinal hfuel hexpanded hq
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
        _ ≤ (∑ _ordinal ∈ Finset.range q, (8 / 7) * epsilon) +
              (∑ ordinal ∈ Finset.range q, if h : q + ordinal < q + q then
                (Pr[fun outcome => outcome.SuccessfulDoomed ∧
                      outcome.FirstExistingHiddenRootHitAt (q + ordinal) | diagnostic] +
                  Pr[fun outcome => outcome.SuccessfulDoomed ∧
                      outcome.FirstExistingHiddenNonRootHitAt (q + ordinal) | diagnostic])
              else 0) := add_le_add hfirst le_rfl
        _ = ∑ _ordinal ∈ Finset.range q, (8 / 7) * epsilon := by rw [hzero, add_zero]
        _ = ∑ ordinal ∈ Finset.range q, if h : ordinal < q then (8 / 7) * epsilon else 0 := by
          apply Finset.sum_congr rfl
          intro ordinal hordinalMem
          simp [Finset.mem_range.1 hordinalMem]
    _ = (q : ENNReal) * ((8 / 7) * epsilon) := by simp
    _ = _ := by
      simp only [epsilon]
      push_cast
      ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem probEvent_sampledDiagnostic_bad_le_fifteen_sevenths_mul
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
      ((15 / 7 : ENNReal) * q) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  let diagnostic :=
    sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)
  calc
    _ ≤ Pr[fun outcome => outcome.final = none | diagnostic] +
          Pr[ObservedMaterializedDiagnostic.SuccessfulDoomed | diagnostic] :=
      probEvent_diagnosticBad_le_finalNone_add_successfulDoomed diagnostic
    _ ≤ (q : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
          ((8 / 7 : ENNReal) * q) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
      apply add_le_add
      · exact probEvent_sampledDiagnostic_final_none_le_queryBound adversary parameter
          ftsSecret (2 * q) q hexpanded (by omega)
      · exact probEvent_sampledDiagnostic_successfulDoomed_le_eight_sevenths_mul adversary parameter
          ftsSecret q hfuel hexpanded hq
    _ = _ := by
      rw [← add_mul, ← one_add_mul]
      have hcoeff : (1 : ENNReal) + 8 / 7 = 15 / 7 := by
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
        norm_num
      rw [hcoeff]

end SphincsSecurity.Concrete.OtsProbeSimulation.Range125

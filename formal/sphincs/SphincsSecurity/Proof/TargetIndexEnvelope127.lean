import SphincsSecurity.Proof.IndexDifferenceEnvelope
import SphincsSecurity.Proof.IndexDifferenceInitial
import SphincsSecurity.Proof.AdaptiveOccupancy127

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem initialTargetIndexEnvelope_eq_finite (q : Nat) :
    targetIndexEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
      (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) q signatureLimit initialTargetIndexVector 0 14 =
        finiteInitialMixedEnvelope q := by
  rw [targetIndexEnvelope_fourteen_eq_mixed, indexDifferenceTransform_initial]
  simpa only [div_eq_mul_inv] using initialMixedEnvelope_eq_finite q

theorem initialTargetIndexEnvelope_le_127 (q : Nat) (hq : q ≤ 2 ^ 127) :
    targetIndexEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
      (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) q signatureLimit initialTargetIndexVector 0 14 ≤
        (29 : ENNReal) * 2 ^ 43 := by
  rw [initialTargetIndexEnvelope_eq_finite]
  exact finiteInitialMixedEnvelope_le_127 q hq

noncomputable def initialRawIndexRate (q : Nat) : ENNReal :=
  finiteInitialMixedEnvelope q * ((2 ^ 176 : Nat) : ENNReal)⁻¹

theorem initialRawIndexRate_le_127 (q : Nat) (hq : q ≤ 2 ^ 127) :
    initialRawIndexRate q ≤ (29 / 64 : ENNReal) * ((2 ^ 127 : Nat) : ENNReal)⁻¹ := by
  apply (mul_le_mul' (finiteInitialMixedEnvelope_le_127 q hq) le_rfl).trans_eq
  have hl : (29 : ENNReal) * 2 ^ 43 * ((2 ^ 176 : Nat) : ENNReal)⁻¹ ≠ ∞ := by finiteness
  have hr : (29 / 64 : ENNReal) * ((2 ^ 127 : Nat) : ENNReal)⁻¹ ≠ ∞ := by finiteness
  apply (ENNReal.toReal_eq_toReal_iff' hl hr).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div]

theorem cappedRawIndexCacheEnvelope_initial_scaled (key : SecretKey) (q : Nat) (cache : QueryCache HashSpec)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none) :
    cappedRawIndexCacheEnvelope key q (cache, []) ∅ Finset.univ * ((2 ^ 176 : Nat) : ENNReal)⁻¹ = initialRawIndexRate q := by
  have hvalid : TargetShapeValid ∅ Finset.univ := by constructor <;> simp
  have hcard : (Finset.univ : Finset FtsTree).card = 14 := by norm_num [FtsTree, ftsTrees]
  simp only [cappedRawIndexCacheEnvelope, if_pos (show SigningTranscript.Valid [] from Nat.zero_le _), List.length_nil, Nat.sub_zero]
  rw [rawIndexCacheEnvelope_initial key q signatureLimit cache hnone ∅ Finset.univ hvalid,
    Finset.card_empty, hcard, initialTargetIndexEnvelope_eq_finite]
  rfl

theorem expected_adaptive_cappedRawIndex_le_initial {α : Type} (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])] *
      cappedRawIndexCacheEnvelope key q result.2 groups remaining) ≤
      targetIndexEnvelope (Fintype.card Index : ENNReal)⁻¹ (digestReuseWeight q)
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) q signatureLimit initialTargetIndexVector groups.card remaining.card := by
  have hsigned : SigningDigestsCached key.parameter cache key.root [] := by
    intro entry hentry
    simp only [List.not_mem_nil] at hentry
  have hbound := expected_adaptive_cappedRawIndexCacheEnvelope_le key q hq computation (cache, []) hsigned hbudget groups remaining hvalid
  have hinitial : cappedRawIndexCacheEnvelope key q (cache, []) groups remaining = rawIndexCacheEnvelope key q signatureLimit (cache, []) groups remaining := by
    simp only [cappedRawIndexCacheEnvelope, if_pos (show SigningTranscript.Valid [] from Nat.zero_le _), List.length_nil, Nat.sub_zero]
  rw [hinitial] at hbound
  exact hbound.trans_eq (rawIndexCacheEnvelope_initial key q signatureLimit cache hnone groups remaining hvalid)

theorem expected_adaptive_cappedRawIndex_full_le_127 {α : Type} (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q) :
    (∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])] *
      cappedRawIndexCacheEnvelope key q result.2 ∅ Finset.univ) ≤ (29 : ENNReal) * 2 ^ 43 := by
  have hvalid : TargetShapeValid ∅ Finset.univ := by constructor <;> simp
  have h := expected_adaptive_cappedRawIndex_le_initial key q hq computation cache hnone hbudget ∅ Finset.univ hvalid
  have hcard : (Finset.univ : Finset FtsTree).card = 14 := by norm_num [FtsTree, ftsTrees]
  simp only [Finset.card_empty, hcard] at h
  exact h.trans (initialTargetIndexEnvelope_le_127 q hq)

theorem expected_adaptive_cappedRawIndex_full_scaled_le_127 {α : Type} (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none)
    (hbudget : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])),
      QueryCache.enncard result.2.1 ≤ q) :
    (∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run (cache, [])] *
      cappedRawIndexCacheEnvelope key q result.2 ∅ Finset.univ) * ((2 ^ 176 : Nat) : ENNReal)⁻¹ ≤
      (29 / 64 : ENNReal) * ((2 ^ 127 : Nat) : ENNReal)⁻¹ := by
  apply (mul_le_mul_left (expected_adaptive_cappedRawIndex_full_le_127 key q hq computation cache hnone hbudget) _).trans_eq
  have hleft : (29 : ENNReal) * 2 ^ 43 * ((2 ^ 176 : Nat) : ENNReal)⁻¹ ≠ ∞ := by finiteness
  have hright : (29 / 64 : ENNReal) * ((2 ^ 127 : Nat) : ENNReal)⁻¹ ≠ ∞ := by finiteness
  apply (ENNReal.toReal_eq_toReal_iff' hleft hright).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div]


end SphincsSecurity.Concrete

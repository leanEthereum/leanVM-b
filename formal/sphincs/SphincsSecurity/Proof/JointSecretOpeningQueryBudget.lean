import SphincsSecurity.Proof.FtsProbeQueryBudget126
import SphincsSecurity.Proof.Security126Endpoint

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

noncomputable def ftsOpeningQueryReserve (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (input : HashInput) : ℝ≥0∞ :=
  FtsProbeSimulation.ftsHashQueryCharge secretKey.parameter cache input * (4 / 3)

noncomputable def otsOpeningQueryReserve (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (input : HashInput) : ℝ≥0∞ :=
  residualPrimitiveQueryCharge secretKey cache input - ftsOpeningQueryReserve secretKey cache input

def residualOtsOpeningEvent (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState) : Prop :=
  result.1.2.2 = true ∧ ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
    ¬ViewedEncodingCollisionWitness parameter otsSecret ftsSecret result ∧
    cleanOtsOpeningEvent parameter otsSecret ftsSecret result

theorem ftsOpeningQueryReserve_le_residual (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (input : HashInput) :
    ftsOpeningQueryReserve secretKey cache input ≤ residualPrimitiveQueryCharge secretKey cache input :=
  (mul_le_mul' le_rfl (show (4 / 3 : ℝ≥0∞) ≤ 2 by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num)).trans
    (FtsProbeSimulation.ftsHashQueryCharge_mul_two_le_residual secretKey cache input)

theorem openingQueryReserve_add (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) :
    ftsOpeningQueryReserve secretKey cache input + otsOpeningQueryReserve secretKey cache input =
      residualPrimitiveQueryCharge secretKey cache input :=
  add_tsub_cancel_of_le (ftsOpeningQueryReserve_le_residual secretKey cache input)

theorem sampled_openingQueryReserve_add (adversary : Adversary) :
    sampledQueryCharge ftsOpeningQueryReserve adversary + sampledQueryCharge otsOpeningQueryReserve adversary =
      sampledQueryCharge residualPrimitiveQueryCharge adversary := by
  rw [sampledQueryCharge, sampledQueryCharge, sampledQueryCharge, ← ENNReal.tsum_add]
  apply tsum_congr
  intro secrets
  rw [← mul_add, ← expectedQueryCharge_add]
  congr 2
  funext cache input
  exact openingQueryReserve_add _ cache input

theorem sampled_ftsOpeningQueryReserve_eq (adversary : Adversary) :
    sampledQueryCharge ftsOpeningQueryReserve adversary =
      (4 / 3 : ℝ≥0∞) * sampledQueryCharge
        (fun secretKey => FtsProbeSimulation.ftsHashQueryCharge secretKey.parameter) adversary := by
  unfold sampledQueryCharge ftsOpeningQueryReserve
  simp only [expectedQueryCharge_mul]
  simp_rw [← mul_assoc, ENNReal.tsum_mul_right]
  exact mul_comm _ _

theorem probEvent_sampled_residual_le_ots_add_fts (adversary : Adversary) :
    Pr[SampledViewedEvent residualPrimitiveEvent | sampledViewedGame adversary] ≤
      Pr[SampledViewedEvent residualOtsOpeningEvent | sampledViewedGame adversary] +
        Pr[SampledViewedEvent cleanUncoveredEvent | sampledViewedGame adversary] := by
  apply (probEvent_mono (p := SampledViewedEvent residualPrimitiveEvent)
    (q := fun result => SampledViewedEvent residualOtsOpeningEvent result ∨
      SampledViewedEvent cleanUncoveredEvent result) ?_).trans
  · exact probEvent_or_le _ _ _
  · intro result _ hresult
    obtain ⟨hwin, hbad, hencoding, hots | hfts⟩ := hresult
    · exact Or.inl ⟨hwin, hbad, hencoding, hots⟩
    · exact Or.inr hfts

theorem probEvent_sampled_residual_le_queryCharge_of_ots
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 126)
    (hots : Pr[SampledViewedEvent residualOtsOpeningEvent | sampledViewedGame adversary] ≤
      sampledQueryCharge otsOpeningQueryReserve adversary * (Fintype.card Digest : ℝ≥0∞)⁻¹) :
    Pr[SampledViewedEvent residualPrimitiveEvent | sampledViewedGame adversary] ≤
      sampledQueryCharge residualPrimitiveQueryCharge adversary * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  apply (probEvent_sampled_residual_le_ots_add_fts adversary).trans
  have hfts := FtsProbeSimulation.probEvent_sampledViewedGame_cleanUncovered_le_queryCharge126 adversary q hq hqMax
  rw [← sampled_ftsOpeningQueryReserve_eq] at hfts
  apply (add_le_add hots hfts).trans_eq
  rw [← add_mul, add_comm, sampled_openingQueryReserve_add]

/-- The one-time-secret estimate remains an explicit premise. -/
theorem security126_of_sampled_otsOpening_le_queryReserve
    (hots : ∀ (q : Nat), 1 ≤ q → ∀ adversary : Adversary,
      HasHashQueryBound scheme adversary q → q ≤ 2 ^ 126 →
        Pr[SampledViewedEvent residualOtsOpeningEvent | sampledViewedGame adversary] ≤
          sampledQueryCharge otsOpeningQueryReserve adversary * (Fintype.card Digest : ℝ≥0∞)⁻¹) :
    HasClassicalSecurityBits scheme 126 := by
  apply security126_of_sampled_residual_le_queryCharge
  intro q hqPos adversary hq hqMax
  exact probEvent_sampled_residual_le_queryCharge_of_ots adversary q hq hqMax
    (hots q hqPos adversary hq hqMax)

end SphincsSecurity.Concrete
